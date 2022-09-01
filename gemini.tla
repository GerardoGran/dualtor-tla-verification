------------------------------- MODULE gemini -------------------------------
(********************************************************************************)
(* This is a specification for the Gemini Protocol. It describes the behavior   *)
(* of the submodules that make up Gemini's two Top of Rack (TOR) solution for   *)
(* reliability. The purpose of the specification is t find all possible failure *)
(* scenarios in the algorithm by exploring reachable states simulating          *)
(* transitions in the submodules' state machines.                               *)
(********************************************************************************)
EXTENDS FiniteSets

VARIABLES 
    torA,
    torB,
    mux       \* Which ToR the MUX cable itself is pointing to
    (*******************************************************************************)
    (* LinkProber knows wether the TOR it's hosted in should be active or standby  *)
    (* by listening to the active ToR's heartbeat that is sent to both ToR's. It   *)
    (* knows this because this ICMP "heartbeat" has the name or MAC address of the *)
    (* active ToR.                                                                 *)
    (*                                                                             *)
    (* In the specification, this is represented by the heartbeatSender variable   *)
    (* since the standby ToR's heartbeat will be dropped and never listened to.    *)
    (*******************************************************************************)                           

vars == <<torA, torB, mux>>

T == {"torA", "torB"}

\* Link Prober (page 9)
LPStates == {"LPActive", "LPStandby", "LPWait", "LPUnknown"}

\* Link Stat (page 10)
LinkStates == {"LinkUp", "LinkDown"}

\* Mux State (page 12)
MuxStates == {"MuxActive", "MuxStandby", "MuxWait", "MuxUnknown"}

\* MUX_XCVRD_ (page 11)
XCVRDStates == {"switch", "check", "-"}

ToR ==
    [ dead: BOOLEAN, 
      name: T,
      xcvrd: XCVRDStates,
      heartbeat: {"on", "off"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: LPStates,
      linkState: LinkStates,
      muxState: MuxStates ]
ash 
\* "Goal" state for a ToR.
ActiveTor == 
    [ dead: {FALSE},
      name: T, 
      xcvrd: {"-"},
      heartbeat: {"on"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: {"LPActive"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxActive"} ]

TypeOK == 
    /\ torA \in ToR
    /\ torB \in ToR    
    /\ mux \in [ active: T, next: T ]

Init ==
    LET InitialTor(name) == 
        [ dead            |-> FALSE,
          name            |-> name,
          xcvrd           |-> "-",
          heartbeat       |-> "on",
          heartbeatIn     |-> {},
          linkProber      |-> "LPUnknown",
          linkState       |-> "LinkDown",
          muxState        |-> "MuxWait" ]
    IN  /\ mux \in {f \in [ active: T, next: T ]: f.active = f.next}
        /\ torA = InitialTor("torA")
        /\ torB = InitialTor("torB")

-----------------------------------------------------------------------------
\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022
\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/t-gegranados/ERThXZdF5MVFusk2rP-PF0cBGguDR3Rt9yJ3WxxwAt0hpg?e=i8aS4v

\* Merged LinkWait and MuxWait on Powerpoint slide 13 into Wait

MuxStateActive(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MuxActive"
    /\ t.linkState \in {"LinkUp", "LinkDown"}
    /\ \/ /\ t.linkProber = "LPUnknown"
          \* TODO Where and when are heartbeats reactivated?
        \*   /\ t' = [t EXCEPT !.muxState = "Wait", !.xcvrd = "check", !.heartbeat = "off"]
          /\ t' = [t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check"]
       \/ /\ t.linkProber = "LPStandby"
          /\ t' = [t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check"]

MuxStateStandby(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MuxStandby"
    /\ \/ /\ t.linkProber = "LPActive"
          /\ t.linkState \in {"LinkUp", "LinkDown"} \* inconsistent with the table on slide 13. 
          /\ t' = [t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check"]
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t' = [t EXCEPT !.muxState = "MuxWait", !.linkProber = "LPWait", !.xcvrd = "switch"]

MuxStateWait(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MuxWait"
    /\ t.linkProber \in {"LPActive", "LPStandby"}
    /\ t.linkState = "LinkUp"
    \* Timeout of a previous check or switch.
    \* TODO Something inaccurate related to ORCAgent.
    /\ t.xcvrd = "-"
    /\ t' = [t EXCEPT !.muxState = "MuxStandby"]

MuxStateUnknown(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MuxUnknown"
    /\ t.linkProber \in {"LPActive", "LPStandby"}
    /\ t.linkState = "LinkUp"
    /\ t' = [t EXCEPT !.xcvrd = "check"]

XCVRDCheck(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    \* /\ \* Solicited mux notification
    \*    \/ t.muxState = "MuxWait"
    \*    \* Unsolicited mux notification
    \*    \/ t.muxState = "MuxUnknown"
    \* /\ t.xcvrd = "check"
    /\ \/ /\ mux.active = t.name
          /\ t' = [t EXCEPT !.muxState = "MuxActive", !.xcvrd = "-"]
       \/ /\ mux.active # t.name
          /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.xcvrd = "-"]

XCVRDSwitch(t, otherTor) ==
    /\ UNCHANGED <<otherTor>>
    /\ t.muxState = "MuxWait"
    /\ t.linkProber = "LPWait"
    /\ t.xcvrd = "switch"
    /\ t' = [t EXCEPT !.xcvrd = "check"]
    /\ mux' = [ mux EXCEPT !.next = t.name]

-----------------------------------------------------------------------------

MuxXCVRD ==
    /\ UNCHANGED <<torA, torB>>
    /\ mux.active # mux.next \* redundant
    /\ mux' = [ mux EXCEPT !.active = mux.next ]

\* State machine page 10 of the Powerpoint presentation as of 08/25/2022

LinkState(t, otherTor) ==
    /\ ~t.dead
    /\ t.linkState = "LinkDown" \* unnecessary, because going from LinkUp to LinkUp is just (finite) stuttering.  However, this conjunct prevent the debugger from evaluating this action when it is stuttering.
    /\ UNCHANGED <<otherTor, mux>>
    /\ t' = [t EXCEPT !.linkState = "LinkUp"]

-----------------------------------------------------------------------------

\* State machine page 09 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/zhangjing/EclAzBSCq_5KuwgbbpyUlMQB1RS_X9nibOrM1PjT8wM_uw?e=eBtJKl

SendHeartbeat(t) ==
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    /\ t.heartbeat = "on"
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\  mux.active = t.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\ torA' = [ torA EXCEPT !.heartbeatIn = @ \cup {t.name} ]
    /\ torB' = [ torB EXCEPT !.heartbeatIn = @ \cup {t.name} ]
    /\ UNCHANGED <<mux>>

LinkProberWait(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPWait"
    /\ \E heartbeat \in t.heartbeatIn:
        \/ /\ t.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ otherTor.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ "noResponse" = heartbeat
           /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]


LinkProberUnknown(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPUnknown"
    /\ \E heartbeat \in t.heartbeatIn:
        \/ /\ t.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ otherTor.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ "noResponse" = heartbeat
           /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]

LinkProberStandby(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPStandby"
    /\ \E heartbeat \in t.heartbeatIn:
       \/ /\ t.name = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ otherTor.name = heartbeat
          /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ "noResponse" = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown", !.heartbeatIn = @ \ {heartbeat}]

LinkProberActive(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPActive"
    /\ \E heartbeat \in t.heartbeatIn:
       \/ /\ t.name = heartbeat
          /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ otherTor.name = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ "noResponse" = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown", !.heartbeatIn = @ \ {heartbeat}]

-----------------------------------------------------------------------------

System ==
    (****************************************************************************)
    (* Mux handling a switch command.                                           *)
    (****************************************************************************)
    \/ MuxXCVRD
    (****************************************************************************)
    (* XCVRD and LinkMgrd                                                       *)
    (****************************************************************************)
    \/ XCVRDCheck(torA, torB)
    \/ XCVRDCheck(torB, torA)
    \/ XCVRDSwitch(torA, torB)
    \/ XCVRDSwitch(torB, torA)
    \/ MuxStateStandby(torA, torB)
    \/ MuxStateStandby(torB, torA)
    \/ MuxStateActive(torA, torB)
    \/ MuxStateActive(torB, torA)
    \/ MuxStateWait(torA, torB)
    \/ MuxStateWait(torB, torA)
    (****************************************************************************)
    (* ToR periodically send heartbeats via the mux to the server.              *)
    (****************************************************************************)
    \/ SendHeartbeat(torA)
    \/ SendHeartbeat(torB)
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    \/ LinkProberStandby(torA, torB)
    \/ LinkProberStandby(torB, torA)
    \/ LinkProberActive(torA, torB)
    \/ LinkProberActive(torB, torA)
    \/ LinkProberUnknown(torA, torB)
    \/ LinkProberUnknown(torB, torA)
    \/ LinkProberWait(torA, torB)
    \/ LinkProberWait(torB, torA)
    (****************************************************************************)
    (* Notification from the kernel that a physical link (L1) came up.          *)
    (****************************************************************************)
    \/ LinkState(torA, torB)
    \/ LinkState(torB, torA)

-----------------------------------------------------------------------------

FailHeartbeat ==
    (*****************************************************************************)
    (* Sender fails to send heartbeat to ToR's making them go into unknown state *)
    (*****************************************************************************)
    /\ \/ /\ \E heartbeat \in SUBSET torA.heartbeatIn:
                /\ torA' = [ torA EXCEPT !.heartbeatIn = heartbeat ]
                /\ UNCHANGED torB
       \/ /\ \E heartbeat \in SUBSET torB.heartbeatIn:
                /\ torB' = [ torB EXCEPT !.heartbeatIn = heartbeat ]
                /\ UNCHANGED torA
    /\ UNCHANGED mux

FailMux ==
    (******************************************************************)
    (* Failure Action for inconsistent MUX States with MuxCable State *)
    (******************************************************************)
    /\  mux' \in [ active: T, next: T ]
    /\  UNCHANGED <<torA, torB>>

FailTor(t, otherTor) ==
    /\ t' = [t EXCEPT !.dead = TRUE]
    /\ UNCHANGED <<otherTor, mux>>

FailXCVRD(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    \* According to Vaibhav Dahiya, the mux returns "Unknown" in case of failure, 
    \* which, subsequently, causes the ToR to go to "Standby".
    /\ t' = [t EXCEPT !.xcvrd = "-"]

FailLinkState(t, otherTor) ==
    /\ ~t.dead
    /\ UNCHANGED <<otherTor, mux>>
    /\ t' = [t EXCEPT !.linkState = "LinkDown"]

Environment ==
    \/ FailMux
    \/ FailHeartbeat
    \/ FailTor(torA, torB)
    \/ FailTor(torB, torA)
    \/ FailXCVRD(torA, torB)
    \/ FailXCVRD(torB, torA)
    \/ FailLinkState(torA, torB)
    \/ FailLinkState(torB, torA)

-----------------------------------------------------------------------------

Next == 
    \/ Environment
    \/ System

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

AtMostOneActive ==
    []~(torA \in ActiveTor /\ torB \in ActiveTor)

RepeatedlyOneActive ==
    []<>(\E t \in {torA, torB} : ~t.dead => (torA \in ActiveTor \/ torB \in ActiveTor))

THEOREM Spec => AtMostOneActive /\ RepeatedlyOneActive

-----------------------------------------------------------------------------

Alias ==
    [
        torA |-> torA, torB |-> torB, mux |-> mux,
        active |-> { t.name : t \in { t \in {torA, torB} : t \in ActiveTor} }
    ]
=============================================================================