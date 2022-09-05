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
          xcvrd           |-> "check",
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

(**************************************************************************************************)
(* MuxState State Transitions depend on LinkManager's decisions and XCVRD responses when checking *)
(* or switching the MuxCable's direction                                                          *)
(**************************************************************************************************)

TRIGGER_LINKMANAGER_CHECK(t) ==
    (**************************************************)
    (* Sends check request to MUX via XCVRD.          *)
    (* Transitions muxState to MuxWait.               *)
    (* Defined to use in subsequent MuxState actions. *)
    (**************************************************)
    t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check" ]


TRIGGER_LINKMANAGER_SWITCH(t, target) ==
    (************************************************************)
    (* Sends write request to MUX via XCVRD.                    *)
    (* Transitions muxState to MuxWait and linkProber to LPWait *)
    (* target refers to ToR the Mux should point to.            *)
    (* Defined to use in subsequent MuxState actions.           *)
    (************************************************************)
    /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "switch", !.linkProber = "LPWait" ]
    /\  mux' = [ mux EXCEPT !.next = target.name]

EXEC_LINKMANAGER_CHECK(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ t.xcvrd = "check"
    /\  \/  /\ mux.active = t.name
            /\ t' = [t EXCEPT !.muxState = "MuxActive", !.heartbeat = "on", !.xcvrd = "-"]
        \/  /\ mux.active # t.name
            /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.heartbeat = "on", !.xcvrd = "-"]
        \/  /\ t' = [t EXCEPT !.muxState = "MuxUnknown", !.heartbeat = "on", !.xcvrd = "-"]
        \* \/  /\ t.muxState = "MuxWait"
        \*     /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.xcvrd = "-"]  MUX_XCVRD_FAIL
        

EXEC_LINKMANAGER_SWITCH(t, otherTor) ==
    \* Writing Switch direction
    /\ UNCHANGED otherTor
    /\ t.xcvrd = "switch"
    /\ t.muxState = "MuxWait"
    /\ t.linkProber = "LPWait"
    /\ mux' = [ mux EXCEPT !.active = mux.next]
    /\  \/  /\ mux.next = t.name
            /\ t' = [t EXCEPT !.muxState = "MuxActive", !.heartbeat = "on", !.xcvrd = "-"]
        \/  /\ mux.next # t.name
            /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.heartbeat = "on", !.xcvrd = "-"]
        \/  /\ t' = [t EXCEPT !.muxState = "MuxUnknown", !.heartbeat = "on", !.xcvrd = "-"]
        \* \/  /\ t.muxState = "MuxWait"
        \*     /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.xcvrd = "-"]  MUX_XCVRD_FAIL

----------------------------

MuxStateActive(t, otherTor) ==
    /\ ~t.dead
    /\  t.muxState = "MuxActive"
    /\  \/  /\ t.linkState = "LinkUp"
            \* LinkUp MuxStateActive Row
            /\  \/  /\ t.linkProber \in {"LPStandby", "LPUnknown"}
                    /\ TRIGGER_LINKMANAGER_CHECK(t)
                \/  /\ t.linkProber = "LPWait"
                    \* Check and suspend heartbeat
                    /\ t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check", !.heartbeat = "off" ]
            /\ UNCHANGED <<mux, otherTor>>
        \/  /\ t.linkState = "LinkDown"
            \* Switch to Standby
            /\ TRIGGER_LINKMANAGER_SWITCH(t, otherTor)
            /\ UNCHANGED otherTor

MuxStateStandby(t, otherTor) ==
    /\ ~t.dead
    /\  t.muxState = "MuxStandby"
    /\  \/  /\ t.linkState = "LinkUp"
        \* LinkUp MuxStateStandby Row
            /\  \/  /\ t.linkProber \in {"LPActive", "LPWait"}
                    /\ TRIGGER_LINKMANAGER_CHECK(t)
                    /\ UNCHANGED <<mux, otherTor>>
                \/  /\ t.linkProber = "LPUnknown"
                    \* Switch to Active
                    /\ TRIGGER_LINKMANAGER_SWITCH(t, t)
                    /\ UNCHANGED otherTor
        \/  /\ t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\ t.linkProber \in {"LPUnknown, LPWait"}
            /\ TRIGGER_LINKMANAGER_CHECK(t)
            /\ UNCHANGED <<mux, otherTor>>

MuxStateUnknown(t, otherTor) ==
    /\ ~t.dead
    /\  t.muxState = "MuxUnknown"
    /\  \/  /\ t.linkState = "LinkUp"
            \* LinkUp MuxStateStandby Row
            /\ TRIGGER_LINKMANAGER_CHECK(t)
        \/  /\ t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\ t.linkProber \in {"LPUnknown, LPWait"}
            /\ TRIGGER_LINKMANAGER_CHECK(t)
    /\  UNCHANGED <<mux, otherTor>>

MuxStateWait(t, otherTor) ==
    \*TODO Specify receiving XCVRD Response
    /\ ~t.dead
    /\ t.muxState = "MuxWait"
    /\  \/  /\ EXEC_LINKMANAGER_CHECK(t, otherTor)
        \/  /\ EXEC_LINKMANAGER_SWITCH(t, otherTor)

-----------------------------------------------------------------------------

\* MuxXCVRD ==
\*     \* 
\*     /\ UNCHANGED <<torA, torB>>
\*     /\ mux' = [ mux EXCEPT !.active = mux.next ]

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
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPActive"
    /\ \E heartbeat \in t.heartbeatIn:
       \/ /\ t.name = heartbeat
          /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ otherTor.name = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ "noResponse" = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown", !.heartbeatIn = @ \ {heartbeat}]

LinkProber(t, otherTor) ==
    /\ ~t.dead
    /\  \/ LinkProberActive(t, otherTor)
        \/ LinkProberStandby(t, otherTor)
        \/ LinkProberWait(t, otherTor)
        \/ LinkProberUnknown(t, otherTor)

-----------------------------------------------------------------------------

System ==
    (****************************************************************************)
    (* Mux handling a switch or check command.                                           *)
    (****************************************************************************)
    \/ EXEC_LINKMANAGER_SWITCH(torA, torB)
    \/ EXEC_LINKMANAGER_SWITCH(torB, torA)
    \/ EXEC_LINKMANAGER_CHECK(torA, torB)
    \/ EXEC_LINKMANAGER_CHECK(torB, torA)
    (****************************************************************************)
    (* XCVRD and LinkMgrd                                                       *)
    (****************************************************************************)
    \/ MuxStateActive(torA, torB)
    \/ MuxStateActive(torB, torA)
    \/ MuxStateStandby(torA, torB)
    \/ MuxStateStandby(torB, torA)
    \/ MuxStateWait(torA, torB)
    \/ MuxStateWait(torB, torA)
    \/ MuxStateUnknown(torA, torB)
    \/ MuxStateUnknown(torB, torA)
    (****************************************************************************)
    (* ToR periodically send heartbeats via the mux to the server.              *)
    (****************************************************************************)
    \/ SendHeartbeat(torA)
    \/ SendHeartbeat(torB)
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    \/ LinkProber(torA, torB)
    \/ LinkProber(torB, torA)
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
    \* \/ Environment
    \/ System

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

\* AtMostOneActive ==
\*     []~(torA \in ActiveTor /\ torB \in ActiveTor)

RepeatedlyOneActive ==
    []<>(\E t \in {torA, torB} : ~t.dead => (torA \in ActiveTor \/ torB \in ActiveTor))

THEOREM Spec => 
    \*/\ AtMostOneActive
    /\ RepeatedlyOneActive

-----------------------------------------------------------------------------

Alias ==
    [
        torA |-> torA, torB |-> torB, mux |-> mux,
        active |-> { t.name : t \in { t \in {torA, torB} : t \in ActiveTor} }
    ]
=============================================================================