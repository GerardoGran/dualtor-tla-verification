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
LPStates == {"LPActive", "LPStandby", "LPUnknown"}

\* Link Stat (page 10)
LinkStates == {"LinkUp", "LinkDown"}

\* Mux State (page 12)
MuxStates == {"MXActive", "MXStandby", "MXMuxWait", "MXLinkWait"} \union {"MXMuxFailure"}

\* MUX_XCVRD_ (page 11)
XCVRDStates == {"XCVRDActive", "XCVRDStandby", "XCVRDFail"} \*TODO s/XCVRDFail/Unknown ?

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
      xcvrd: {"XCVRDActive"},
      heartbeat: {"on"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: {"LPActive"}, 
      linkState: {"LinkUp"},
      muxState: {"MXActive"} ]

TypeOK == 
    /\ torA \in ToR
    /\ torB \in ToR    
    /\ mux \in [ active: T, next: T ]

Init ==
    LET InitialTor(name) == 
        [ dead            |-> FALSE,
          name            |-> name,
          xcvrd           |-> IF name = mux.active THEN "XCVRDActive" ELSE "XCVRDStandby",
          heartbeat       |-> "on",
          heartbeatIn     |-> {},
          linkProber      |-> "LPUnknown",
          linkState       |-> "LinkDown",
          muxState        |-> "MXMuxWait" ]
    IN  /\ mux \in {f \in [ active: T, next: T ]: f.active = f.next}
        /\ torA = InitialTor("torA")
        /\ torB = InitialTor("torB")

\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022

XCVRD(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ ~t.dead                                          \* TODO Model dead XCVDR daemon separately?
    /\ mux.active = mux.next
    \* /\ t.muxState = "MXLinkWait"
    /\ \/ /\ mux.active = t.name
          /\ t' = [t EXCEPT !.xcvrd = "XCVRDActive"]
       \/ /\ mux.active # t.name
          /\ t' = [t EXCEPT !.xcvrd = "XCVRDStandby"]

\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022

MuxStateLinkWait(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MXLinkWait"
    /\ \/ /\ t.linkProber \in {"LPActive", "LPStandby"}
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MXMuxWait", !.heartbeat = "on"]
       \/ /\ t.xcvrd = "XCVRDFail"
          /\ t' = [t EXCEPT !.muxState = "MXMuxFailure"]

MuxStateMuxWait(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MXMuxWait"
    \* All columns for row "MuxWait" are no-op.
    /\ \/ /\ t.xcvrd = "XCVRDActive"
          /\ t' = [t EXCEPT !.muxState = "MXActive"]
       \/ /\ t.xcvrd = "XCVRDStandby"
          /\ t' = [t EXCEPT !.muxState = "MXStandby"]
       \/ /\ t.xcvrd = "XCVRDFail"
          /\ t' = [t EXCEPT !.muxState = "MXMuxFailure"]

MuxStateActive(t, otherTor) ==
    /\ UNCHANGED <<mux, otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MXActive"
    /\ \/ /\ t.linkProber = "LPStandby"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MXMuxWait"]
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t.heartbeat = "off"
          /\ t' = [t EXCEPT !.muxState = "MXLinkWait"]    \* TODO page 13 says these two actions suspends sending heartbeats, but heartbeats are nowhere reactivated.

MuxStateStandby(t, otherTor) ==
    /\ UNCHANGED <<otherTor>>
    /\ ~t.dead
    /\ t.muxState = "MXStandby"
    /\ \/ /\ t.linkProber = "LPActive"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MXMuxWait"]
          /\ UNCHANGED mux
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkDown"}
          /\ t' = [t EXCEPT !.muxState = "MXLinkWait"]
          /\ UNCHANGED mux
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkUp"}
          /\ t' = [t EXCEPT !.muxState = "MXLinkWait"]
          /\ \/ /\ mux.active = mux.next
                /\ mux' = [ mux EXCEPT !.next = t.name ]
             \/ UNCHANGED mux

\* State machine page 10 of the Powerpoint presentation as of 08/25/2022

LinkState(t, otherTor) ==
    /\ ~t.dead
    /\ t.linkState = "LinkDown" \* unnecessary, because going from LinkUp to LinkUp is just (finite) stuttering.  However, this conjunct prevent the debugger from evaluating this action when it is stuttering.
    /\ UNCHANGED <<otherTor, mux>>
    /\ t' = [t EXCEPT !.linkState = "LinkUp"]

-----------------------------------------------------------------------------

\* State machine page 09 of the Powerpoint presentation as of 08/25/2022

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

LinkProberUnknown(t, otherTor) ==
    /\ t.linkProber = "LPUnknown"
    /\ \E heartbeat \in t.heartbeatIn:
        \/ /\ t.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ otherTor.name = heartbeat
           /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
        \/ /\ "noResponse" = heartbeat
           /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]

LinkProberStandby(t, otherTor) ==
    /\ t.linkProber = "LPStandby"
    /\ \E heartbeat \in t.heartbeatIn:
       \/ /\ t.name = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ otherTor.name = heartbeat
          /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ "noResponse" = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown", !.heartbeatIn = @ \ {heartbeat}]

LinkProberActive(t, otherTor) ==
    /\ t.linkProber = "LPActive"
    /\ \E heartbeat \in t.heartbeatIn:
       \/ /\ t.name = heartbeat
          /\ t' = [t EXCEPT !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ otherTor.name = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]
       \/ /\ "noResponse" = heartbeat
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown", !.heartbeatIn = @ \ {heartbeat}]

ReceiveHeartbeat(t, otherTor) ==
    /\ ~t.dead
    /\ t.linkState = "LinkUp"
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    /\  UNCHANGED <<otherTor, mux>>
    /\  \/  LinkProberUnknown(t, otherTor)
        \/  LinkProberStandby(t, otherTor)
        \/  LinkProberActive(t, otherTor)

MuxXCVRD ==
    /\ UNCHANGED <<torA, torB>>
    /\ mux.active # mux.next \* redundant
    /\ mux' = [ mux EXCEPT !.active = mux.next ]

-----------------------------------------------------------------------------

System ==
    \/ MuxXCVRD
    \/ MuxStateStandby(torA, torB)
    \/ MuxStateActive(torA, torB)
    \/ MuxStateMuxWait(torA, torB)
    \/ MuxStateLinkWait(torA, torB)    
    \/ MuxStateStandby(torB, torA)
    \/ MuxStateActive(torB, torA)
    \/ MuxStateMuxWait(torB, torA)
    \/ MuxStateLinkWait(torB, torA)    
    \/ SendHeartbeat(torA)
    \/ SendHeartbeat(torB)
    \/ ReceiveHeartbeat(torA, torB)
    \/ ReceiveHeartbeat(torB, torA)
    \/ LinkState(torA, torB)
    \/ LinkState(torB, torA)
    \/ XCVRD(torA, torB)
    \/ XCVRD(torB, torA)    

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
    \* /\ t' = [t EXCEPT !.xcvrd = "XCVRDFail"]
    /\ t' = [t EXCEPT !.xcvrd = "XCVRDStandby"]

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