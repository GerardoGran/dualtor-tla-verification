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
    mux,       \* Which ToR the MUX cable itself is pointing to
    \* TODO check real component name
    heartbeatSender
    (*******************************************************************************)
    (* LinkProber knows wether the TOR it's hosted in should be active or standby  *)
    (* by listening to the active ToR's heartbeat that is sent to both ToR's. It   *)
    (* knows this because this ICMP "heartbeat" has the name or MAC address of the *)
    (* active ToR.                                                                 *)
    (*                                                                             *)
    (* In the specification, this is represented by the heartbeatSender variable   *)
    (* since the standby ToR's heartbeat will be dropped and never listened to.    *)
    (*******************************************************************************)                           

vars == <<torA, torB, mux, heartbeatSender>>

T == {"torA", "torB"}

\* Link Manager (page 14)
LMStates == {"LMChecking", "LMActive", "LMStandby"} \union {"LMFailure"}

\* Link Prober (page 9)
LPStates == {"LPActive", "LPStandby", "LPUnknown"}

\* Link Stat (page 10)
LinkStates == {"LinkUp", "LinkDown"}

\* Mux State (page 12)
MuxStates == {"MSActive", "MSStandby", "MSMuxWait", "MSLinkWait"} \union {"MSMuxFailure"}

\* MUX_XCVRD_ (page 11)
XCVRDStates == {"XCVRDActive", "XCVRDStandby", "XCVRDUnknown"} \*TODO s/Fail/Unknown ?

ToR ==
    [ dead: BOOLEAN, 
      name: T,
      xcvrd: XCVRDStates,
      heartbeat: {"on", "off"},
      linkManager: LMStates, 
      linkProber: LPStates,
      linkState: LinkStates,
      muxState: MuxStates ]

\* "Goal" state for a ToR.
ActiveTor == 
    [ dead: {FALSE},
      name: T, 
      xcvrd: {"XCVRDActive"},
      heartbeat: {"on"},
      linkManager: {"LMActive"},
      linkProber: {"LPActive"}, 
      linkState: {"LinkUp"},
      muxState: {"MSActive"} ]

TypeOK == 
    /\ torA \in ToR
    /\ torB \in ToR    
    /\ mux \in T
    /\ heartbeatSender \in (T \union {"noResponse"})

Init ==
    LET InitialTor(name) == 
        [ dead            |-> FALSE,
          name            |-> name,
          xcvrd           |-> IF name = mux THEN "XCVRDActive" ELSE "XCVRDStandby",
          heartbeat       |-> "on",
          linkManager     |-> "LMChecking",
          linkProber      |-> "LPUnknown",
          linkState       |-> "LinkDown",
          muxState        |-> "MSMuxWait" ]
    IN  /\ mux \in T
        /\ heartbeatSender = "noResponse"
        /\ torA = InitialTor("torA")
        /\ torB = InitialTor("torB")

\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022

XCVRD(t, otherTor) ==
    /\ UNCHANGED <<otherTor, heartbeatSender, mux>>
    /\ ~t.dead                                          \* TODO Model dead XCVDR daemon separately?
    \* /\ t.muxState = "MSLinkWait"
    /\ \/ /\ mux = t.name
          /\ t' = [t EXCEPT !.xcvrd = "XCVRDActive"]
       \/ /\ mux # t.name
          /\ t' = [t EXCEPT !.xcvrd = "XCVRDStandby"]

\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022

MuxStateLinkWait(t, otherTor) ==
    /\ t.muxState = "MSLinkWait"
    /\ \/ /\ t.linkProber \in {"LPActive", "LPStandby"}
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MSMuxWait", !.heartbeat = "on"]
       \/ /\ t.xcvrd = "XCVRDUnknown"
          /\ t' = [t EXCEPT !.muxState = "MSMuxFailure"]

MuxStateMuxWait(t, otherTor) ==
    /\ t.muxState = "MSMuxWait"
    \* All columns for row "MuxWait" are no-op.
    /\ \/ /\ t.xcvrd = "XCVRDActive"
          /\ t' = [t EXCEPT !.muxState = "MSActive"]
       \/ /\ t.xcvrd = "XCVRDStandby"
          /\ t' = [t EXCEPT !.muxState = "MSStandby"]
       \/ /\ t.xcvrd = "XCVRDUnknown"
          /\ t' = [t EXCEPT !.muxState = "MSMuxFailure"]

MuxStateActive(t, otherTor) ==
    /\ t.muxState = "MSActive"
    /\ \/ /\ t.linkProber = "LPStandby"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MSMuxWait"]
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t.heartbeat = "off"
          /\ t' = [t EXCEPT !.muxState = "MSLinkWait"]    \* TODO page 13 says these two actions suspends sending heartbeats, but heartbeats are nowhere reactivated.

MuxStateStandby(t, otherTor) ==
    /\ t.muxState = "MSStandby"
    /\ \/ /\ t.linkProber = "LPActive"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MSMuxWait"]
       \/ /\ t.linkProber = "LPUnknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t' = [t EXCEPT !.muxState = "MSLinkWait"]

MuxState(t, otherTor) ==
    /\ UNCHANGED <<otherTor, heartbeatSender, mux>>
    /\ ~t.dead
    /\ \/ MuxStateStandby(t, otherTor)
       \/ MuxStateActive(t, otherTor)
       \/ MuxStateMuxWait(t, otherTor)
       \/ MuxStateLinkWait(t, otherTor)    

\* State machine page 10 of the Powerpoint presentation as of 08/25/2022

LinkState(t, otherTor) ==
    /\ ~t.dead
    /\ UNCHANGED <<otherTor, mux, heartbeatSender>>
    /\ t' = [t EXCEPT !.linkState = "LinkUp"]

\* State machine page 14 of the Powerpoint presentation as of 08/25/2022

LinkManagerChecking(t, otherTor) ==
    /\ t.linkManager = "LMChecking"
    /\ \/ /\ t.muxState = "MSActive"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber = "LPActive"
          /\ t' = [t EXCEPT !.linkManager = "LMActive"]
       \/ /\ t.muxState = "MSStandby"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber = "LPStandby"
          /\ t' = [t EXCEPT !.linkManager = "LMStandby"]
       \* TODO MSMuxFailure and Failure are no enums above!
       \/ /\ t.muxState = "MSMuxFailure"
          /\ t' = [t EXCEPT !.linkManager = "Failure"]

LinkManagerActive(t, otherTor) ==
    /\ t.linkManager = "LMActive"
    /\ \/ /\ t.muxState = "MSActive"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber \in {"LPStandby", "LPUnknown"}
          /\ t' = [t EXCEPT !.linkManager = "LMChecking"]
       \/ /\ t.muxState = "MSActive"
          /\ t.linkState = "LinkDown"
          /\ t.linkProber = "LPUnknown"
          /\ t' = [t EXCEPT !.linkManager = "LMChecking"]

LinkManagerStandby(t, otherTor) ==
    /\ t.linkManager = "LMStandby"
    /\ t.muxState = "MSStandby"
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "LPUnknown" \* ??? Go to linkManager Active if linkProber is "unknown"?
    /\ t' = [t EXCEPT !.linkManager = "LMActive"]

LinkManagerPage14(t, otherTor) ==
    /\ ~t.dead
    /\ UNCHANGED <<otherTor, mux, heartbeatSender>>
    /\ \/ LinkManagerChecking(t, otherTor)
       \/ LinkManagerActive(t, otherTor)
       \/ LinkManagerStandby(t, otherTor)

-----------------------------------------------------------------------------

\* State machine page 09 of the Powerpoint presentation as of 08/25/2022

SendHeartbeat(t) ==
    /\ ~t.dead
    /\ t.heartbeat = "on"
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\  mux = t.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\  heartbeatSender' = t.name
    /\  UNCHANGED <<torA, torB, mux>>

LinkProberUnknown(t, otherTor) ==
    /\ t.linkProber = "LPUnknown"
    /\ \/ /\ t.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPActive"]
       \/ /\ otherTor.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPStandby"]
       \/ /\ "noResponse" = heartbeatSender
          /\ UNCHANGED t

LinkProberStandby(t, otherTor) ==
    /\ t.linkProber = "LPStandby"
    /\ \/ /\ t.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPActive"]
       \/ /\ otherTor.name = heartbeatSender
          /\ UNCHANGED t
       \/ /\ "noResponse" = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown"]

LinkProberActive(t, otherTor) ==
    /\ t.linkProber = "LPActive"
    /\ \/ /\ t.name = heartbeatSender
          /\ UNCHANGED t
       \/ /\ otherTor.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPStandby"]
       \/ /\ "noResponse" = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "LPUnknown"]

ReceiveHeartbeat(t, otherTor) ==
    /\ ~t.dead
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    /\  UNCHANGED <<otherTor, heartbeatSender, mux>>
    /\  \/  LinkProberUnknown(t, otherTor)
        \/  LinkProberStandby(t, otherTor)
        \/  LinkProberActive(t, otherTor)

-----------------------------------------------------------------------------

System ==
    \/ MuxState(torA, torB)
    \/ MuxState(torB, torA)
    \/ SendHeartbeat(torA)
    \/ SendHeartbeat(torB)
    \/ ReceiveHeartbeat(torA, torB)
    \/ ReceiveHeartbeat(torB, torA)
    \/ LinkManagerPage14(torA, torB)
    \/ LinkManagerPage14(torB, torA)
    \/ LinkState(torA, torB)
    \/ LinkState(torB, torA)
    \/ XCVRD(torA, torB)
    \/ XCVRD(torB, torA)    

-----------------------------------------------------------------------------

FailHeartbeat ==
    (*****************************************************************************)
    (* Sender fails to send heartbeat to ToR's making them go into unknown state *)
    (*****************************************************************************)
    /\  heartbeatSender' = "noResponse"
    /\  UNCHANGED <<torA, torB, mux>>

FailMux ==
    (******************************************************************)
    (* Failure Action for inconsistent MUX States with MuxCable State *)
    (******************************************************************)
    /\  mux' \in T
    /\  UNCHANGED <<torA, torB, heartbeatSender>>

FailTor(t, otherTor) ==
    /\ t' = [t EXCEPT !.dead = TRUE]
    /\ UNCHANGED <<otherTor, heartbeatSender, mux>>

FailXCVRD(t, otherTor) ==
    /\ UNCHANGED <<otherTor, heartbeatSender, mux>>
    \* According to Vaibhav Dahiya, the mux returns "Unknown" in case of failure, 
    \* which, subsequently, causes the ToR to go to "Standby".
    \* /\ t' = [t EXCEPT !.xcvrd = "XCVRDUnknown"]
    /\ t' = [t EXCEPT !.xcvrd = "XCVRDStandby"]

FailLinkState(t, otherTor) ==
    /\ ~t.dead
    /\ UNCHANGED <<otherTor, mux, heartbeatSender>>
    /\ t' = [t EXCEPT !.linkState = "LinkDown"]

\* RebootTor(t, otherTor) ==
\*     /\ t.dead = TRUE
\*     /\ UNCHANGED <<otherTor, heartbeatSender, mux>>
\*     /\ t' = [ dead          |-> FALSE,
\*             name            |-> t.name,
\*             xcvrd           |-> IF t.name = mux THEN "XCVRDActive" ELSE "XCVRDStandby",
\*             linkManager     |-> "LMChecking",
\*             linkProber      |-> "LPUnknown",
\*             linkState       |-> "LinkDown",
\*             muxState        |-> "MSMuxWait" ]
            
Environment ==
    \/ FailMux
    \/ FailHeartbeat
    \/ FailTor(torA, torB)
    \/ FailTor(torB, torA)
    \* \/ RebootTor(torA, torB)
    \* \/ RebootTor(torB, torA)
    \/ FailXCVRD(torA, torB)
    \/ FailXCVRD(torB, torA)
    \/ FailLinkState(torA, torB)
    \/ FailLinkState(torB, torA)

-----------------------------------------------------------------------------

Next == 
    Environment \/ System

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
        torA |-> torA, torB |-> torB, mux |-> mux,  heartbeatSender |-> heartbeatSender,
        active |-> { t \in {torA, torB} : t \in ActiveTor}
    ]
=============================================================================