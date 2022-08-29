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
LMStates == {"Checking", "Active", "Standby"} \union {"Failure"}

\* Link Prober (page 9)
LPStates == {"Active", "Standby", "Unknown"}

\* Link Stat (page 10)
LinkStates == {"LinkUp", "LinkDown"}

\* Mux State (page 12)
MuxStates == {"Active", "Standby", "MuxWait", "LinkWait"} \union {"MuxFailure"}

ToR ==
    [ dead: BOOLEAN, 
      name: T,
      linkManager: LMStates, 
      linkProber: LPStates,
      linkState: LinkStates,
      muxState: MuxStates ]

\* "Goal" state for a ToR.
ActiveTor == 
    [ dead: {FALSE},
      name: T, 
      linkManager: {"Active"},
      linkProber: {"Active"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxActive"} ]

TypeOK == 
    /\ torA \in ToR
    /\ torB \in ToR    
    /\ mux \in T
    /\ heartbeatSender \in (T \union {"noResponse"})

Init ==
    LET InitialTor(name) == 
        [ dead            |-> FALSE,
          name            |-> name,
          linkManager     |-> "Checking",
          linkProber      |-> "Unknown",
          linkState       |-> "LinkDown",
          muxState        |-> "MuxWait" ]
    IN  /\ torA = InitialTor("torA")
        /\ torB = InitialTor("torB")
        /\ mux \in T
        /\ heartbeatSender = "noResponse"

\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022

XCVRD(t, otherTor) ==
    /\ UNCHANGED <<otherTor, heartbeatSender, mux>>
    /\ ~t.dead                                          \* TODO Model dead XCVDR daemon separately?
    \* /\ t.muxState = "LinkWait"
    /\ \/ /\ mux = t.name
          /\ t' = [t EXCEPT !.muxState = "Active"]
       \/ /\ mux # t.name
          /\ t' = [t EXCEPT !.muxState = "Standby"]
       \/ /\ t' = [t EXCEPT !.muxState = "MuxFailure"]

\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022

MuxStateLinkWait(t, otherTor) ==
    /\ t.muxState = "LinkWait"
    /\ \/ /\ t.muxState = "Active"                      \* TODO This sub-action is already covered by XCVRD!2!1
          /\ t' = [t EXCEPT !.muxState = "Active"]
       \/ /\ t.linkProber \in {"Active", "Standby"}
          /\ t' = [t EXCEPT !.muxState = "Standby"]     \* TODO This sub-action is already covered by XCVRD!2!2
       \/ /\ TRUE \* MUX_XCVRD_FAIL                     \* TODO This sub-action is already covered by XCVRD!2!3
          /\ t' = [t EXCEPT !.muxState = "MuxFailure"]

MuxStateMuxWait(t, otherTor) ==
    /\ t.muxState = "MuxWait"
    \* All columns for row "MuxWait" are no-op.         \* TODO This suggests that XCVRD and this action are the one and the same?
    /\ UNCHANGED t

MuxStateActive(t, otherTor) ==
    /\ t.muxState = "Active"
    /\ \/ /\ t.linkProber = "Standby"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MuxWait"]
       \/ /\ t.linkProber = "Unknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t' = [t EXCEPT !.muxState = "LinkWait"]    \* TODO page 13 says these two actions suspends sending heartbeats, but heartbeats are nowhere reactivated.

MuxStateStandby(t, otherTor) ==
    /\ t.muxState = "Standby"
    /\ \/ /\ t.linkProber = "Active"
          /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.muxState = "MuxWait"]
       \/ /\ t.linkProber = "Unknown"
          /\ t.linkState \in {"LinkUp", "LinkDown"}
          /\ t' = [t EXCEPT !.muxState = "LinkWait"]

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
    \* Non-deterministically flip the link state (reacting to a kernel message)
    /\ \/ /\ t.linkState = "LinkDown"
          /\ t' = [t EXCEPT !.linkState = "LinkUp"]
       \/ /\ t.linkState = "LinkUp"
          /\ t' = [t EXCEPT !.linkState = "LinkDown"]

\* State machine page 14 of the Powerpoint presentation as of 08/25/2022

LinkManagerChecking(t, otherTor) ==
    /\ t.linkManager = "Checking"
    /\ \/ /\ t.muxState = "Active"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber = "Active"
          /\ t' = [t EXCEPT !.linkManager = "Active"]
       \/ /\ t.muxState = "Standby"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber = "Standby"
          /\ t' = [t EXCEPT !.linkManager = "Standby"]
       \* TODO MuxFailure and Failure are no enums above!
       \/ /\ t.muxState = "MuxFailure"
          /\ t' = [t EXCEPT !.linkManager = "Failure"]

LinkManagerActive(t, otherTor) ==
    /\ t.linkManager = "Active"
    /\ \/ /\ t.muxState = "Active"
          /\ t.linkState = "LinkUp"
          /\ t.linkProber \in {"Standby", "Unknown"}
          /\ t' = [t EXCEPT !.linkManager = "Checking"]
       \/ /\ t.muxState = "Active"
          /\ t.linkState = "LinkDown"
          /\ t.linkProber = "Unknown"
          /\ t' = [t EXCEPT !.linkManager = "Checking"]

LinkManagerStandby(t, otherTor) ==
    /\ t.linkManager = "Standby"
    /\ t.muxState = "Standby"
    /\ t.linkState = "LinkUp"
    /\ t.linkProber = "Unknown" \* ??? Go to linkManager Active if linkProber is "unknown"?
    /\ t' = [t EXCEPT !.linkManager = "Active"]

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
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\  mux = t.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\  heartbeatSender' = t.name
    /\  UNCHANGED <<torA, torB, mux>>

LinkProberUnknown(t, otherTor) ==
    /\ t.linkProber = "Unknown"
    /\ \/ /\ t.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Active"]
       \/ /\ otherTor.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Standby"]
       \/ /\ "noResponse" = heartbeatSender
          /\ UNCHANGED t

LinkProberStandby(t, otherTor) ==
    /\ t.linkProber = "Standby"
    /\ \/ /\ t.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Active"]
       \/ /\ otherTor.name = heartbeatSender
          /\ UNCHANGED t
       \/ /\ "noResponse" = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Unknown"]

LinkProberActive(t, otherTor) ==
    /\ t.linkProber = "Active"
    /\ \/ /\ t.name = heartbeatSender
          /\ UNCHANGED t
       \/ /\ otherTor.name = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Standby"]
       \/ /\ "noResponse" = heartbeatSender
          /\ t' = [t EXCEPT !.linkProber = "Unknown"]

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

Environment ==
    \/ FailMux
    \/ FailHeartbeat
    \/ FailTor(torA, torB)
    \/ FailTor(torB, torA)

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
        active |-> { t \in {torA, torB} : t.linkManager = "Active"}
    ]
=============================================================================