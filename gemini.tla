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
    muxPointingTo,       \* Which ToR the MUX cable itself is pointing to 
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

vars == <<torA, torB, muxPointingTo,  heartbeatSender>>

InitialTorStates == 
    [linkManager    |-> "Checking",
     linkProber      |-> "Unknown",
     linkState       |-> "LinkDown",
     muxState        |-> "MuxWait"]

LMStates == {"Checking", "Active", "Standby"}
LPStates == {"Active", "Standby", "Unknown"}
LinkStates == {"LinkUp", "LinkDown"}
MuxStates == {"Active", "Standby", "MuxWait", "LinkWait"}

\* 
ActiveTor == [linkManager|->"Active", linkProber|->"Active", linkState|->"LinkUp", muxState|->"MuxActive"]

TypeOK == 
    /\ torA \in [name:{"torA"}, linkManager: LMStates, linkProber: LPStates, linkState: LinkStates, muxState: MuxStates]
    /\ torB \in [name:{"torB"}, linkManager: LMStates, linkProber: LPStates, linkState: LinkStates, muxState: MuxStates]
    /\ heartbeatSender \in {"torA", "torB", "noResponse"} 
    /\ muxPointingTo \in {"torA", "torB"}

Init == 
    /\ torA = [name |-> "torA", linkManager |-> "Checking", linkProber |-> "Unknown", linkState |-> "LinkDown", muxState |-> "MuxWait"]
    /\ torB = [name |-> "torB", linkManager |-> "Checking", linkProber |-> "Unknown", linkState |-> "LinkDown", muxState |-> "MuxWait"]
    /\ muxPointingTo \in {"torA", "torB"}
    /\ heartbeatSender = "noResponse"

LinkManagerCheck(t, otherTor) ==
    (***********************************************************************)
    (* LinkManager takes an action by looking at other states. This action *)
    (* is defined based on the decision table.                             *)
    (***********************************************************************)
    \* MuxState transitions to MuxWait
    /\  \/  /\  t.linkState = "LinkUp"
            /\  \/  t.muxState = "Active"   /\  t.linkProber = "Standby"
                \/  t.muxState = "Standby"  /\  t.linkProber = "Active" 
                \/  t.muxState = "LinkWait" /\  t.linkProber # "Unknown"
            /\  t' = [t EXCEPT !.muxState = "MuxWait"]
        \* MuxState transitions to MuxLinkWait
        \/  /\  t.linkProber = "Unknown"
            /\  t.muxState = "Active"
            /\  t' = [t EXCEPT !.muxState = "LinkWait"]
    /\  UNCHANGED <<muxPointingTo, otherTor, heartbeatSender>>

LinkManagerSwitch(t, otherTor) ==
    /\  t.muxState = "Standby"
    /\  t.linkProber = "Unknown"
    /\  t' = [t EXCEPT !.muxState = "LinkWait"]
    /\  UNCHANGED <<otherTor, muxPointingTo, heartbeatSender>>

XCVRD(t, otherTor) ==
\* TODO: Mux is pointing in wrong direction, when to ask where it's pointing?
    /\  t.muxState = "MuxWait"
    /\  \/  /\  muxPointingTo = t.name
            /\  t' = [t EXCEPT !.muxState = "Active"]
        \/  /\  muxPointingTo # t.name
            /\  t' = [t EXCEPT !.muxState = "Standby"]
    /\  UNCHANGED <<otherTor, heartbeatSender, muxPointingTo>>

SendHeartbeat(sender) ==
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\  muxPointingTo = sender.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\  heartbeatSender' = sender.name
    /\  UNCHANGED <<torA, torB, muxPointingTo>>

ReceiveHeartbeat(t, otherTor) ==
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    /\  \/  /\  heartbeatSender = t.name
            /\  t' = [t EXCEPT !.linkProber = "Active"]
        \/  /\  heartbeatSender = otherTor.name
            /\  t' = [t EXCEPT !.linkProber = "Standby"]
        \/  /\  heartbeatSender = "noResponse"
            /\  t' = [t EXCEPT !.linkProber = "Unknown"]
    /\  UNCHANGED <<otherTor, heartbeatSender, muxPointingTo>>

System ==
    \/ LinkManagerCheck(torA, torB)
    \/ LinkManagerCheck(torB, torA)
    \/ LinkManagerSwitch(torA, torB)
    \/ LinkManagerSwitch(torB, torA)
    \/ SendHeartbeat(torA)
    \/ SendHeartbeat(torB)
    \/ ReceiveHeartbeat(torA, torB)
    \/ ReceiveHeartbeat(torB, torA)
    \/ XCVRD(torA, torB)
    \/ XCVRD(torB, torA)    

-----------------------------------------------------------------------------

FailHeartbeat ==
    (*****************************************************************************)
    (* Sender fails to send heartbeat to ToR's making them go into unknown state *)
    (*****************************************************************************)
    /\  heartbeatSender' = "noResponse"
    /\  UNCHANGED <<torA, torB, muxPointingTo>>

FailMux ==
    (******************************************************************)
    (* Failure Action for inconsistent MUX States with MuxCable State *)
    (******************************************************************)
    /\  muxPointingTo' \in {"torA", "torB"}
    /\  UNCHANGED <<torA, torB, heartbeatSender>>

Environment ==
    \/ FailHeartbeat
    \/ FailMux    

-----------------------------------------------------------------------------

Next == 
    Environment \/ System

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

AtMostOneActive ==
    []~(torA.linkManager = "Active" /\ torB.linkManager = "Active")

RepeatedlyOneActive ==
    []<>(torA.linkManager = "Active" \/ torB.linkManager = "Active")

THEOREM Spec => AtMostOneActive /\ RepeatedlyOneActive

=============================================================================