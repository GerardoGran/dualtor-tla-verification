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
    [ alive: BOOLEAN, 
      name: T,
      xcvrd: XCVRDStates,
      heartbeat: {"on", "off"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: LPStates,
      linkState: LinkStates,
      muxState: MuxStates,
      target: T \union {"-"} ]


ActiveTor == 
    \* "Goal" state for a ToR.
    [ alive: {TRUE},
      name: T, 
      xcvrd: {"-"},
      heartbeat: {"on"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: {"LPActive"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxActive"},
      target: {"-"} ]
          
StandbyTor == 
    \* The Standby ToR needs orchagent to be tunneling to the ActiveTor
    [ alive: {TRUE},
      name: T, 
      xcvrd: {"-"},
      heartbeat: {"on"},
      heartbeatIn: SUBSET (T \union {"noResponse"}),
      linkProber: {"LPStandby"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxStandby"},
      target: {"-"} ]
          
ActiveToRs ==
    { t \in {torA, torB} : t \in ActiveTor }
        
StandbyToRs ==
    { t \in {torA, torB} : t \in StandbyTor }

AliveToRs ==
    { t \in {torA, torB} : t.alive }

TypeOK == 
    /\ torA \in ToR
    /\ torB \in ToR    
    /\ mux \in [ active: T, next: T, serving: T \union {"-"} ]

Init ==
    LET InitialTor(name) == 
        [ alive           |-> TRUE,
          name            |-> name,
          xcvrd           |-> "check",
          heartbeat       |-> "on",
          heartbeatIn     |-> {},
          linkProber      |-> "LPWait",
          linkState       |-> "LinkDown",
          muxState        |-> "MuxWait",
          target          |-> "-" ]
    IN  /\ mux \in {f \in [ active: T, next: T, serving: T \union {"-"} ]: f.active = f.next /\ f.serving # "-"}
        /\ torA = InitialTor("torA")
        /\ torB = InitialTor("torB")

-----------------------------------------------------------------------------
\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022
\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/t-gegranados/ERThXZdF5MVFusk2rP-PF0cBGguDR3Rt9yJ3WxxwAt0hpg?e=i8aS4v

(**************************************************************************************************)
(* MuxState State Transitions depend on LinkManager's decisions and XCVRD responses when checking *)
(* or switching the MuxCable's direction                                                          *)
(**************************************************************************************************)

TRIGGER_CHECK(t) ==
    (************************************************************)
    (* Beginning of blocking check request between ToR and Mux. *)
    (* Transitions muxState to MuxWait.                         *)
    (* Mux must not be blocked by other request                 *)
    (************************************************************)
    /\ t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check" ]
    /\  \/  /\ mux.serving = "-"
            /\ mux' = [ mux EXCEPT !.serving = t.name]

ACK_CHECK(t, otherTor) ==
    (**********************************************)
    (* Acknowledge Check request from serving tor.*)
    (* Change muxState of tor to correct state.   *)
    (* Unblock mux.                               *)
    (**********************************************)
    /\ UNCHANGED <<otherTor>>
    /\ t.xcvrd = "check"
    /\  mux.serving = t.name
    /\  \/  /\ mux.active = t.name
            /\ t' = [t EXCEPT !.muxState = "MuxActive", !.heartbeat = "on", !.xcvrd = "-"]
        \/  /\ mux.active = otherTor.name
            /\ t' = [t EXCEPT !.muxState = "MuxStandby", !.heartbeat = "on", !.xcvrd = "-"]
    /\ mux' = [ mux EXCEPT  !.serving = "-"]


TRIGGER_SWITCH(t, target) ==
    (*************************************************************)
    (* Beginning of switch between ToR and Mux.                  *)
    (* Transitions muxState to MuxWait and linkProber to LPWait. *)
    (* Target refers to ToR the Mux should point to.             *)
    (* Mux must not be blocked by other request                  *)
    (*************************************************************)
    /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "switch", !.linkProber = "LPWait", !.target = target.name ]
    /\  \/  /\  mux.serving = "-"
            /\  mux' = [ mux EXCEPT !.serving = t.name]

        
ACK_SWITCH(t, otherTor) ==
    (*********************************************************************)
    (* Acknowledge Switch request from serving ToR.                      *)
    (* ToR assumes correct switching action and changes to target state. *)
    (* Unblock Mux.                                                      *)
    (*********************************************************************)
    /\ UNCHANGED otherTor
    /\ t.xcvrd = "switch"
    /\ mux.serving = t.name
    /\  \/  /\ t.target = t.name
            /\ t' = [ t EXCEPT !.muxState = "MuxActive", !.xcvrd = "-", !.target = "-"]
        \/  /\ t.target = otherTor.name
            /\ t' = [ t EXCEPT !.muxState = "MuxStandby", !.xcvrd = "-", !.target = "-"]
    /\ mux' = [ mux EXCEPT !.next = t.target, !.serving = "-"]

EXEC_SWITCH ==
    (*****************************)
    (* Execute switch operation. *)
    (* Mux must be unblocked.    *)
    (* Mux direction changes.    *)
    (*****************************)
    /\ UNCHANGED <<torA, torB>>
    /\ mux.serving = "-"
    /\ mux.active # mux.next    \* could be removed
    /\ mux' = [ mux EXCEPT !.active = mux.next]

NACK(t, otherTor) ==
    (*************************************************************)
    (* If Mux is serving other ToR, return a no acknowledgement. *)
    (* Unblock ToR.                                              *)
    (* Clear t.xcvrd.                                            *)
    (* Transition MuxState to MuxStateUnknown                    *)
    (*************************************************************)
    /\ UNCHANGED otherTor
    /\ t.xcvrd \in {"check", "switch"}
    /\ mux.serving # t.name
    /\ t' =  [ t EXCEPT !.muxState = "MuxUnknown", !.xcvrd = "-", !.target = "-"]
    /\ UNCHANGED mux

\* Mux-Side Actions
MuxCommands ==
    \/ EXEC_SWITCH
    \/ ACK_CHECK(torA, torB)
    \/ ACK_CHECK(torB, torA)
    \/ ACK_SWITCH(torA, torB)
    \/ ACK_SWITCH(torB, torA)
    \/ NACK(torA, torB)
    \/ NACK(torB, torA)

----------------------------


MuxStateActive(t, otherTor) ==
    /\ t.alive
    /\  t.muxState = "MuxActive"
    /\  \/  /\ t.linkState = "LinkUp"
            \* LinkUp MuxStateActive Row
            /\  \/  /\ t.linkProber \in {"LPStandby", "LPUnknown", "LPWait"}
                    /\ TRIGGER_CHECK(t)
            /\ UNCHANGED <<otherTor>>
        \/  /\ t.linkState = "LinkDown"
            \* Switch to Standby
            /\ TRIGGER_SWITCH(t, otherTor)
            /\ UNCHANGED otherTor

MuxStateStandby(t, otherTor) ==
    /\ t.alive
    /\  t.muxState = "MuxStandby"
    /\  \/  /\ t.linkState = "LinkUp"
        \* LinkUp MuxStateStandby Row
            /\  \/  /\ t.linkProber \in {"LPActive", "LPWait"}
                    /\ TRIGGER_CHECK(t)
                    /\ UNCHANGED <<otherTor>>
                \/  /\ t.linkProber = "LPUnknown"
                    \* Switch to Active
                    /\ TRIGGER_SWITCH(t, t)
                    /\ UNCHANGED otherTor
        \/  /\ t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\ t.linkProber \in {"LPUnknown, LPWait"}
            /\ TRIGGER_CHECK(t)
            /\ UNCHANGED <<mux, otherTor>>

MuxStateUnknown(t, otherTor) ==
    /\ t.alive
    /\  t.muxState = "MuxUnknown"
    /\  \/  /\ t.linkState = "LinkUp"
            \* LinkUp MuxStateStandby Row
            /\ TRIGGER_CHECK(t)
        \/  /\ t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\ t.linkProber \in {"LPUnknown, LPWait"}
            /\ TRIGGER_CHECK(t)
    /\  UNCHANGED <<otherTor>>

MuxStateWait(t, otherTor) ==
    /\ t.alive
    /\ t.muxState = "MuxWait"  
    \* If Mux is busy, go to Unknown
    /\ UNCHANGED <<t, otherTor, mux>>


-----------------------------------------------------------------------------

\* State machine page 09 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/zhangjing/EclAzBSCq_5KuwgbbpyUlMQB1RS_X9nibOrM1PjT8wM_uw?e=eBtJKl

SendHeartbeat(t) ==
    /\ UNCHANGED <<mux>>
    /\ t.alive
    /\ t.linkState = "LinkUp"
    /\ t.heartbeat = "on"
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\ mux.active = t.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\ torA' = [ torA EXCEPT !.heartbeatIn = @ \union {t.name} ]
    /\ torB' = [ torB EXCEPT !.heartbeatIn = @ \union {t.name} ]

ReadHeartbeat(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ t.alive
    /\ t.linkState = "LinkUp"
    /\  \/ \E heartbeat \in t.heartbeatIn:
            /\  \/  /\ t.name = heartbeat
                    /\ t' = [t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat}]

                \/  /\ otherTor.name = heartbeat
                    /\ t' = [t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat}]

----------------------------------------------------------------------------

MuxState(t, otherTor) == 
    \/ MuxStateActive(t, otherTor)
    \/ MuxStateWait(t, otherTor)
    \/ MuxStateStandby(t, otherTor)
    \/ MuxStateUnknown(t, otherTor)

LinkState(t, otherTor) ==
    /\ UNCHANGED <<otherTor, mux>>
    /\ t.alive
    /\ t.linkState = "LinkDown" \* unnecessary, because going from LinkUp to LinkUp is just (finite) stuttering.  However, this conjunct prevent the debugger from evaluating this action when it is stuttering.
    /\ t' = [t EXCEPT !.linkState = "LinkUp"]

-----------------------------------------------------------------------------

System ==
    (****************************************************************************)
    (* Mux handling a switch or check command.                                  *)
    (****************************************************************************)
    \/ EXEC_SWITCH
    \/ ACK_CHECK(torA, torB)
    \/ ACK_SWITCH(torA, torB)
    \/ ACK_CHECK(torB, torA)
    \/ ACK_SWITCH(torB, torA)
    \/ NACK(torA, torB)
    \/ NACK(torB, torA)
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
    \/ ReadHeartbeat(torA, torB)
    \/ ReadHeartbeat(torB, torA)
    (****************************************************************************)
    (* Notification from the kernel that a physical link (L1) came up.          *)
    (****************************************************************************)
    \/ LinkState(torA, torB)
    \/ LinkState(torB, torA)

-----------------------------------------------------------------------------

FailServerHeartbeat ==
    (*************************************************)
    (* Makes Server unable to respond to heartbeat.  *)
    (* Should lead to both ToR's going into Unknown. *)
    (*************************************************)
    TRUE


FailServer ==
    (************************************************************)
    (* Server shuts off/crashes.                                *)
    (* Mux loses power, Heartbeats fail, LinkDown on both ToR's *)  \*TODO Potentially LinkState goes down in different points of time.
    (************************************************************)  \*TODO re initialize MUX when Server goes up
    /\ FailServerHeartbeat
    /\ TRUE

FailHeartbeat(t, otherTor) ==
    (*****************************************************************************)
    (* Sender fails to send heartbeat to ToR's making them go into unknown state *)
    (*****************************************************************************)
    /\ UNCHANGED mux
    /\ \/ /\ \E heartbeat \in SUBSET torA.heartbeatIn:
                /\ torA' = [ torA EXCEPT !.heartbeatIn = heartbeat ]
                /\ UNCHANGED torB
       \/ /\ \E heartbeat \in SUBSET torB.heartbeatIn:
                /\ torB' = [ torB EXCEPT !.heartbeatIn = heartbeat ]
                /\ UNCHANGED torA


FailTor(t, otherTor) ==
    (*****************************)
    (* TOR powers off or crashes *)
    (*****************************)
    /\ UNCHANGED <<otherTor, mux>>
    /\ t' = [t EXCEPT !.alive = FALSE]

CrashXCVRD(t, otherTor) ==
    (***************************************************************)
    (* XCVRD DAEMON crashes.                                       *)
    (* Set t.xcvrd to "crashed".                                   *)
    (* Makes any TRIGGER or ACK transition to MuxStateStandby on t *)
    (***************************************************************)
    TRUE


FailLinkState(t, otherTor) ==
    (******************)
    (* Link goes down *)
    (******************)
    /\ UNCHANGED <<otherTor, mux>>
    /\ t' = [t EXCEPT !.linkState = "LinkDown"]

FailMux ==
    (******************************************************************)
    (* Failure Action for inconsistent MUX States with MuxCable State *)
    (******************************************************************)
    /\  UNCHANGED <<torA, torB>>
    /\  mux' \in [ active: T, next: T ]



Environment ==
    \* \/ FailMux
    \/ FailHeartbeat(torA, torB)
    \/ FailHeartbeat(torB, torA)
    \* \/ FailTor(torA, torB)
    \* \/ FailTor(torB, torA)
    \* \/ FailXCVRD(torA, torB)
    \* \/ FailXCVRD(torB, torA)
    \* \/ FailLinkState(torA, torB)
    \* \/ FailLinkState(torB, torA)


----------------------------------------------------------------------------
(******************)
(* Reboot Actions *)
(******************)



-----------------------------------------------------------------------------

Fairness ==
    /\ WF_vars(System)
    /\ WF_vars(MuxState(torA, torB))
    /\ WF_vars(MuxState(torB, torA))
    /\ WF_vars(ReadHeartbeat(torA, torB))
    /\ WF_vars(ReadHeartbeat(torB, torA))
    /\ WF_vars(SendHeartbeat(torA)) 
    /\ WF_vars(SendHeartbeat(torB))
    /\ WF_vars(LinkState(torA, torB)) 
    /\ WF_vars(LinkState(torB, torA))
    /\ WF_vars(MuxCommands)

WithoutFailureSpec ==
    Init /\ [][System]_vars /\ Fairness

Next == 
    \/ Environment
    \/ System

Spec ==
    Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

NotForeverBothActive ==
    \* Both tors are never active indefinitely. In other words, there is no behavior
    \* such that both tors are indefinitely active from some point onward.
    ~(<>[](torA \in ActiveTor /\ torB \in ActiveTor))

RepeatedlyOneActive ==
    \* One or more alive tors imply that there repeatedly exists an active tor.
    []<>(AliveToRs # {} => \E t \in AliveToRs: t \in ActiveTor)

THEOREM Spec => 
    /\ NotForeverBothActive
    /\ RepeatedlyOneActive

-----------------------------------------------------------------------------

Alias ==
    [
        torA |-> torA, torB |-> torB, mux |-> mux,
        active |-> { t.name : t \in ActiveToRs },
        standby |-> { t.name : t \in StandbyToRs }
    ]
=============================================================================