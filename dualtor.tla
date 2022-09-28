------------------------------- MODULE dualtor -------------------------------
(**********************************************************************************************)
(* This is a specification for the DualTor Standby/Active Protocol. It describes the behavior *)
(* of the submodules that make up a two Top of Rack (TOR) solution for                        *)
(* reliability. The purpose of the specification is t find all possible failure               *)
(* scenarios in the algorithm by exploring reachable states simulating                        *)
(* transitions in the submodules' state machines.                                             *)
(**********************************************************************************************)

VARIABLES 
    torA,
    torB,
    mux
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
XCVRDStates == {"switch", "check", "-", "crashed"}

Heartbeats == [sender:T, switchTarget:T \union {"-"}]

ToR ==
    [ alive: BOOLEAN, 
      name: T,
      xcvrd: XCVRDStates,
      heartbeat: {"on", "off"},
      heartbeatIn: SUBSET (Heartbeats),
      linkProber: LPStates,
      linkState: LinkStates,
      muxState: MuxStates,
      target: T \union {"-"} ]


ActiveTor == 
    \* "Goal" state for a ToR.
    [ alive: {TRUE},
      name: T, 
      xcvrd: XCVRDStates,
      heartbeat: {"on"},
      heartbeatIn: SUBSET (Heartbeats),
      linkProber: {"LPActive", "LPUnknown"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxActive", "MuxWait"},
      target: {"-"} ]
          
StandbyTor == 
    \* The Standby ToR needs orchagent to be tunneling to the ActiveTor
    [ alive: {TRUE},
      name: T, 
      xcvrd: XCVRDStates,
      heartbeat: {"on"},
      heartbeatIn: SUBSET (Heartbeats),
      linkProber: {"LPStandby", "LPUnknown"}, 
      linkState: {"LinkUp"},
      muxState: {"MuxStandby", "MuxWait"},
      target: {"-"} ]
          
ActiveToRs ==
    { t \in {torA, torB} : t \in ActiveTor }
        
StandbyToRs ==
    { t \in {torA, torB} : t \in StandbyTor }

AliveToRs ==
    { t \in {torA, torB} : t.alive /\ t.xcvrd # "crashed" }

TypeOK == 
    /\  torA \in ToR
    /\  torB \in ToR    
    /\  mux \in [ active: T, next: T, serving: T \union {"-"} ]

Init ==
    LET InitialTor(name) == 
        [ alive           |-> TRUE,
          name            |-> name,
          xcvrd           |-> "-",
          heartbeat       |-> "on",
          heartbeatIn     |-> {},
          linkProber      |-> "LPWait",
          linkState       |-> "LinkDown",
          muxState        |-> "MuxWait",
          target          |-> "-" ]
    IN  /\  mux \in {f \in [ active: T, next: T, serving: T \union {"-"} ]: f.active = f.next /\ f.serving = "-"}
        /\  torA = InitialTor("torA")
        /\  torB = InitialTor("torB")

-----------------------------------------------------------------------------
\* State machine and transition table pages 12 & 13 of the Powerpoint presentation as of 08/25/2022
\* XCVRD daemon described on page 11 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/t-gegranados/ERThXZdF5MVFusk2rP-PF0cBGguDR3Rt9yJ3WxxwAt0hpg?e=i8aS4v

(**************************************************************************************************)
(* MuxState State Transitions depend on LinkManager's decisions and XCVRD responses when checking *)
(* or switching the MuxCable's direction                                                          *)
(**************************************************************************************************)

\*TODO WRITE_XCVRD(t, action) ==

XCVRD_FAIL_RESPONSE(t, otherTor) ==
    /\  t.alive
    /\  t.xcvrd = "crashed"
    /\  t' = [ t EXCEPT !.muxState = "MuxStandby", !.target = "-"]
    /\  UNCHANGED <<mux, otherTor>>

TRIGGER_CHECK(t, otherTor) ==
    (************************************************************)
    (* Beginning of blocking check request between ToR and Mux. *)
    (* Transitions muxState to MuxWait.                         *)
    (* Mux must not be blocked by other request                 *)
    (************************************************************)
    \/  XCVRD_FAIL_RESPONSE(t, otherTor)
    \/  /\  t.xcvrd = "-"
        /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check" ]
        /\  \/  /\  mux.serving = "-"
                /\  mux' = [ mux EXCEPT !.serving = t.name]
            \/  /\  mux.serving # "-"
                /\  UNCHANGED mux
        /\  UNCHANGED otherTor

ACK_CHECK(t, otherTor) ==
    (**********************************************)
    (* Acknowledge Check request from serving tor.*)
    (* Change muxState of tor to correct state.   *)
    (* Unblock mux.                               *)
    (**********************************************)
    /\  \/  XCVRD_FAIL_RESPONSE(t, otherTor)
        \/  /\  t.xcvrd = "check"
            /\  mux.serving = t.name
            /\  \/  /\  mux.active = t.name
                    /\  t' = [t EXCEPT !.muxState = "MuxActive", !.heartbeat = "on", !.xcvrd = "-"]
                \/  /\  mux.active = otherTor.name
                    /\  t' = [t EXCEPT !.muxState = "MuxStandby", !.heartbeat = "on", !.xcvrd = "-"]
    /\  mux' = [ mux EXCEPT  !.serving = "-"]
    /\  UNCHANGED otherTor


TRIGGER_SWITCH(t, target, otherTor) ==
    (*************************************************************)
    (* Beginning of switch between ToR and Mux.                  *)
    (* Transitions muxState to MuxWait and linkProber to LPWait. *)
    (* Target refers to ToR the Mux should point to.             *)
    (* Mux must not be blocked by other request                  *)
    (*************************************************************)
    \/  XCVRD_FAIL_RESPONSE(t, otherTor)
    \/  /\  t.xcvrd = "-"
        /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "switch", !.linkProber = "LPWait", !.target = target.name ]
        /\  \/  /\  mux.serving = "-"
                /\  mux' = [ mux EXCEPT !.serving = t.name]
            \/  /\  mux.serving # "-"
                /\  UNCHANGED mux
        /\ UNCHANGED otherTor

        
ACK_SWITCH(t, otherTor) ==
    (*********************************************************************)
    (* Acknowledge Switch request from serving ToR.                      *)
    (* ToR assumes correct switching action and changes to target state. *)
    (* Unblock Mux.                                                      *)
    (*********************************************************************)
    /\  \/  XCVRD_FAIL_RESPONSE(t, otherTor)
        \/  /\  t.xcvrd = "switch"
            /\  mux.serving = t.name
            /\  \/  /\  t.target = t.name
                    /\  t' = [ t EXCEPT !.muxState = "MuxActive", !.xcvrd = "-", !.target = "-"]
                \/  /\  t.target = otherTor.name
                    /\  t' = [ t EXCEPT !.muxState = "MuxStandby", !.xcvrd = "-", !.target = "-"]
    /\  mux' = [ mux EXCEPT !.next = t.target, !.serving = "-"]
    /\  UNCHANGED otherTor

EXEC_SWITCH ==
    (*****************************)
    (* Execute switch operation. *)
    (* Mux must be unblocked.    *)
    (* Mux direction changes.    *)
    (*****************************)
    /\  UNCHANGED <<torA, torB>>
    /\  mux.serving = "-"
    /\  mux.active # mux.next    \* could be removed
    /\  mux' = [ mux EXCEPT !.active = mux.next]

NACK(t, otherTor) ==
    (*************************************************************)
    (* If Mux is serving other ToR, return a no acknowledgement. *)
    (* Unblock ToR.                                              *)
    (* Clear t.xcvrd.                                            *)
    (* Transition MuxState to MuxStateUnknown                    *)
    (*************************************************************)

    \* This happens if the MUX cable has no power or is unplugged, etc.
    \/  XCVRD_FAIL_RESPONSE(t, otherTor)
    \/  /\  t.xcvrd \in {"check", "switch"}
        /\  \/  mux.serving # t.name
            \/  ~t.alive
        /\  t' =  [ t EXCEPT !.muxState = "MuxUnknown", !.xcvrd = "-", !.target = "-"]
        /\  UNCHANGED <<mux, otherTor>>


\* Mux-Side Actions
MuxCommands ==
    \/  ACK_CHECK(torA, torB)
    \/  ACK_CHECK(torB, torA)
    \/  ACK_SWITCH(torA, torB)
    \/  ACK_SWITCH(torB, torA)
    \/  XCVRD_FAIL_RESPONSE(torA, torB)
    \/  XCVRD_FAIL_RESPONSE(torB, torA)

----------------------------------------------------------------------------

(***************************************************************************************************)
(* Anytime there is a state change by LinkProber or CHECK, LinkManager does StateTransitionHandler *)
(* to evaluate the state combination of all the Submodules. This Action decides what action must   *)
(* be taken (SWITCH or CHECK).                                                                     *)
(***************************************************************************************************)
StateTransitionHandler(t, otherTor) ==
    \*LinkUp Table
    \/  /\  t.linkState = "LinkUp"
            \*MuxActive row
        /\  \/  /\  t.muxState =  "MuxActive"
                /\  t.linkProber \in {"LPStanby", "LPUnknown", "LPWait"}
                /\  TRIGGER_CHECK(t, otherTor)
            \*MuxStandby row
            \/  /\  t.muxState = "MuxStandby"
                /\  \/  /\  t.linkProber \in {"LPActive", "LPWait"}
                        /\  TRIGGER_CHECK(t, otherTor)
                    \/  /\  t.linkProber = "LPUnknown"
                        /\  TRIGGER_SWITCH(t, t, otherTor)
            \*MuxUnknown row
            \/  /\  t.muxState = "MuxUnknown"
                /\  TRIGGER_CHECK(t, otherTor)
    \*LinkDown Table
    \/  /\  t.linkState = "LinkDown"
            \*MuxActive row
        /\  \/  /\  t.muxState =  "MuxActive"
                /\  TRIGGER_SWITCH(t, otherTor, otherTor)
            \*MuxStandby row
            \/  /\  t.muxState = "MuxStandby"
                /\  t.linkProber \in {"LPUnknown", "LPWait"}
                /\  TRIGGER_CHECK(t, otherTor)
            \*MuxUnknown row
            \/  /\  t.muxState = "MuxUnknown"
                /\  t.linkProber \in {"LPUnknown", "LPWait"}
                /\  TRIGGER_CHECK(t, otherTor)

---------------------------------------------------------------------------


MuxStateActive(t, otherTor) ==
    /\  t.alive
    /\  t.muxState = "MuxActive"
    /\  \/  /\  t.linkState = "LinkUp"
            \* LinkUp MuxStateActive Row
            /\  \/  /\  t.linkProber \in {"LPStandby", "LPUnknown", "LPWait"}
                    /\  TRIGGER_CHECK(t, otherTor)
            /\  UNCHANGED <<otherTor>>
        \/  /\  t.linkState = "LinkDown"
            \* Switch to Standby
            /\  TRIGGER_SWITCH(t, otherTor, otherTor)
            /\  UNCHANGED otherTor

MuxStateStandby(t, otherTor) ==
    /\  t.alive
    /\  t.muxState = "MuxStandby"
    /\  \/  /\  t.linkState = "LinkUp"
        \* LinkUp MuxStateStandby Row
            /\  \/  /\  t.linkProber \in {"LPActive", "LPWait"}
                    /\  TRIGGER_CHECK(t, otherTor)
                    /\  UNCHANGED <<otherTor>>
                \/  /\  t.linkProber = "LPUnknown"
                    \* Switch to Active
                    /\  TRIGGER_SWITCH(t, t, otherTor)
                    /\  UNCHANGED otherTor
        \/  /\  t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\  t.linkProber \in {"LPUnknown", "LPWait"}
            /\  TRIGGER_CHECK(t, otherTor)
            /\  UNCHANGED <<otherTor>>

MuxStateUnknown(t, otherTor) ==
    /\  t.alive
    /\  t.muxState = "MuxUnknown"
    /\  \/  /\  t.linkState = "LinkUp"
            \* LinkUp MuxStateStandby Row
            /\  TRIGGER_CHECK(t, otherTor)
        \/  /\  t.linkState = "LinkDown"
        \* LinkDown MuxStateStandby Row
            /\  t.linkProber \in {"LPUnknown", "LPWait"}
            /\  TRIGGER_CHECK(t, otherTor)
    /\  UNCHANGED <<otherTor>>

MuxStateWait(t, otherTor) ==
    /\  t.alive
    /\  t.muxState = "MuxWait"  
    /\  t.xcvrd = "-"
    /\  t' = [ t EXCEPT  !.muxState = "MuxUnknown"]
    /\  UNCHANGED <<otherTor, mux>>


-----------------------------------------------------------------------------

\* State machine page 09 of the Powerpoint presentation as of 08/25/2022
\* https://microsoft-my.sharepoint.com/:u:/p/zhangjing/EclAzBSCq_5KuwgbbpyUlMQB1RS_X9nibOrM1PjT8wM_uw?e=eBtJKl

SendHeartbeat(t, otherTor) ==
    /\  UNCHANGED <<mux>>
    /\  t.alive
    /\  t.linkState = "LinkUp"
    /\  t.heartbeat = "on"
    (****************************************************************************)
    (* Active ToR sends heartbeat to server. MUX duplicates packet and sends it *)
    (* to both ToR's                                                            *)
    (****************************************************************************)
    /\  mux.active = t.name  \* The MUX will drop traffic from ToR if it is not pointing to it
    /\  \/  /\  t.xcvrd # "crashed" \* Normal heartbeat behavior
            /\  torA' = [ torA EXCEPT !.heartbeatIn = @ \union {[sender |-> t.name, switchTarget |-> "-"]} ]
            /\  torB' = [ torB EXCEPT !.heartbeatIn = @ \union {[sender |-> t.name, switchTarget |-> "-"]} ]
        \/  /\  t.xcvrd = "crashed" \* When XCVRD crashes on active, LinkProber will send a heartbeat telling peer to take over
            /\  torA' = [ torA EXCEPT !.heartbeatIn = @ \union {[sender |-> t.name, switchTarget |-> otherTor.name]} ]
            /\  torB' = [ torB EXCEPT !.heartbeatIn = @ \union {[sender |-> t.name, switchTarget |-> otherTor.name]} ]

ReadHeartbeat(t, otherTor) ==
    /\  UNCHANGED <<otherTor>>
    /\  t.alive
    /\  t.linkState = "LinkUp"
    /\  \/  /\  \E heartbeat \in t.heartbeatIn:
                \/  /\  t.name = heartbeat.sender
                    \* Incoming heartbeat is self. LPActive
                    /\  \/  /\  t.muxState \in {"MuxStandby", "MuxUnknown"}
                            \* Trigger Check, set linkProber state and remove heartbeat
                            /\  \/  /\  t.xcvrd = "-"   \* If nothing pending on xcvrd trigger check
                                    /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check", !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat} ]
                                    /\  \/  /\  mux.serving = "-"    \* If mux is free, serve t
                                            /\  mux' = [ mux EXCEPT !.serving = t.name]
                                        \/  /\  mux.serving # "-"    \* Else no change on mux
                                            /\  UNCHANGED mux
                                \/  /\  t.xcvrd # "-"   \* If something pending on xcvrd only change linkProber and remove heartbeat
                                    /\  t' = [ t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat} ]
                                    /\  UNCHANGED mux

                        \/  /\  t.muxState \notin {"MuxStandby", "MuxUnknown"}
                            /\  t' = [ t EXCEPT !.linkProber = "LPActive", !.heartbeatIn = @ \ {heartbeat} ]
                            /\  UNCHANGED mux
                \/  /\  otherTor.name = heartbeat.sender
                    /\  \/  /\  t.muxState \in {"MuxActive", "MuxUnknown"}
                    \* Trigger Check, set linkProber state and remove heartbeat
                            /\  \/  /\  t.xcvrd = "-"   \* If nothing pending on xcvrd trigger check
                                    /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check", !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat} ]
                                    /\  \/  /\  mux.serving = "-"    \* If mux is free, serve t
                                            /\  mux' = [ mux EXCEPT !.serving = t.name]
                                        \/  /\  mux.serving # "-"    \* Else no change on mux
                                            /\  UNCHANGED mux
                                \/  /\  t.xcvrd # "-"   \* If something pending on xcvrd only change linkProber and remove heartbeat
                                    /\  t' = [ t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat} ]
                                    /\  UNCHANGED mux
                        \/  /\  t.muxState \notin {"MuxActive", "MuxUnknown"}
                            /\  \/  /\  heartbeat.switchTarget # "-"
                                    /\  TRIGGER_SWITCH(t, t, otherTor)
                                \/  /\  heartbeat.switchTarget = "-"
                                    /\  t' = [ t EXCEPT !.linkProber = "LPStandby", !.heartbeatIn = @ \ {heartbeat} ]
                                    /\  UNCHANGED mux
        \/  /\  t.heartbeatIn = {}
            /\  \/  /\  t.muxState \in {"MuxActive", "MuxUnknown"}
                        \* Trigger Check, set linkProber state
                        /\  \/  /\  t.xcvrd = "-"   \* If nothing pending on xcvrd trigger check
                                /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check", !.linkProber = "LPUnknown"]
                                /\  \/  /\  mux.serving = "-"    \* If mux is free, serve t
                                        /\  mux' = [ mux EXCEPT !.serving = t.name]
                                    \/  /\  mux.serving # "-"    \* Else no change on mux
                                        /\  UNCHANGED mux
                            \/  /\  t.xcvrd # "-"   \* If something pending on xcvrd only change linkProber
                                /\  t' = [ t EXCEPT !.linkProber = "LPUnknown"]
                                /\  UNCHANGED mux
                    \/  /\  t.muxState = "MuxStandby"
                        \* Trigger Switch, set linkProber state
                        /\  TRIGGER_SWITCH(t, t, otherTor)
                    \/  /\  t.muxState = "MuxWait"
                        /\  t' = [ t EXCEPT !.linkProber = "LPUnknown" ]
                        /\  UNCHANGED mux     

----------------------------------------------------------------------------

MuxState(t, otherTor) == 
    \/  MuxStateActive(t, otherTor)
    \/  MuxStateWait(t, otherTor) 
    \/  MuxStateStandby(t, otherTor)
    \/  MuxStateUnknown(t, otherTor)

LinkState(t, otherTor) ==
    /\  UNCHANGED <<otherTor, mux>>
    /\  t.alive
    /\  t.linkState = "LinkDown" \* unnecessary, because going from LinkUp to LinkUp is just (finite) stuttering.  However, this conjunct prevent the debugger from evaluating this action when it is stuttering.
    /\  t' = [t EXCEPT !.linkState = "LinkUp"]

-----------------------------------------------------------------------------

System ==
    (****************************************************************************)
    (* Mux handling a switch or check command.                                  *)
    (****************************************************************************)
    \/  EXEC_SWITCH
    \/  ACK_CHECK(torA, torB)
    \/  ACK_SWITCH(torA, torB)
    \/  ACK_CHECK(torB, torA)
    \/  ACK_SWITCH(torB, torA)
    \/  NACK(torA, torB)
    \/  NACK(torB, torA)
    \/  XCVRD_FAIL_RESPONSE(torA, torB)
    \/  XCVRD_FAIL_RESPONSE(torB, torA)
    (****************************************************************************)
    (* XCVRD and LinkMgrd                                                       *)
    (****************************************************************************)
    \/  MuxStateActive(torA, torB)
    \/  MuxStateActive(torB, torA)
    \/  MuxStateStandby(torA, torB)
    \/  MuxStateStandby(torB, torA)
    \/  MuxStateWait(torA, torB)
    \/  MuxStateWait(torB, torA)
    \/  MuxStateUnknown(torA, torB)
    \/  MuxStateUnknown(torB, torA)
    (****************************************************************************)
    (* ToR periodically send heartbeats via the mux to the server.              *)
    (****************************************************************************)
    \/  SendHeartbeat(torA, torB)
    \/  SendHeartbeat(torB, torA)
    (****************************************************************************)
    (* ToR receives heartbeat and triggers appropriate transition in LinkProber *)
    (****************************************************************************)
    \/  ReadHeartbeat(torA, torB)
    \/  ReadHeartbeat(torB, torA)
    (****************************************************************************)
    (* Notification from the kernel that a physical link (L1) came up.          *)
    (****************************************************************************)
    \/  LinkState(torA, torB)
    \/  LinkState(torB, torA)

-----------------------------------------------------------------------------

FailServerHeartbeat ==
    (*************************************************)
    (* Makes Server unable to respond to heartbeat.  *)
    (* Should lead to both ToR's going into Unknown. *)
    (*************************************************)
    TRUE

FailMuxCable ==
    (*******************************************************)
    (* Mux Cable loses power, stops responding to requests *)
    (*******************************************************)
    /\  torA' = [torA EXCEPT !.linkState = "LinkDown"]
    /\  torB' = [torB EXCEPT !.linkState = "LinkDown"]
    /\  TRUE

FailServer ==
    (************************************************************)
    (* Server shuts off/crashes.                                *)
    (* Mux loses power, Heartbeats fail, LinkDown on both ToR's *)  \*TODO Potentially LinkState goes down in different points of time.
    (************************************************************)  \*TODO re initialize MUX when Server goes up
    /\  FailServerHeartbeat
    /\  FailMuxCable

FailHeartbeat ==
    (*****************************************************************************)
    (* Sender fails to send heartbeat to ToR's making them go into unknown state *)
    (*****************************************************************************)
    /\  UNCHANGED mux
    /\  \/  /\  torA.alive
            /\  \E heartbeat \in SUBSET torA.heartbeatIn:
                /\  torA' = [ torA EXCEPT !.heartbeatIn = heartbeat ]
                /\  UNCHANGED torB
       \/   /\  torB.alive
            /\  \E heartbeat \in SUBSET torB.heartbeatIn:
                /\  torB' = [ torB EXCEPT !.heartbeatIn = heartbeat ]
                /\  UNCHANGED torA

TimeoutHeartbeat(t, otherTor) ==
    /\  t.alive
    /\  UNCHANGED otherTor
    /\  \/  /\  t.muxState \in {"MuxActive", "MuxUnknown"}
            \* Trigger Check, set linkProber state
            /\  \/  /\  t.xcvrd = "-"   \* If nothing pending on xcvrd trigger check
                    /\  t' = [ t EXCEPT !.muxState = "MuxWait", !.xcvrd = "check", !.linkProber = "LPUnknown"]
                    /\  \/  /\  mux.serving = "-"    \* If mux is free, serve t
                            /\  mux' = [ mux EXCEPT !.serving = t.name]
                        \/  /\  mux.serving # "-"    \* Else no change on mux
                            /\  UNCHANGED mux
                \/  /\  t.xcvrd # "-"   \* If something pending on xcvrd only change linkProber
                    /\  t' = [ t EXCEPT !.linkProber = "LPUnknown"]
                    /\  UNCHANGED mux
        \/  /\  t.muxState = "MuxStandby"
            \* Trigger Switch, set linkProber state
            /\  TRIGGER_SWITCH(t, t, otherTor)
        \/  /\  t.muxState = "MuxWait"
            /\  t' = [ t EXCEPT !.linkProber = "LPUnknown" ]
            /\  UNCHANGED mux

FailTor(t, otherTor) ==
    (*****************************)
    (* TOR powers off or crashes *)
    (*****************************)
    /\  UNCHANGED <<otherTor, mux>>
    /\  t' = [t EXCEPT !.alive = FALSE, !.heartbeatIn = {}] \*TODO Set to initial states

CrashXCVRD(t, otherTor) ==
    (***************************************************************)
    (* XCVRD DAEMON crashes.                                       *)
    (* Set t.xcvrd to "crashed".                                   *)
    (* Makes any TRIGGER or ACK transition to MuxStateStandby on t *)
    (***************************************************************)
    /\  t.alive
    /\  t' = [ t EXCEPT !.xcvrd = "crashed" ]
    /\  UNCHANGED <<mux, otherTor>>

\*TODO FailXCVRDWrite

FailLinkState(t, otherTor) ==
    (******************)
    (* Link goes down *)
    (******************)
    /\  t.alive
    /\  UNCHANGED <<otherTor, mux>>
    /\  t' = [t EXCEPT !.linkState = "LinkDown"]

FailMux ==
    (******************************************************************)
    (* Failure Action for inconsistent MUX States with MuxCable State *)
    (******************************************************************)
    /\  UNCHANGED <<torA, torB>>
    /\  mux' \in [ active: T, next: T, serving: {"-"} ]



----------------------------------------------------------------------------
(******************)
(* Reboot Actions *)
(******************)

RebootXCVRD(t, otherTor) == 
    /\  t.xcvrd = "crashed"
    /\  t' = [ t EXCEPT !.xcvrd = "-"]
    /\  UNCHANGED <<mux, otherTor>>
-----------------------------------------------------------------------------


Environment ==
    \/  FailMux
    \/  TimeoutHeartbeat(torA, torB)
    \/  TimeoutHeartbeat(torB, torA)
    \/  FailHeartbeat
    \/  FailTor(torA, torB)
    \/  FailTor(torB, torA)
    \/  CrashXCVRD(torA, torB)
    \/  CrashXCVRD(torB, torA)
    \/  FailLinkState(torA, torB)
    \/  FailLinkState(torB, torA)
    \/  RebootXCVRD(torA, torB)
    \/  RebootXCVRD(torB, torA)


Fairness ==
    /\  WF_vars(System)
    /\  WF_vars(MuxCommands)
    /\  SF_vars(EXEC_SWITCH)
    /\  SF_vars(NACK(torA, torB))
    /\  SF_vars(NACK(torB, torA))
    /\  SF_vars(SendHeartbeat(torA, torB))
    /\  SF_vars(SendHeartbeat(torB, torA))
    /\  WF_vars(LinkState(torA, torB))
    /\  WF_vars(LinkState(torB, torA))
    /\  WF_vars(MuxState(torA, torB))
    /\  WF_vars(MuxState(torB, torA))
    /\  WF_vars(ReadHeartbeat(torA, torB))
    /\  WF_vars(ReadHeartbeat(torB, torA))


WithoutFailureSpec ==
    Init /\  [][System]_vars /\  Fairness

Next == 
    \/  Environment
    \/  System

Spec ==
    Init /\  [][Next]_vars /\  Fairness

-----------------------------------------------------------------------------

NotForeverBothActive ==
    \* Both tors are never active indefinitely. In other words, there is no behavior
    \* such that both tors are indefinitely active from some point onward.
    ~(<>[](torA \in ActiveTor /\  torB \in ActiveTor))

RepeatedlyOneActive ==
    \* One or more alive tors imply that there repeatedly exists an active tor.
    []<>(AliveToRs # {} => \E t \in AliveToRs: t \in ActiveTor)

THEOREM Spec => 
    /\  NotForeverBothActive
    /\  RepeatedlyOneActive

-----------------------------------------------------------------------------

Alias ==
    [
        torA |-> torA, torB |-> torB, mux |-> mux,
        active |-> { t.name : t \in ActiveToRs },
        standby |-> { t.name : t \in StandbyToRs },
        Timeout_A |-> ENABLED TimeoutHeartbeat(torA, torB),
        Timeout_B |-> ENABLED TimeoutHeartbeat(torB, torA)
    ]
=============================================================================