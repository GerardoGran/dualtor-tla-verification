# dualtor-tla-verification

This is the repository for the TLA+ Specification for the DualTor Standby/Active Protocol in use in SONiC Top-of-Rack switches (ToR). The purpose of the specification is to verify the correctness of the proposed solution by modeling the entire system with its possible actions and failures to ensure that the system will stabilize itself and do the required task.

# The DualTor Standby/Active Protocol
The purpose of the DualTor Standby/Active protocol is to increase reliability in top-of-rack switches by introducing redundancy in the form of a second ToR. In the proposed design, one ToR will be designated as "Active" and the other must be "Standby". This "Active" or "Standby" state is defined by a combination of [other states](#the-submodules) that will be explained later. The Active ToR will operate normally, forwarding southbound (T1 to Server) and northbound (Server to T1) traffic. The Standby ToR will tunnel all southbound traffic to its peer ToR and drop all northbound traffic (except for ICMP packets it requires for the [LinkProber Module](#linkprober-module)).
Both ToRs are connected to the server with a Y-split MUX cable. The MUX cable is a powered by the server, can only listen to southbound traffic in one direction, and has a microcontroller unit (MCU) that controls the direction the MUX is listening to. The MUX will duplicate all northbound traffic to both ToR's regardless of which way the MUX is pointing.

![Basic Architecture Diagram](figures/Dualtor%20Animation.gif)

ToR's are connected by a MUX cable to every server in the rack, and each of these connections runs its own instance of the protocol independent from each other. Since the instances are independent, in the specification we only model the connection of two ToR's to a single server.

## The Submodules
The modules in charge of coordinating state transitions and requesting changes in MUX direction are [LinkManager](#the-linkmanager-module) and its submodules: [LinkState](#linkstate-module), [LinkProber](#linkprober-module), and [MuxState](#muxstate-module). There is an instance of LinkManager in every connection from a ToR to a Server. The submodules will each listen to different events and will write their current state to a local redis DB table. Whenever there is a change in states, LinkManager will evaluate the combination of states and decide what it must do.

### **LinkProber Module**
LinkProber is the way a ToR can know if it **should** be Active or Standby. LinkProber periodically pings the server with an ICMP packet with information on the ToR who sent it and optionally a command to be executed by the receiving ToR (see [XCVRD CRASH](#xcvrd-crash)). We call these pings *heartbeats*. Since the MUX will drop all traffic from the ToR it is not pointing to, the only heartbeats that will reach the server and be replied come from the ToR that is Active from the MUX's perspective. Then, the reply reaches the MUX and is split to both ToR's where LinkProber will look at the heartbeat and who sent it. This way LinkProber is periodically informed of the direction of the MUX.
It uses this comparison to determine its distinct states:
- **LinkProberActive**: ICMP_SELF, the received *hearbeat* came from this same ToR. This means this ToR must be the Active ToR.
- **LinkProberStandby**: ICMP_PEER, the received *hearbeat* **did not** come from this same ToR. This means this ToR must be the Standby ToR.
- **LinkProberUnknown**: ICMP_UNKNOWN, No *heartbeat* was received after the timeout limit n times (3 in example). This means something went wrong and could trigger a LINKMANAGER_SWITCH action in [LinkManager](#the-linkmanager-module) to switch ToR operation mode.
- **LinkProberWait**: Initial State and Intermediary state after a LINKMANAGER_SWITCH action or ICMP_UNKNOWN (<2 times).

Something important to note is that LinkProber sends and listens to heartbeats **separately**. This means that a LinkProberUnknown state transition happens after a set timeout limit, not a timeout on the original ICMP packet response.

![LinkProber State Machine](figures/LinkProber%20State%20Diagram.jpg)

### **LinkState Module**
LinkState's job is to listen to the state of the connection from the ToR to the Server. LinkState has two possible states: LinkUp and LinkDown, indicating a healthy and unhealthy connection to the Server respectively.
If LinkState is LinkDown, this means no ICMP packets can be sent or received and will affect all network traffic including LinkProber's heartbeats

### **MuxState Module**
MuxState is the way a ToR can know which ToR the MUX is pointing to. MuxState will query the MUX using a daemon in the ToR called XCVRD. XCVRD can also request a switch in the direction of the MUX to point to itself or its peer ToR depending on the decision table in [LinkManager](#the-linkmanager-module). The states in MuxState are given by the responses XCVRD gets after receiving acknowledgement to a CHECK or a SWITCH request:
- **MuxStateActive**: MUX_XCVRD_ACTIVE, XCVRD daemon returned active indicating that the MUX cable is pointing to this ToR. This ToR must be the Active ToR.
- **MuxStateStandby**: MUX_XCVRD_STANDBY or MUX_XCVRD_FAIL, XCVRD daemon returned standby indicating that the MUX cable is **not** pointing to this ToR. This ToR must be the Standby ToR. Alternatively, XCVRD crashed and ToR must be Standby to make peer ToR become Active eventually.
- **MuxStateWait**: LINKMANAGER_CHECK or LINKMANAGER_SWITCH, Intermediate state. Sent request via XCVRD, waits response.
- **MuxStateUnknown**: MUX_XCVRD_UNKNOWN, Received NACK or request timed out. Could be because MUX is busy with other ToR or Server crashed and MUX lost power.

**Important things to note**
From the MUX point of view, these calls are blocking calls which means the MUX can only serve one ToR at a time and will reply with a NACK to the other ToR.
When a LINKMANAGER_SWITCH is acknowledged, XCVRD will assume it is successful and will return the expected new state even before MUX has switched directions.

![LinkProber State Machine](figures/MUX%20State%20Diagram.jpg)
## The LinkManager Module
All of the modules report their states to a redids DB. LinkManager reads that DB and takes decisions according to the combination of all states. It will evaluate actions to take whenever any of the submodule changes state.

![LinkManager Decision table when LinkUp](figures/LinkManager%20LinkUp.jpeg)
![LinkManager Decision table when LinkDown](figures/LinkManager%20LinkDown.jpeg)

LinkManager will trigger two types of events, LINKMANAGER_CHECK and LINKMANAGER_SWITCH.
**LINKMANAGER_CHECK** will trigger when there is an inconsistency between the LinkProber and the MuxState. This will use XCVRD to request the current direction of the MUX and transition MuxState into MuxWait until XCVRD receives a response, crashes, or timesout.
**LINKMANAGER_SWITCH** will ask to become Standby when MuxState is Active and Link goes down, and it will ask to become Active when MuxState is Standby and LinkProber is Unknown. XCVRD will tell the MUX to change to a target ToR which could be self or peer and transition MuxState into MuxWait. When XCVRD receives a response, this does not mean that the switch has been executed in the MUX, only that it **will** be executed.

# Why do Formal Verification?

When you have a protocol based on a distributed concurrent system with multiple state combinations, thinking of possible edge cases and failure scenarios becomes too complex for one to do without a tool's assistance. **TLA+** allows us to model the entire system without worrying about implementation details to verify the correctness of the underlying algorithm's design or in our case, find new undiscovered ways in which the system could fail.

In TLA+ we do this by writing a *specification*, a written description of what a system is **supposed** to do. This is done by modeling the system's possible actions using mathematics to define actions that a system can take. These actions will define all possible behaviors in the system where a behavior is a sequence of states. For detailed information on TLA+ and resources see [Leslie Lamport's Website](http://lamport.azurewebsites.net/tla/tla.html) and his book [Specifying Systems](http://lamport.azurewebsites.net/tla/book-21-07-04.pdf).