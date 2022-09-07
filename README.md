# gemini-tla-verification

This is the repository for the TLA+ Specification for the Gemini Protocol in use in SONiC Top-of-Rack switches (ToR). The specifics of the implementation of the protocol are not essential for verifying the correctness of the algorithm and finding failure conditions in the logic for it. As such, some details may be ommitted.

# The Gemini Protocol
The Gemini Protocol implements a dual-ToR solution on a given rack, ensuring reliability in case one presents a failure. In it one ToR is designated as "Active" and the other must be "Standby". The Active ToR will operate normally, forwarding southbound and northbound traffic. The Standby ToR will tunnel all southbound traffic to the Active ToR and drop all northbound traffic (except for ICMP packets it requires for the [LinkProber Module](#linkprober-module)).
Both ToRs are connected to the server with a Y-split MUX cable. The MUX cable can only accept the southbound (T0 to server) traffic from one direction and drop traffic from the other direction. However, the MUX cable will duplicate northbound (server to T0) traffic and send it on both directions. The standby ToR has ACL rules to drop redundant northbound traffic.

![Basic Architecture Diagram](figures/Gemini%20Architecture%20Gif.gif)

Each ToR is running its own instance of the protocol which is divided into different submodules. These submodules listen to different inputs to determine their state and report it to the main module LinkManager. This way each ToR knows if it should be in Active or Standby operation mode.
## The Submodules
### **LinkState Module**
LinkState has two possible states: {LinkUp, LinkDown}. This module listens periodically to a redis DB reporting the ToR's connection to T1 (where traffic is being received from).
### **LinkProber Module**
LinkProber is in charge of sending signs of health with ICMP packets encoded with the ToR's MAC address or name. We call these packets *heartbeats*. Separately, LinkProber is listening to any incoming *heartbeats* and compares the encoded MAC address or name with its own. It uses this comparison to determine its three distinct states:
- **LinkProberActive**: ICMP_SELF, the received *hearbeat* has the ToR's own MAC address or name. This means this ToR must be the Active ToR.
- **LinkProberStandby**: ICMP_PEER, the received *hearbeat* **does not** have the ToR's own MAC address or name. This means this ToR must be the Standby ToR.
- **LinkProberUnknown**: ICMP_NONE, No *heartbeat* was received after the timeout limit. This means something went wrong and could trigger a LINKMANAGER_SWITCH event in [LinkManager](#the-linkmanager-module) to switch ToR operation mode.

![LinkProber State Machine](figures/LinkProber%20State%20Diagram.jpg)
### **MuxState Module**
MuxState listens to LinkManager and queries information from the MUX cable with a daemon hosted in the ToR called XCVRD. It has two intermediate states and the active and standby state indicating wether the MUX cable is pointing to this ToR. the states in detail:
- **MuxStateActive**: MUX_XCVRD_ACTIVE, XCVRD daemon returned active indicating that the MUX cable is pointing to this ToR. This ToR must be the Active ToR.
- **MuxStateStandby**: MUX_XCVRD_STANDBY, XCVRD daemon returned standby indicating that the MUX cable is **not** pointing to this ToR. This ToR must be the Standby ToR.
- **MuxStateMuxwait**: LINKMANAGER_CHECK, Intermediate state. Serves as initial state meaning that it must check cable state with XCVRD.
- **MuxStateLinkWait**: LINKMANAGER_SWITCH or LINKMANAGER_CHECK (when LinkProber Unknown), Intermediate state. Won't wo into MuxStateMuxWait until LinkProber is Active or Standby.

![LinkProber State Machine](figures/MUX%20State%20Diagram.png)
## The LinkManager Module
All of the other modules report their states to a local db. LinkManager reads that DB and takes decisions according to the combination of all states. 

![LinkManager Decision table when LinkUp](figures/LinkManager%20LinkUp.jpeg)
![LinkManager Decision table when LinkDown](figures/LinkManager%20LinkDown.jpeg)

LinkManager will trigger two types of events, LINKMANAGER_CHECK and LINKMANAGER_SWITCH.
**LINKMANAGER_CHECK** will trigger when there is an inconsistency between the LinkProber and the MuxState. This will make MuxState change into its intermediary states while it cascades to a point where it can try to go Active or query the MUX with XCVRD.
**LINKMANAGER_SWITCH** makes the MuxState go into intermediate states and asks to change from active to standby or vice versa.
