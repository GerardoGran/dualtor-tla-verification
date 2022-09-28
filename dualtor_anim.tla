---- MODULE dualtor_anim ----
EXTENDS TLC, TLCExt, SVG, IOUtils, Sequences, Integers, dualtor

Arial == [font |-> "Arial"]

LegendBasePos == [ x |-> -5, y |-> 45 ]

RingBasePos == [w |-> 55, h |-> 55, r |-> 75]

\* 12pts (x/y) offset to be concentric with RingNetwork.
TokenBasePos == [ w |-> RingBasePos.w + 12, 
                  h |-> RingBasePos.h + 12,
                  r |-> RingBasePos.r + 25 ]

NodeDimension == 100

\* Centers the line/circle at the center of a node instead of
\* a node's left upper corner (which are its 0:0 coordinates).
ArrowPosOffset == NodeDimension \div 2

Labels == Group(<<Text(LegendBasePos.x, LegendBasePos.y, "Circle: Active, Arrow: Mux active", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 20, "Red line: Ping, Orange line: Pong", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 40, "Dashed: LinkDown, Solid: LinkUp", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 60, "Level: " \o ToString(TLCGet("level")), Arial)>>,
                  <<>>)

ToRs ==
    LET ToRR(t, offset) ==         
            LET coord == [x |-> offset * 100, y |-> 100]
                id == Text(coord.x + ArrowPosOffset + 2, coord.y + ArrowPosOffset + 7, ToString(t.name), 
                                                Arial @@ [fill |-> "black"])
                muxState == Text(coord.x + ArrowPosOffset - 20, coord.y + ArrowPosOffset + 20, "MS: " \o ToString(t.muxState), 
                                                Arial @@ [fill |-> "black"])
                linkProber == Text(coord.x + ArrowPosOffset - 20, coord.y + ArrowPosOffset + 33, "LP: " \o ToString(t.linkProber), 
                                                Arial @@ [fill |-> "black"])
                node == Rect(coord.x + 15, coord.y, NodeDimension, NodeDimension,
                                            \* round (rx=15) if node is active.
                                            [rx |-> IF t \in ActiveTor THEN "30" ELSE "0",
                                            stroke |-> "black",
                                            fill |-> "white"])
            IN Group(<<node, id, muxState, linkProber>>, ("transform" :> "translate(0 125)"))
    IN Group(<<ToRR(torA, 1), ToRR(torB, 4)>>, <<>>)

Mux ==
    LET coord == [x |-> 250, y |-> 300]
        id == Text(coord.x + ArrowPosOffset + 2, coord.y + ArrowPosOffset + 7, "Mux", 
                                                Arial @@ [fill |-> "black"])
        active == Text(coord.x + ArrowPosOffset - 20, coord.y + ArrowPosOffset + 20, "Active: " \o ToString(mux.active), 
                                                Arial @@ [fill |-> "black"])
        next == Text(coord.x + ArrowPosOffset - 20, coord.y + ArrowPosOffset + 33, "Next: " \o ToString(mux.next), 
                                                Arial @@ [fill |-> "black"])
        node == Rect(coord.x + 15, coord.y, NodeDimension, NodeDimension,
                                            \* round (rx=15) if node is active.
                                            [rx |-> "0",
                                            stroke |-> "black",
                                            fill |-> "white"])
    IN Group(<<node, id, active, next>>, ("transform" :> "translate(0 125)"))

Server ==
    LET coord == [x |-> 250, y |-> 500]
        id == Text(coord.x + ArrowPosOffset + 2, coord.y + ArrowPosOffset + 7, "Srv", 
                                                Arial @@ [fill |-> "black"])
        node == Rect(coord.x + 15, coord.y, NodeDimension, NodeDimension,
                                            \* round (rx=15) if node is active.
                                            [rx |-> "0",
                                            stroke |-> "black",
                                            fill |-> "white"])
    IN Group(<<node, id>>, ("transform" :> "translate(0 125)"))

Past ==
    IF TLCGet("level") > 1 
    THEN Trace[TLCGet("level") - 1]
    ELSE Trace[1]

CableColorA ==
    CASE Past.torA.heartbeatIn # torA.heartbeatIn /\ torA.name \in torA.heartbeatIn -> "red"
      [] Past.torA.linkProber # torA.linkProber -> "orange"
      [] OTHER -> "black"

CableColorB ==
    CASE Past.torB.heartbeatIn # torB.heartbeatIn /\ torB.name \in torB.heartbeatIn-> "red"
      [] Past.torB.linkProber # torB.linkProber -> "orange"
      [] OTHER -> "black"

Cables ==
    LET 
        a2m == Line(265 + ArrowPosOffset, 250 + ArrowPosOffset, 100 + 40 +ArrowPosOffset, 160 + ArrowPosOffset, 
                        [stroke |-> CableColorA, stroke_width |-> IF CableColorA # "black" THEN "3" ELSE "1",
                        stroke_dasharray |-> IF torA.linkState = "LinkUp" THEN "0" ELSE "10"]
                        @@ IF mux.active = torA.name THEN [ marker_end |-> "url(#arrow)"] ELSE <<>>)
        b2m == Line(265 + ArrowPosOffset, 250 + ArrowPosOffset, 400 + ArrowPosOffset, 160 + ArrowPosOffset,
                        [stroke |-> CableColorB, stroke_width |-> IF CableColorB # "black" THEN "3" ELSE "1",
                        stroke_dasharray |-> IF torB.linkState = "LinkUp" THEN "0" ELSE "10"]
                        @@ IF mux.active = torB.name THEN [ marker_end |-> "url(#arrow)"] ELSE <<>>)
        m2s == Line(265 + ArrowPosOffset, 350 + ArrowPosOffset, 
                        265 + ArrowPosOffset, 450 + ArrowPosOffset, 
                        [stroke |-> "black", stroke_dasharray |-> "0"])
    IN Group(<<a2m, b2m, m2s>>, ("transform" :> "translate(0 125)"))


Animation == SVGElemToString(Group(<<Labels, ToRs, Mux, Server, Cables>>, <<>>))

\* This is just the arrow head that's used by the Message definition above as an attribute.
Defs ==
    "<defs><marker id='arrow' markerWidth='35' markerHeight='35' refX='0' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='black' /></marker></defs>"

AnimAlias == Alias @@ [
    \* T |-> Trace,
    \* P |-> Past,
    \* lvl |-> TLCGet("level"),
    \* ccA |-> CableColorA,
    \* ccB |-> CableColorB,
    \* \* toolbox |-> Defs \o Animation,
    \* \* eyeofgnome |-> "<svg viewBox='-80 0 300 300'>" \o Defs \o Animation \o "</svg>",
    toSVG |-> 
        IOExecTemplate(
            \* %%03d to escape %03d in Java format strings.
            <<"bash", "-c", "echo \"%1$s\" > gemini_anim_$(printf %%03d %2$s).svg">>,
                <<"<svg viewBox='-40 15 700 800'>"
                    \o Defs
                    \o Animation
                    \o "</svg>", ToString(TLCGet("level"))>>) 
    ]

====



convert -delay 100 -density 200 *.svg gemini.pdf