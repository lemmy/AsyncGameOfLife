------------------------ MODULE AsyncGameOfLifeAnim ------------------------
EXTENDS SVG

CONSTANT G

\*CellColor(cell) == 
\*  CASE cell[1] = TRUE /\ cell[2] = TRUE  -> "lightblue"
\*    [] cell[1] = TRUE /\ cell[2] = FALSE -> "lightgray"
\*    [] cell[1] =FALSE /\ cell[2] = TRUE  -> "yellow"
\*    [] cell[1] =FALSE /\ cell[2] = FALSE -> "lightyellow"

CellColor(cell) == 
  CASE cell[1] = TRUE /\ cell[2] =TRUE -> "blue"                      \* Alive cell for r \in {0,1}
    [] cell[1] = TRUE /\ cell[2] =FALSE -> "lightblue"                \* Alive cell for r \in {0}
    [] cell[1] =FALSE /\ cell[2] =TRUE -> "yellow"                    \* Alive cell for r \in {1}
    [] cell[1] =FALSE /\ cell[2] =FALSE /\cell[3] = 0 -> "lightgray"  \* Dead cell for r = 0
    [] cell[1] =FALSE /\ cell[2] =FALSE /\cell[3] = 1  -> "gray"      \* Dead cell for r = 1
    [] cell[1] =FALSE /\ cell[2] =FALSE /\cell[3] = 2 -> "darkgray"   \* Dead cell for r = 2

\* Gap between cells.
AnimPos == [ x |-> 4, y |-> 4 ]

\* Dimensions of a single rectangle.
GAnimPos == [w |-> 40, h |-> 40]

\* Grid
Grid ==
   SetToSeq(
     { Group(<<
         Rect(coordinate[1] * (GAnimPos.w + AnimPos.x), 
              coordinate[2] * (GAnimPos.h + AnimPos.y), 
              GAnimPos.w, 
              GAnimPos.h, 
              [fill |-> CellColor(G[coordinate]) ]),
         Text(coordinate[1] * (GAnimPos.w + AnimPos.x),
              coordinate[2] * (GAnimPos.h + AnimPos.y),
              ToString(G[coordinate][3]), [font |-> "Arial"])>>, <<>>) : 
                          coordinate \in DOMAIN G })

\* Grid converted to SVG.
Animation == SVGElemToString(Group(Grid, <<>>))

Alias == 
  "anim" :> \* key can be anything (grep's regex below looks for svg start/end tag).
  "<svg viewBox='0 0 300 300'>" \o Animation \o "</svg>"

=============================================================================

```bash
/opt/toolbox/tla2tools.jar \
-simulate num=1 -depth 32001 \
-config AsyncGameOfLifeDistributed.tla AsyncGameOfLifeDistributed.tla \
| awk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > n ".svg" }'


## Render set of svg files as mp4 video (ffmpeg has no support for piping it images yet).
## Replace "mp4" with "gif" to create an animated gif that can be posted on e.g. Twitter.
ffmpeg -y -i %d.svg AsyncGameOfLifeDistributed$(date +%s).mp4 && rm *.svg
```