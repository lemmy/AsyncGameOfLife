------------------------ MODULE AsyncGameOfLifeAnim ------------------------
EXTENDS SVG, SequencesExt, Toolbox, AsyncGameOfLife

CellColor(cell) == 
  CASE cell[1] = TRUE /\ cell[2] = TRUE  -> "lightblue"
    [] cell[1] = TRUE /\ cell[2] = FALSE -> "lightgray"
    [] cell[1] =FALSE /\ cell[2] = TRUE  -> "yellow"
    [] cell[1] =FALSE /\ cell[2] = FALSE -> "lightyellow"

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
              [fill |-> CellColor(grid[coordinate]) ]),
         Text(coordinate[1] * (GAnimPos.w + AnimPos.x),
              coordinate[2] * (GAnimPos.h + AnimPos.y),
              ToString(grid[coordinate][3]), [font |-> "Arial"])>>, <<>>) : 
                          coordinate \in DOMAIN grid })

\* Grid converted to SVG.
Animation == SVGElemToString(Group(Grid, <<>>))

=============================================================================
