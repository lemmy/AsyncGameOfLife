-------------------------- MODULE AsyncGameOfLife --------------------------
(***********************************************************************)
(* Evolution in Asynchronous Cellular Automata                         *)
(* by Chrystopher L. Nehaniv.                                          *)
(* https://uhra.herts.ac.uk/bitstream/handle/2299/7041/102007.pdf      *)
(***********************************************************************)
EXTENDS Integers, (* Int bc of coordinates relative to the current cell. *)
        FiniteSets

CONSTANT N
ASSUME N \in Nat

R == 
  {0,1,2}

Pos ==
  {<<x, y>> : x, y \in 1..N}

\* The set of neighbors of node/dfa v.
\* \A v \in Pos: nbhd(v) \in SUBSET Pos
nbhd(v) ==
  LET moore == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<v[1] + x, v[2] + y>> : <<x, y>> \in moore}
  IN { p \in points : /\ p[1] # 0 /\ p[2] # 0   \* Filter out all neighbors
                      /\ p[1]<= N /\ p[2]<= N } \* that are off the grid.

\* Topology modeled as a 2D grid with Moore neighborhood without
\* "wrap around". We don't model the general case (yet?) where
\* the topology/neighborhood is given by a graph (network of computers).
\* Each cell in the grid is a deterministic finite automaton (DFA).
VARIABLES grid
vars == <<grid>>

TypeOK == 
  grid \in [Pos -> (BOOLEAN \X BOOLEAN \X R)]

Init == 
  grid \in [Pos -> (BOOLEAN \X BOOLEAN \X R)]

(* Original local transition function from the second page and 
   GameOfLife.tla. *)
delta(b, liveNbgrs) ==
  IF \/  (b /\ Cardinality(liveNbgrs) \in {2, 3})
     \/ (~b /\ Cardinality(liveNbgrs) = 3)
  THEN TRUE
  ELSE FALSE

\* \A r \in R, nbhr \in SUBSET Pos: ready(r, nbhr) \in BOOLEAN
ready(r, Neighbors) == 
  \A w \in Neighbors: grid[w][3] # (r + 2) % 3

qPP(qw, qwP, rw) == 
  CASE rw = 0 -> qw \* w in a state of form (q_w,qP_w,0)
    [] rw = 1 -> qwP \* w in a state of form (q_w,qP_w,1)
\*    [] OTHER -> FALSE \* Undefined

(* Transition function from third page. *)  
deltaP(v, q, qP, r, Neighbors) ==
  \/ /\ r = 0
     /\ ready(0, Neighbors) 
     /\ grid' = [ grid EXCEPT ![v] = <<delta(q, 
                  {w \in Neighbors: qPP(grid[w][1], grid[w][2], grid[w][3])}),
                  q, 1>> ]
  \/ /\ r = 0
     /\ ~ ready(0, Neighbors) 
     /\ grid' = [ grid EXCEPT ![v] = <<q, qP, 0>> ]
  \/ /\ r \in {1,2}
     /\ ready(r, Neighbors)
     /\ grid' = [ grid EXCEPT ![v] = <<q, qP, (r + 1) % 3>> ]
  \/ /\ r \in {1,2}
     /\ ~ ready(r, Neighbors)
     /\ UNCHANGED grid

Next ==
  \E v \in Pos: /\ deltaP(v, grid[v][1], grid[v][2], grid[v][3], nbhd(v))
\*                \* Print current grid to stdout (this become huge). 
\*                /\ LET TLC == INSTANCE TLC
\*                   IN TLC!PrintT(grid)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------

\* TLC evaluates this eagerly at start as part of constant processing to
\* prevent races in value instances during model-checking.
\*SomeConfiguration ==
\*  CHOOSE init \in [Pos -> ({TRUE} \X {FALSE} \X R)] : TRUE

-------------------------------------------------------
\* Tests based on Still lifes

\* https://en.wikipedia.org/wiki/File:Game_of_life_block_with_border.svg
BlockN == 
  4
  
Block ==
   /\ grid = [pos \in Pos |-> IF pos \in {<<2,2>>,<<2,3>>,<<3,2>>,<<3,3>>}
                   THEN <<TRUE, TRUE, 0>>
                   ELSE <<FALSE, FALSE, 0>>]  
  /\ [][Next]_vars
                   
\* r keeps changing, but q doesn't because Block is a still life.
BlockInv ==
  /\ \A pos \in Pos \ {<<2,2>>,<<2,3>>,<<3,2>>,<<3,3>>}:
          /\ grid[pos][1] = FALSE
          /\ grid[pos][2] = FALSE
          /\ grid[pos][3] \in R
  /\ \A pos \in {<<2,2>>,<<2,3>>,<<3,2>>,<<3,3>>}:
          /\ grid[pos][1] = TRUE
          /\ grid[pos][2] = TRUE
          /\ grid[pos][3] \in R

BlockDiameter == 
  31

\* https://en.wikipedia.org/wiki/File:Game_of_life_beehive.svg
Beehive ==
  TRUE
  
\* https://en.wikipedia.org/wiki/File:Game_of_life_loaf.svg
Load ==
  TRUE
    
\* https://en.wikipedia.org/wiki/File:Game_of_life_loaf.svg
Boat ==
  TRUE
  
\* https://en.wikipedia.org/wiki/File:Game_of_life_flower.svg
Flower ==
  TRUE

\* Oscillators

\* https://en.wikipedia.org/wiki/File:Game_of_life_blinker.gif
BlinkerN == 
  5
  
Blinker ==
  /\ grid = [ pos \in Pos |-> IF pos \in {<<3,2>>,<<3,3>>,<<3,4>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
  /\ [][Next]_vars


\* In an ordinay Cellular Automata it would be easy to formulate
\* an invariant for oscillators (list of valid grid states). With
\* the asynchronous CA the state changes in waves, which makes it
\* tedious to enumerate all valid grid states).  This is why the
\* invariant below is not as strong as it should be (it only 
\* checks quiescent cells but ignores cells that oscillate.
BlinkerInv == 
  \/ /\ \A pos \in Pos \ 
                    {<<3,2>>,<<3,3>>,<<3,4>>,  \* horizontal
                     <<2,3>>,<<3,3>>,<<4,3>>}: \* vertical
          /\ grid[pos][1] = FALSE
          /\ grid[pos][2] = FALSE
          /\ grid[pos][3] \in R
  
=============================================================================
\* Modification History
\* Last modified Thu Jun 25 22:06:55 PDT 2020 by markus
\* Created Wed Jun 17 13:56:15 PDT 2020 by markus
