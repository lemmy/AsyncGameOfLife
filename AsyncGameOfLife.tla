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
      points == {<<v[1] + m[1], v[2] + m[2]>> : m \in moore}
  IN { p \in points : /\ p[1] # 0 /\ p[2] # 0   \* Filter out all neighbors
                      /\ p[1]<= N /\ p[2]<= N } \* that are off the grid.

(* Original local transition function from the second page and 
   GameOfLife.tla. *)
delta(b, liveNbgrs) ==
  \/  (b /\ Cardinality(liveNbgrs) \in {2, 3})
  \/ (~b /\ Cardinality(liveNbgrs) = 3)

qPP(qw, qwP, rw) == 
  CASE rw = 0 -> qw \* w in a state of form (q_w,qP_w,0)
    [] rw = 1 -> qwP \* w in a state of form (q_w,qP_w,1)
    [] OTHER -> FALSE \* Undefined

\* Topology modeled as a 2D grid with Moore neighborhood without
\* "wrap around". We don't model the general case (yet?) where
\* the topology/neighborhood is given by a graph (network of computers).
\* Each cell in the grid is a deterministic finite automaton (DFA).
VARIABLES grid
vars == <<grid>>

TypeOK == 
  (* 1. component of a cell is the cell's (visible) state (alive/dead).      *)
  (* 2. component of a cell is the cell's previous (visible) state.          *)
  (* 3. component of a cell is the cell's temporal state (synchronization).  *)
  (* (see "Temporal Waves" section on page 4 for temporal synchronization)   *)
  grid \in [Pos -> (BOOLEAN \X BOOLEAN \X R)]

Init == 
  grid \in [Pos -> (BOOLEAN \X BOOLEAN \X R)]

\* \A r \in R, nbhr \in SUBSET Pos: ready(r, nbhr) \in BOOLEAN
ready(r, Neighbors) == 
  \A w \in Neighbors: grid[w][3] # (r + 2) % 3 \* (0 :> 2 @@ 1 :> 0 @@ 2 :> 1)

(* Transition function from third page. *)
deltaP(v, q, qP, r, Neighbors) ==
  \/ /\ r = 0
     /\ ready(0, Neighbors)   \* \A w \in Neighbors: grid[w][3] \in {0,1}
     /\ grid' = [ grid EXCEPT ![v] = <<delta(q, 
                  (* If w is temporarily in sync with v, compute delta from w's current state.  *)
                  (* If w is one time unit ahead of v, compute delta with w's previous state.   *)
                  {w \in Neighbors: qPP(grid[w][1], grid[w][2], grid[w][3])}),
                  (* Remember v's previous state and advance its temporal synchronization. *)
                  q, 1>> ] \* 1 = (0 + 1) % 3
  (* v could update its visible state (r = 0) but some of its neighbors are at out of sync (r = 2). *)
\*  \/ /\ r = 0
\*     /\ ~ ready(0, Neighbors) \* \E w \in Neighbors: grid[w][3] = 2
\*     /\ UNCHANGED grid
  (* v is not allowed to change visible state but its neighbors are in sync. *)
  \/ /\ r \in {1,2}
     /\ ready(r, Neighbors)
     (* Advance v's temporal state. *)
     /\ grid' = [ grid EXCEPT ![v] = <<q, qP, (r + 1) % 3>> ] \* (0 :> 1 @@ 1 :> 2 @@ 2 :> 0)
  (* v cannot change visible state and neighhood is out of sync. *)
\*  \/ /\ r \in {1,2}
\*     /\ ~ ready(r, Neighbors)
\*     /\ UNCHANGED grid

Next ==
  \E v \in Pos: /\ deltaP(v, grid[v][1], grid[v][2], grid[v][3], nbhd(v))

Spec == Init /\ [][Next]_vars

-------------------------------------------------------

\* TLC evaluates this eagerly at start as part of constant processing to
\* prevent races in value instances during model-checking.
\*SomeConfiguration ==
\*  CHOOSE init \in [Pos -> ({TRUE} \X {FALSE} \X R)] : TRUE


BlinkerN3 ==
    3 
  
BlinkerInitN3 == 
    grid = [ pos \in Pos |-> IF pos \in {<<1,2>>,<<2,2>>,<<3,2>>}
                       THEN <<TRUE, TRUE, 0>>
                       ELSE <<FALSE, FALSE, 0>> ]

====
BlinkerSpecN3 ==
    /\ grid = [ pos \in Pos |-> IF pos \in {<<1,2>>,<<2,2>>,<<3,2>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
    \* /\ Network!Init
    \* /\ msgs = [ pos \in Pos |-> {[ src |-> v, state |-> <<grid[v][1], grid[v][2], grid[v][3]>> ] : v \in nbhd(pos)} ]
  /\ [][Next]_vars

BlinkerN5 ==
    5

BlinkerSpecN5 ==
  /\ grid = [ pos \in Pos |-> IF pos \in {<<3,2>>,<<3,3>>,<<3,4>>}
                   THEN <<TRUE, TRUE, 0>>
                   ELSE <<FALSE, FALSE, 0>> ]
  /\ [][Next]_vars

\* In an ordinay Cellular Automata it would be easy to formulate
\* an invariant for oscillators (list of valid grid states). With
\* the asynchronous CA the state changes in "waves", which makes it
\* tedious to enumerate all valid grid states).  This is why the
\* invariant below is not as strong as it should be (it only 
\* checks quiescent cells but ignores cells that oscillate.
BlinkerInvN5 == 
  \/ /\ \A pos \in Pos \ 
                    {<<3,2>>,<<3,3>>,<<3,4>>,  \* horizontal
                     <<2,3>>,<<3,3>>,<<4,3>>}: \* vertical
          /\ grid[pos][1] = FALSE
          /\ grid[pos][2] = FALSE
          /\ grid[pos][3] \in R
