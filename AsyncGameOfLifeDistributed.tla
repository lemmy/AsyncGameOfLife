* msgs is defined for all pos \in Pos in the initial state.  What we want
  is to let a pos send messages depending on its state.
  
* How to visualize the global state in a distributed *execution*? 

* Variables grid, msgs, ... model the *global* state of the computation
  and we are either clever and map this implicitly to a node's local state,
  or we re-write the high-level spec to better encapsulate the local state.

--------------------- MODULE AsyncGameOfLifeDistributed ---------------------
EXTENDS Integers,
        FiniteSets,
        Sequences,
        SequencesExt,
        TLC

CONSTANT N \* Size of the grid
ASSUME N \in Nat /\ N > 1

CONSTANT null

(* Temporal state. *)
R == 
  {0,1,2}


(* Set of all positions of the 2D grid of size NxN. *)
Pos ==
  {<<x, y>> : x, y \in 1..N}

(* Set of positions (x,y) for the given position v that are v's
   neighbors as defined by [Moore neighborhood](https://en.wikipedia.org/wiki/Moore_neighborhood) *)
nbhd(v) ==
  LET moore == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<v[1] + x, v[2] + y>> : <<x, y>> \in moore}
  IN { p \in points : /\ p[1] # 0 /\ p[2] # 0  
                      /\ p[1]<= N /\ p[2]<= N }

-------------------------------------------------------------------------------

delta(b, liveNbgrs) ==
  IF \/  (b /\ Cardinality(liveNbgrs) \in {2, 3})
     \/ (~b /\ Cardinality(liveNbgrs) = 3)
  THEN TRUE
  ELSE FALSE

qPP(qw, qwP, rw) == 
  CASE rw = 0 -> qw
    [] rw = 1 -> qwP

-------------------------------------------------------------------------------

(* Each cell (pos) of the grid represents a node in the distributed system. 
   An individual node does *not* have a consistent view of the state of the
   grid.  A node has a local set of messages and a messaging interface. 
   The message interface can be seen as the NIC's buffer, i.e. packets 
   that have been received by the host but not yet delivered to this app. *)
VARIABLES grid, msgs, mi
vars == <<grid, msgs, mi>>

\* Network related (type of messages, payload, ...).
Message == [ src: Pos, state: (BOOLEAN \X BOOLEAN \X R) ]
Network == INSTANCE Messaging WITH Processes <- Pos

-------------------------------------------------------------------------------

TypeOK ==
  (* 1. component of a cell is the cell's (visible) state (alive/dead).      *)
  (* 2. component of a cell is the cell's previous (visible) state.          *)
  (* 3. component of a cell is the cell's temporal state (synchronization).  *)
  (* (see "Temporal Waves" section on page 4 for temporal synchronization)   *)
  /\ grid \in [Pos -> (BOOLEAN \X BOOLEAN \X R)]
  /\ \A pos \in Pos : DOMAIN msgs[pos] = nbhd(pos) 

-------------------------------------------------------------------------------

Init ==
    \* Non-deterministically initialize grid from the set of *all* initial states, re-define in your model for a particular configuration,i.e. Blinker, ...!
\*    /\ grid \in [ Pos -> (BOOLEAN \X BOOLEAN \X R) ]
    \* Glider
    /\ grid = [ pos \in Pos |-> IF pos \in {<<1,3>>,<<2,1>>,<<2,3>>,<<3,2>>,<<3,3>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
    
    \* Block
\*    /\ grid = [pos \in Pos |-> IF pos \in {<<2,2>>,<<2,3>>,<<3,2>>,<<3,3>>}
\*                   THEN <<TRUE, TRUE, 0>>
\*                   ELSE <<FALSE, FALSE, 0>>]  
      \* Blinker
\*    /\ grid = [ pos \in Pos |-> IF pos \in {<<3,2>>,<<3,3>>,<<3,4>>}
\*                   THEN <<TRUE, TRUE, 0>>
\*                   ELSE <<FALSE, FALSE, 0>> ]
    \* This is a node's in-process message set.
    \* TODO: This definition assumes that we can access the state of the neighboring nodes, which we obviously can't!
    \*       Also, the next-state relation is enabled, iff msgs # [pos \in Pos |-> {}].
    /\ msgs = [ pos \in Pos |->
                    [ v \in nbhd(pos) |-> <<grid[v][1], grid[v][2], grid[v][3]>> ] ]
    \* The network underlying the nodes with reliable message delivery guarantees.
    /\ Network!Init

-------------------------------------------------------------------------------

\*\*{0,1,2} 1 > 2 > 0 \* Is this an invariant because neighbors cannot get ahead of us?
\*\*{0,1}   0
\*\*{1,2}   1
\*\*{2,0}   2
\*ready(r, Neighbors, Messages) ==
\*  \A n \in Neighbors:
\*     \* v received a message for each of its neighbors.
\*     /\ \E m \in Messages: 
\*         m.src = n
\*     \* The message from each neighbor has the correct temporal timestamp.
\*     /\ \A m \in Messages:
\*         m.src = n => m.state[3] # (r + 2) % 3 \* (0 :> 2 @@ 1 :> 0 @@ 2 :> 1)
ready(r, Messages) ==
  /\ \A w \in DOMAIN Messages: IF Messages[w] = null
                               THEN FALSE 
                               ELSE Messages[w][3] # (r + 2) % 3 \* (0 :> 2 @@ 1 :> 0 @@ 2 :> 1)

\*\* The set of messages from v's neighbors with the lowest temporal state.
\*Nbghs(v, Neighbors) ==
\*  \* ready(0, ...) implies that we've already received a message from every neighbor and that those messages are \in {0,1}
\*  { m \in msgs[v]: /\ m.state[3] \in {0,1} \* This conjunct appears to be redundant to ready.
\*                   /\ \A o \in (msgs[v] \ {m}): 
\*                        m.src = o.src => m.state[3] < o.state[3] }

-------------------------------------------------------------------------------

(* Deliver a packet received by the host's NIC to this app (AsyncGameOfLifeDist...). 
   This action is a technical artifact that is orthogonal to modeling 
   the distributed version of AsyncGameOfLife. *)
Deliver(p, m) ==
   \/ /\ m.src \in nbhd(p)
      /\ msgs' = [ msgs EXCEPT ![p][m.src] = m.state ]
      /\ UNCHANGED <<grid>>
   \/ \* This disjunct is never enabled at the spec level, but at the
      \* execution level it is conceivable that a node receives a message
      \* from a faulty non-neighborhood node.
      /\ m.src \notin nbhd(p)
      /\ PrintT(<<"Received msg from non-neighborhood node", p, m>>)
      /\ UNCHANGED <<msgs, grid>>    

VisibleAndTemporal(v, q, qP, r) ==
     /\ r = 0   \* \A state[3] # 2 <=> \A state[3] \in {0,1}
     /\ ready(r, msgs[v])
     /\ grid' = [ grid EXCEPT ![v] = <<delta(q, 
                         {m \in DOMAIN msgs[v]: qPP(msgs[v][m][1], msgs[v][m][2], msgs[v][m][3])}),
                          q, 1>> ]            
           
IncrementTemporal(v, q, qP, r) ==
     /\ \/ r = 1 \* \A state[3] # 0 = \A state[3] \in {1,2}
        \/ r = 2 \* \A state[3] # 1 = \A state[3] \in {0,2}
     /\ ready(r, msgs[v])
     /\ grid' = [ grid EXCEPT ![v] = <<q, qP, (r + 1) % 3>> ] \* (0 :> 1 @@ 1 :> 2 @@ 2 :> 0)

Next == 
  /\ \E v \in Pos: \/ /\ \/ IncrementTemporal(v, grid[v][1], grid[v][2], grid[v][3])
                         \/ VisibleAndTemporal(v, grid[v][1], grid[v][2], grid[v][3])
                      /\ msgs' = [ pos \in Pos |-> 
                                   IF pos = v
                                   THEN [ n \in DOMAIN msgs[v] |-> null ]
                                   ELSE msgs[pos] ]
                   (* Everything related to Network is, again, technical, rather uninteresting technical artifacts. *)
                         \* Broadcast/multicast state of this node to its neighbors.
                      /\ Network!Send(
                                {<<w, [ src |-> v, state |-> <<grid[v][1]', grid[v][2]', grid[v][3]'>> ]>> : w \in nbhd(v) })
                   \/ Network!Receive(v, Deliver)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

Agol == INSTANCE AsyncGameOfLife

\* TLC MC.cfg doesn't like "Algo!Spec"
AgolSpec == Agol!Spec

THEOREM Spec => AgolSpec

-------------------------------------------------------------------------------

Inv == 
    TLCGet("level") < 32001

Anim == INSTANCE AsyncGameOfLifeAnim
\* https://github.com/tlaplus/tlaplus/issues/485
Alias == 
  "anim" :> \* key can be anything (grep's regex below looks for svg start/end tag).
  "<svg viewBox='0 0 300 300'>" \o Anim!SVGElemToString(Anim!Group(Anim!Grid, <<>>)) \o "</svg>"

===========================================================================
------------------------ CONFIG AsyncGameOfLifeDistributed --------------------
CONSTANT
N = 5 \* 4 for block \* 5 for blinker & glider
null = "null"
SPECIFICATION Spec
INVARIANT Inv
ALIAS Alias
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