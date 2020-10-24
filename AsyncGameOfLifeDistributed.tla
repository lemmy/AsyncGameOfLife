\** msgs is defined for all pos \in Pos in the initial state.  What we want
\*  is to let a pos send messages depending on its state.
\*  
\** How to visualize the global state in a distributed *execution*? 
\*
\** Variables grid, msgs, ... model the *global* state of the computation
\*  and we are either clever and map this implicitly to a node's local state,
\*  or we re-write the high-level spec to better encapsulate the local state.
\*
--------------------- MODULE AsyncGameOfLifeDistributed ---------------------
EXTENDS Integers,
        FiniteSets

BOOLS == {TRUE, FALSE} \* PlusPy's parser doesn't know BOOLEAN yet.

\*CONSTANT N \* Size of the *square* grid.
\*ASSUME N \in Nat /\ N > 1
N == 3

null == CHOOSE x : x \notin Nat

(* Temporal state of a node/cell and a message. *)
R == 
  {0,1,2}


(* Set of all positions of the 2D grid of size NxN. *)
Pos ==
  {<<x, y>> : x, y \in 1..N}

(* Set of positions (x,y) for the given position v that are v's
   neighbors as defined by [Moore neighborhood](https://en.wikipedia.org/wiki/Moore_neighborhood) *)
nbhd(v) ==
  LET moore == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<v[1] + m[1], v[2] + m[2]>> : m \in moore}
  IN { p \in points : /\ p[1] # 0 /\ p[2] # 0  
                      /\ p[1]<= N /\ p[2]<= N }

\*CONSTANT P  \* Some initial pattern (blinker, glider, block, ...).
\*ASSUME P \in [Pos -> (BOOLS \X BOOLS \X R)]
P == [ pos \in Pos |-> IF pos \in {<<1,2>>,<<2,2>>,<<3,2>>}
                       THEN <<TRUE, TRUE, 0>>
                       ELSE <<FALSE, FALSE, 0>> ]

-------------------------------------------------------------------------------

(* Each cell (pos) of the grid represents a node in the distributed system. 
   An individual node does *not* have a consistent view of the state of the
   grid.  A node has a local set of messages and a messaging interface. 
   The message interface can be seen as the NIC's buffer, i.e. packets 
   that have been received by the host but not yet delivered to this app. *)
VARIABLES grid, msgs, mi
vars == <<grid, msgs, mi>>

\* Network related (type of messages, payload, ...).
Message == [ src: Pos, state: (BOOLS \X BOOLS \X R) ]
Network == INSTANCE Messaging WITH Processes <- Pos

-------------------------------------------------------------------------------

TypeOK ==
  (* 1. component of a cell is the cell's (visible) state (alive/dead).      *)
  (* 2. component of a cell is the cell's previous (visible) state.          *)
  (* 3. component of a cell is the cell's temporal state (synchronization).  *)
  (* (see "Temporal Waves" section on page 4 for temporal synchronization)   *)
  /\ grid \in [Pos -> (BOOLS \X BOOLS \X R)]
  (* Each node has one inbox for each of its neighbors and the message in    *)
  (* the inbox is the last known state of that neighbor or null.             *)
  /\ \A pos \in Pos : 
              /\ DOMAIN msgs[pos] = nbhd(pos)
              /\ \A n \in nbhd(pos):
                   msgs[pos][n] \in ((BOOLS \X BOOLS \X R) \cup {null})
  \* Variable "mi" is not ours but the Network's responsibility.

-------------------------------------------------------------------------------

Init ==
    /\ grid = P
    \* Non-deterministically initialize grid from the set of *all* initial states,
    \* re-define in your model for a particular configuration,i.e. Blinker, ...!
\*    /\ grid \in [ Pos -> (BOOLS \X BOOLS \X R) ]
    /\ msgs = [ pos \in Pos |->
                    [ v \in nbhd(pos) |-> <<grid[v][1], grid[v][2], grid[v][3]>> ] ]
    \* The network underlying the nodes with reliable message delivery guarantees.
    /\ Network!Init

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
      \* from a faulty node that's not in its neighborhood.
      /\ m.src \notin nbhd(p)
      /\ UNCHANGED <<msgs, grid>>  

-------------------------------------------------------------------------------

ready(r, Messages) ==
  /\ \A w \in DOMAIN Messages: IF Messages[w] = null
                               THEN FALSE 
                               ELSE Messages[w][3] # (r + 2) % 3 \* (0 :> 2 @@ 1 :> 0 @@ 2 :> 1)

delta(b, liveNbgrs) ==
  \* This node/cell is alive and 2 to 3 neighbors are alive.
  \/  (b /\ Cardinality(liveNbgrs) \in {2, 3})
  \* This node/cell is dead but 3 neighbors are alive.
  \/ (~b /\ Cardinality(liveNbgrs) = 3)

qPP(qw, qwP, rw) == 
  CASE rw = 0 -> qw
    [] rw = 1 -> qwP

-------------------------------------------------------------------------------

CONSTANT O \* Others, the set of remote nodes. Define to be {} to run model locally.
ASSUME O \subseteq Pos

Next == 
  /\ \E v \in (Pos \ O): 
                  \/ 
\*                  IF \* Breaking non-determinism with IF-THEN-ELSE at the spec-level fails because 
                       \* TLC evaluates the conditional of ITE not in the scope where it can generate
                       \* states, i.e. just constant and state-level expression (unless the successor
                       \* state is already fully defined).
                      LET q  == grid[v][1]
                          qP == grid[v][2]
                          r  == grid[v][3]
                      IN \* A node is ready iff it has a consistent view of its neighborhood nodes/cells.
                         \* In other words, the set of messages received by the node from its neighborhood
                         \* nodes, allows the node to determine its next state.
                         /\ ready(r, msgs[v])
                            \* Change node's visible state.
                         /\ \/ /\ r = 0
                               /\ grid' = [ grid EXCEPT ![v] = <<delta(q, 
                                    {m \in DOMAIN msgs[v]: qPP(msgs[v][m][1], msgs[v][m][2], msgs[v][m][3])}),
                                      q, 1>> ]    
                            \* Advance node's hidden/temporal state.        
                            \/ /\ r \in {1,2}
                               /\ grid' = [ grid EXCEPT ![v] = <<q, qP, (r + 1) % 3>> ] \* (0 :> 1 @@ 1 :> 2 @@ 2 :> 0)
                         \* Consume messages from node's inboxes by emptying (null) all of its inboxes.
                         /\ msgs' = [ pos \in Pos |-> 
                                       IF pos = v
                                       THEN [ n \in DOMAIN msgs[v] |-> null ]
                                       ELSE msgs[pos] ]
                         \* Broadcast/multicast/unicast state of this node to its neighbors.
                         /\ Network!Send(
                                {<<w, [ src |-> v, state |-> <<grid[v][1]', grid[v][2]', grid[v][3]'>> ]>> : w \in nbhd(v) })
\*                   THEN TRUE ELSE Network!Receive(v, Deliver)
                   \* Receive packets from the NIC and deliver a high-level message to a node's inbox.
                   \/ Network!Receive(v, Deliver)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

(* Distributed/Message-passing AsyncGameOfLife refines AsyncGameOfLife. *)
Agol == INSTANCE AsyncGameOfLife
AgolSpec == Agol!Spec

THEOREM Spec => AgolSpec

-------------------------------------------------------------------------------

(* Cannot use instantiation in a model's Alias expression, because the Toolbox
   does not copy the instantiated module to the model directory.  Otherwise,
   the following would be defined as an alias in the model:
      LET Anim == INSTANCE AsyncGameOfLifeAnim WITH G <- grid
      IN Anim!Alias                                                            *)
\*Anim == INSTANCE AsyncGameOfLifeAnim WITH G <- grid

=============================================================================
