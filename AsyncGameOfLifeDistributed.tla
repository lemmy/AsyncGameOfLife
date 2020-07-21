--------------------- MODULE AsyncGameOfLifeDistributed ---------------------
EXTENDS Integers,
        FiniteSets

CONSTANT N
ASSUME N \in Nat /\ N > 1

R == 
  {0,1,2}

Pos ==
  {<<x, y>> : x, y \in 1..N}

nbhd(v) ==
  LET moore == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<v[1] + x, v[2] + y>> : <<x, y>> \in moore}
  IN { p \in points : /\ p[1] # 0 /\ p[2] # 0  
                      /\ p[1]<= N /\ p[2]<= N }

delta(b, liveNbgrs) ==
  IF \/  (b /\ Cardinality(liveNbgrs) \in {2, 3})
     \/ (~b /\ Cardinality(liveNbgrs) = 3)
  THEN TRUE
  ELSE FALSE

qPP(qw, qwP, rw) == 
  CASE rw = 0 -> qw
    [] rw = 1 -> qwP

VARIABLES grid, msgs, mi, seqs
vars == <<grid, msgs, mi, seqs>>

\* Network related (type of messages, payload, ...).
Rnd == 1..4 \*Nat
Vote == [ round: Rnd, state: (BOOLEAN \X BOOLEAN \X R) ]
Message == [ src: Pos, vote: Vote ]
Network == INSTANCE Messaging WITH Processes <- Pos

Init == 
    /\ grid = [ pos \in Pos |-> IF pos \in {<<3,2>>,<<3,3>>,<<3,4>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
\*    /\ grid = [ pos \in Pos |-> (BOOLEAN \X BOOLEAN \X R) ]
    \* This is a node's in-process message set
    /\ seqs  = [ pos \in Pos |-> 0 ]
    /\ msgs  = [ pos \in Pos |-> {[ src |-> v, 
                                        vote |-> 
                                          [ round |-> seqs[v], 
                                            state |-> <<grid[v][1], grid[v][2], grid[v][3]>> ] ] : v \in nbhd(pos)} ]
    \* The network underlying the nodes. We expect it to
    \* not lose messages.
    /\ Network!Init

ready(r, ballots) ==
  \A b \in ballots: b.vote.state[3] # (r + 2) % 3 \* (0 :> 2 @@ 1 :> 0 @@ 2 :> 1)

VisibleAndTemporal(v, q, qP, r, ballots) ==
     /\ r = 0
     /\ ready(0, ballots)
     /\ grid' = [ grid EXCEPT ![v] = <<delta(q, 
                  {b \in ballots: qPP(b.vote.state[1], b.vote.state[2], b.vote.state[3])}),
                  q, 1>> ]

IncrementTemporal(v, q, qP, r, ballots) ==
     /\ r \in {1,2}
     /\ ready(r, ballots)
     /\ grid' = [ grid EXCEPT ![v] = <<q, qP, (r + 1) % 3>> ] \* (0 :> 1 @@ 1 :> 2 @@ 2 :> 0)

Deliver(p, m) ==
    /\ msgs' = [ msgs EXCEPT ![p] = @ \union { m } ]
    /\ UNCHANGED <<grid, seqs>>

Next ==
  /\ \E v \in Pos: \/ LET ballots == { m \in msgs[v] : m.vote.round = seqs[v] } \* Filter the messages for the current sequence number. It assumes a node only receives messages from its neighbors. 
                          Neighbors == nbhd(v)
                      IN /\ Cardinality(ballots) = Cardinality(Neighbors)
                         /\ \/ /\ IncrementTemporal(v, grid[v][1], grid[v][2], grid[v][3], ballots)
                               /\ UNCHANGED msgs
                            \/ /\ VisibleAndTemporal(v, grid[v][1], grid[v][2], grid[v][3], ballots)
                               \* Consume ballots for this seq nr.
                               /\ msgs' = [ msgs EXCEPT ![v] = @ \ ballots ]
                         /\ seqs' = [ seqs EXCEPT ![v] = @ + 1 ]
                         /\ Network!Send(
                                {<<w, [ src |-> v, 
                                        vote |-> 
                                          [ round |-> seqs[v]', 
                                            state |-> <<grid[v][1]', grid[v][2]', grid[v][3]'>> ] ]>> : w \in Neighbors })
                   \/ Network!Receive(v, Deliver)

Spec == Init /\ [][Next]_vars

Agol == INSTANCE AsyncGameOfLife

ImplementsAgol == Spec => Agol!Spec
===========================================================================

