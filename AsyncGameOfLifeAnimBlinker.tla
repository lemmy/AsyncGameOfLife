------------------------ CONFIG AsyncGameOfLifeAnimBlinker --------------------
CONSTANT
N <- BlinkerN3
null = "null"
SPECIFICATION BlinkerSpecN3
INVARIANT Inv
\* PROPERTIES AgolSpec
ALIAS Alias
=============================================================================

\* Oscillators
\* https://en.wikipedia.org/wiki/File:Game_of_life_blinker.gif
------------------------ MODULE AsyncGameOfLifeAnimBlinker --------------------
EXTENDS AsyncGameOfLife

BlinkerN3 ==
    3 

BlinkerN5 ==
    5
  
BlinkerSpecN3 ==
    /\ grid = [ pos \in Pos |-> IF pos \in {<<1,2>>,<<2,2>>,<<3,2>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
    \* /\ Network!Init
    \* /\ msgs = [ pos \in Pos |-> {[ src |-> v, state |-> <<grid[v][1], grid[v][2], grid[v][3]>> ] : v \in nbhd(pos)} ]
  /\ [][Next]_vars

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

\*Inv ==
\*   TLCGet("level") < 20000

\* https://github.com/tlaplus/tlaplus/issues/485
\*INSTANCE AsyncGameOfLifeAnim
\*Alias == 
\*  "anim" :> \* key can be anything (grep's regex below looks for svg start/end tag).
\*  "<svg viewBox='0 0 300 300'>" \o SVGElemToString(Group(Grid, <<>>)) \o "</svg>"

=============================================================================

```bash
/opt/toolbox/tla2tools.jar \
-simulate num=1 -depth 32001 \
-config AsyncGameOfLifeAnimBlinker.tla AsyncGameOfLifeAnimBlinker.tla \
| awk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > n ".svg" }'

## Render set of svg files as mp4 video (ffmpeg has no support for piping it images yet).
## Replace "mp4" with "gif" to create an animated gif that can be posted on e.g. Twitter.
ffmpeg -y -i %d.svg AsyncGameOfLifeAnimBlinker_$(date +%s).mp4 && rm *.svg

## Show generated animation.
vlc AsyncGameOfLifeAnimBlinker_*.mp4
```



## Convert mp4 to gif so that it can be posted on twitter.
#ffmpeg -ss 30 -t 3 -i input.mp4 -vf "fps=10,scale=320:-1:flags=lanczos,split[s0][s1];[s0]palettegen[p];[s1][p]paletteuse" -loop 0 output.gif
