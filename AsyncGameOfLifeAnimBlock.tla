------------------------ CONFIG AsyncGameOfLifeAnimBlock --------------------
CONSTANT
N <- BlockN
SPECIFICATION Block
INVARIANT Inv
ALIAS Alias
=============================================================================

\* Oscillators
\* https://en.wikipedia.org/wiki/File:Game_of_life_blinker.gif
------------------------ MODULE AsyncGameOfLifeAnimBlock --------------------
EXTENDS AsyncGameOfLifeAnim


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

Inv ==
  TLCGet("level") < 20000

\* https://github.com/tlaplus/tlaplus/issues/485
Alias == 
  "anim" :> \* key can be anything (grep's regex below looks for svg start/end tag).
  "<svg viewBox='0 0 300 300'>" \o SVGElemToString(Group(Grid, <<>>)) \o "</svg>"

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
