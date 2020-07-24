------------------------ CONFIG AsyncGameOfLifeAnimGlider --------------------
CONSTANT
N <- GliderN
SPECIFICATION Glider
INVARIANT Inv
ALIAS Alias
=============================================================================

\* Glider
\* https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life#/media/File:Game_of_life_animated_glider.gif
------------------------ MODULE AsyncGameOfLifeAnimGlider --------------------
EXTENDS AsyncGameOfLifeAnim

GliderN ==
  5
  
Glider == 
  \* From top-left.
  /\ grid = [ pos \in Pos |-> IF pos \in {<<1,3>>,<<2,1>>,<<2,3>>,<<3,2>>,<<3,3>>}
                    THEN <<TRUE, TRUE, 0>>
                    ELSE <<FALSE, FALSE, 0>> ]
  /\ [][Next]_vars

Inv ==
  TLCGet("level") < 14000

\* https://github.com/tlaplus/tlaplus/issues/485
Alias == 
  "anim" :> \* key can be anything (grep's regex below looks for svg start/end tag).
  SVGElemToString(Svg(Grid, <<>>))

=============================================================================

```bash
/opt/toolbox/tla2tools.jar \
-simulate num=1 -depth 32001 \
-config AsyncGameOfLifeAnimGlider.tla AsyncGameOfLifeAnimGlider.tla \
| awk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > n ".svg" }'

## Render set of svg files as mp4 video (ffmpeg has no support for piping it images yet).
## Replace "mp4" with "gif" to create an animated gif that can be posted on e.g. Twitter.
ffmpeg -y -i %d.svg AsyncGameOfLifeAnimGlider_$(date +%s).mp4 && rm *.svg

## Show generated animation.
vlc AsyncGameOfLifeAnimGlider_*.mp4
```



## Convert mp4 to gif so that it can be posted on twitter.
#ffmpeg -ss 30 -t 3 -i input.mp4 -vf "fps=10,scale=320:-1:flags=lanczos,split[s0][s1];[s0]palettegen[p];[s1][p]paletteuse" -loop 0 output.gif
