------------------------ CONFIG AsyncGameOfLifeAnimBlinker --------------------
CONSTANT
N <- BlinkerN
SPECIFICATION Blinker
INVARIANT Inv
ALIAS Alias
=============================================================================

------------------------ MODULE AsyncGameOfLifeAnimBlinker --------------------
EXTENDS AsyncGameOfLifeAnim

Inv ==
  TLCGet("level") <2500

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
