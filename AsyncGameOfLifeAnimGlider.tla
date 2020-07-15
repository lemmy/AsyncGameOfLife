------------------------ CONFIG AsyncGameOfLifeAnimGlider --------------------
CONSTANT
N <- AnimN
SPECIFICATION Glider
INVARIANT Inv
ALIAS Alias
=============================================================================

------------------------ MODULE AsyncGameOfLifeAnimGlider --------------------
EXTENDS AsyncGameOfLifeAnim

AnimN == 8

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
    | grep -o "<svg.*<\/svg>" > glider.out

## Convert glider.out to a set of svg files (would prefer to somehow do this with grep).
rm -rf animation
mkdir animation
awk '{print > "animation/"NR".svg"}' glider.out

## Render set of svg files as mp4 video (ffmpeg has no support for piping it images yet).
ffmpeg -y -i animation/%d.svg AsyncGameOfLifeAnimGlider_$(date +%s).mp4
rm -rf animation

## Show generated animation.
vlc AsyncGameOfLifeAnimGlider_*.mp4
```