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
  TLCGet("level") < 14000 \*32000

\* https://github.com/tlaplus/tlaplus/issues/485
Alias == 
  "anim" :> Animation  \* grep below for "anim"

=============================================================================

/opt/toolbox/tla2tools.jar \
    -simulate num=1 -depth 32001 -config AsyncGameOfLifeAnimGlider.tla AsyncGameOfLifeAnimGlider.tla \
    | grep anim | sed 's;anim = ;<svg viewBox="0 0 400 400">;g; s;</g></g>";</g></g></svg>;g' > glider.out

rm -rf animation
mkdir animation
awk '{print > "animation/"NR".svg"}' glider.out
ffmpeg -y -i animation/%d.svg AsyncGameOfLifeAnimGlider_$(date +%s).mp4
rm -rf animation

vlc AsyncGameOfLifeAnimGlider_*.mp4