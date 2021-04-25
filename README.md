#  Rubik's cube alloy solver

## rubiks_cube.als

This my first attempt which has relations for lower level sigs like lines and squares within their own sigs.

## rubiks_cube_2.als

This is my second attempt which lifts the relations into the higher level cube sigs, meaning that it is possible to do a run for multiple cube states with the same number of instances of lower level sigs.

## two_cubes.xml

This is the output of rubiks_cube_2.als, which takes ~1hr to run and attempts to solve moving a single line onto a different face, with two cube states.

## TODO

1. Some of the lower rules on the cube may not be necessary and increase run time, like the rule for each face having four edge lines?
1. A twist can be defined without a line, just a face and a square that is on a neighbouring face and has > 1 bordering squares.
1. Continue with rules at the bottom of doTwist