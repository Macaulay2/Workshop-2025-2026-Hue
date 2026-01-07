-- Package-writing tutorial for Hue 2026
-*
We start with some code for the package that implements
functionality to play versions of the "Towers of Hanoi" puzzle.
We will call the package `TowersOfHue`.
*-

-- Note: to start a new package one can use a template: e.g.,
packageTemplate "TowersOfHue"
-*
The starter code `TowersOfHue.m2` (that already implements some things)
is posted. Download and try to implement
  changed that we discuss in the tutorial
  and more! (see "exercises" at the end)
*-


-- Let's walk through (and change) the starter code:
  -*
  modify the header
  to export or not to export?
  new Type
  a method with options
  an internal (not exported) function `drawTower`
  define `net` for `HueState`
  logic expressions in `isValidMove`
  implement moveRing (mutable hash table?)
  *-

  
-- Documentation:
  installPackage "TowersOfHue" -- to build documentation
  viewHelp "TowersOfHue" -- or `help` instead of viewHelp
  -*  
  write `moveRing` node
  complete the example in `isSolved`
  *-

-- Tests:
  check "TowersOfHue"
  -*
  tests need to be as comprehensive as possible (but simple and fast)
  look at `newHueState` test
  look at `isValidMove` test
  complete the test for `moveRing` and `isSolved`
  *-
  tests "TowersOfHue"
  
-- Things to try (exercises?)
  -*
  create an algorithm to solve the puzzle; it needs to
    start with the initial state `newHueState`
    use `moveRing`
    to get to the state that `isSolved`
  consider a variant of the puzzle, "Cyclic Towers of Hue"
    only moves to the (cyclically) next tower (e.g. 1 to 2; or last to first) are allowed
    write isValidCyclicMove
    what puzzles are solvable?
    write an algorithm to do the moves
  write `texMath` method to make `HueState` look good in Macaulay2Web
  *-

  
