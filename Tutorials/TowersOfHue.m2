newPackage(
    "TowersOfHue",
    Version => "0.1",
    Date => "December 31, 2025",
    Authors => {{Name => "Assistant", Email => "assistant@example.com"}},
    Headline => "A package for solving and manipulating Towers of Hue puzzles",
    DebuggingMode => true
)

export {
    "HueState",
    "newHueState",
    "moveRing",
    "isValidMove",
    "isSolved",
    "NumberOfTowers"
}

-- Type definition for a Hue game state
HueState = new Type of HashTable

-- Constructor for the initial Hue state
-- Input: n = number of rings, k = number of towers (default 3)
-- Output: Initial state with all rings on tower 0
newHueState = method(Options => {NumberOfTowers => 3})
newHueState ZZ := opts -> n -> (
    if n <= 0 then error "Number of rings must be positive";
    k := opts.NumberOfTowers;
    if k < 3 then error "Number of towers must be at least 3";
    
    -- Create list of key-value pairs for all towers
    towerPairs := for i from 0 to k-1 list (
        if i == 0 then i => reverse toList(1..n)
        else i => {}
    );
    
    new HueState from join(towerPairs, {
        "numRings" => n,
        "numTowers" => k
    })
)

-- Draw a single tower as a Net
drawTower = (state, towerNum) -> (
    n := state#"numRings";
    tower := state#towerNum;
    w := 2*n + 1;  -- Maximum width for largest ring
    
    -- Helper function to draw a ring or pole at given level
    drawLevel := level -> (
        if level < #tower then (
            ringSize := tower#level;
            spaces := n - ringSize;
            padding := concatenate(spaces : " ");
            r := concatenate(ringSize : "=");
            padding | r | "|" | r | padding
        ) else (
            -- Just the pole
            padding = concatenate(n : " ");
            padding | "|" | padding
        )
    );
    
    -- Draw from top to bottom
    l := reverse apply(n, drawLevel);
    
    -- Add base
    base := concatenate(w : "-");
    l = append(l,  base);
    
    -- Add label
    center := n;
    padding := concatenate(center : " ");
    label := padding | toString(towerNum) | padding;
    l = append(l, label);
    
    stack l
)

-- Net method for graphical display - concatenate all towers horizontally
net HueState := state -> (
    k := state#"numTowers";
    
    -- Draw each tower as a Net
    towerNets := apply(k, i->drawTower(state, i));
    
    -- Concatenate horizontally with spacing
    horizontalJoin between("  ", towerNets)
)

-- Check if a move is valid
-- Input: state, source tower number, destination tower number
-- Output: true if valid, false otherwise
isValidMove = method()
isValidMove(HueState, ZZ, ZZ) := (state, a, b) -> (
    k := state#"numTowers";
    -- Check if tower numbers are valid
    if a < 0 or a >= k or b < 0 or b >= k then (
        return false;
    );
    -- Can't move to the same tower
    if a == b then return false;
    -- Check if source tower is empty
    if #(state#a) == 0 then return false;
    -- Check if we can place the ring (destination is empty or top ring is larger)
    if #(state#b) == 0 then return true;
    -- Top of source must be smaller than top of destination
    last(state#a) < last(state#b)
)

-- Move a ring from one tower b another
-- Input: state, source tower number, destination tower number
-- Output: new state with the move applied
moveRing = method()
moveRing(HueState, ZZ, ZZ) := (state, a, b) -> (
    if not isValidMove(state, a, b)
    then error("Invalid move from tower " | toString(a) | " to tower " | toString(b));

    newState := new MutableHashTable from state;
    -- Remove ring from source tower
    r := last(newState#a);
    newState#a = drop(newState#a, -1);
    -- Add ring to destination tower
    newState#b = append(newState#b, r);
    
    -- Return new state with updated towers
    new HueState from newState
)

-- Check if the puzzle is solved (all rings on last tower)
isSolved = method()
isSolved HueState := state -> (
    n := state#"numRings";
    k := state#"numTowers";
    lastTower := k - 1;
    #(state#lastTower) == n and state#lastTower == reverse toList(1..n)
)

beginDocumentation()

doc ///
    Key
        TowersOfHue
    Headline
        A package for solving and manipulating Towers of Hue puzzles
    Description
        Text
            This package provides tools for working with the classic Towers of Huế puzzle.
            It includes a data type for representing game states and methods for moving rings
            between towers while enforcing the rules of the game. The package supports 
            an arbitrary number of towers (minimum 3).
///

doc ///
    Key
        HueState
    Headline
        Type representing a Towers of Hue game state
    Description
        Text
            An immutable hash table containing the state of a Towers of Hue puzzle,
            including the configuration of rings on towers numbered 0, 1, 2, ..., k-1
            and the total number of rings and towers. States are displayed as ASCII art towers.
///

doc ///
    Key
        newHueState
        (newHueState, ZZ)
        [newHueState, NumberOfTowers]
    Headline
        Create a new Towers of Hue game state
    Usage
        s = newHueState n
        s = newHueState(n, NumberOfTowers => k)
    Inputs
        n:ZZ
            the number of rings in the puzzle
        NumberOfTowers => ZZ
            the number of towers (default 3, minimum 3)
    Outputs
        :HueState
            initial state with all rings on tower 0
    Description
        Text
            Creates a new Towers of Hue puzzle with n rings, all initially placed
            on tower 0 in order from largest (bottom) to smallest (top). Towers are
            numbered 0, 1, 2, ..., k-1.
        Example
            s = newHueState 3
            s
        Example
            s = newHueState(4, NumberOfTowers => 4)
            s
///

doc ///
    Key
        moveRing
        (moveRing, HueState, ZZ, ZZ)
    Headline
        Move a ring from one tower to another
    Usage
        s' = moveRing(s, a, b)
    Inputs
        s:HueState
            the current game state
        a:ZZ
            source tower number
        b:ZZ
            destination tower number
    Outputs
        :HueState
            new state with the move applied
    Description
        Text
            Returns a new state with the top ring moved from the source tower 
            to the destination tower, if the move is valid according to Towers 
            of Hue rules. The original state is not modified.
        Example
            s = newHueState 3
            s' = moveRing(s, 0, 2)
            s'
            s'' = moveRing(s', 0, 1)
            s''
///

doc ///
    Key
        isValidMove
        (isValidMove, HueState, ZZ, ZZ)
    Headline
        Check if a move is valid
    Usage
        isValidMove(s, a, b)
    Inputs
        s:HueState
        a:ZZ
            source tower number
        b:ZZ
            destination tower number
    Outputs
        :Boolean
            true if the move is valid, false otherwise
    Description
        Text
            Checks whether moving a ring from the source tower to the destination
            tower would be valid according to the rules: you can only place a smaller
            ring on top of a larger ring, and you cannot move from an empty tower.
        Example
            s = newHueState 3
            isValidMove(s, 0, 1)
            isValidMove(s, 1, 2)
///

doc ///
    Key
        isSolved
        (isSolved, HueState)
    Headline
        Check if the puzzle is solved
    Usage
        isSolved s
    Inputs
        s:HueState
    Outputs
        :Boolean
            true if all rings are on the last tower in correct order
    Description
        Text
            Returns true if the puzzle is in the solved state, with all rings
            on the last tower (tower k-1) in order from largest to smallest.
        Example
            s = newHueState 2
            s' = moveRing(s, 0, 1)
            s'' = moveRing(s', 0, 2)
            s''' = moveRing(s'', 1, 2)
            isSolved s'''
///

-- Tests
TEST ///
    s = newHueState 3
    assert(s#"numRings" == 3)
    assert(s#"numTowers" == 3)
    assert(s#0 == {3,2,1})
    assert(s#1 == {})
    assert(s#2 == {})
///

TEST ///
    s = newHueState(4, NumberOfTowers => 5)
    assert(s#"numRings" == 4)
    assert(s#"numTowers" == 5)
    assert(s#0 == {4,3,2,1})
    for i from 1 to 4 do assert(s#i == {})
///

TEST ///
    s = newHueState 3
    assert(isValidMove(s, 0, 1))
    assert(isValidMove(s, 0, 2))
    assert(not isValidMove(s, 1, 2))
    assert(not isValidMove(s, 0, 0))
    assert(not isValidMove(s, -1, 2))
    assert(not isValidMove(s, 0, 5))
///

TEST ///
    s = newHueState 3
    s' = moveRing(s, 0, 2)
    assert(s'#0 == {3,2})
    assert(s'#2 == {1})
    -- Original state unchanged
    assert(s#0 == {3,2,1})
    assert(s#2 == {})
    assert(not isValidMove(s', 0, 2))
    assert(isValidMove(s', 0, 1))
///

TEST ///
    s = newHueState 2
    s' = moveRing(s, 0, 1)
    s'' = moveRing(s', 0, 2)
    s''' = moveRing(s'', 1, 2)
    assert(isSolved s''')
///

TEST ///
    -- Test with 4 towers
    s = newHueState(3, NumberOfTowers => 4)
    s' = moveRing(s, 0, 3)
    assert(s'#0 == {3,2})
    assert(s'#3 == {1})
    s'' = moveRing(s', 0, 1)
    assert(s''#0 == {3})
    assert(s''#1 == {2})
///

end

installPackage "TowersOfHue"
check "TowersOfHue"
