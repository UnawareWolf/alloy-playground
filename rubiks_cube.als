sig Cube {
    faces: some Face
}

sig Face {
    lines: some Line,
    neighbours: some Face
} {
    #{lines.orientation :> Vertical} = #{lines.orientation :> Horizontal}
    this not in neighbours
}

enum Orientation { Vertical, Horizontal }

sig Line {
    orientation: one Orientation,
    squares: some Square
}

sig Square {
    colour: one Colour
}

sig Colour {
    
}

fact {
    // all squares are on two lines
    all s: Square | #squares.s = 2
    // if two lines share the same square,
    // they are on the same face and have a different orientation
    all l1, l2: Line | some s: Square |
        s in (l1 & l2).squares =>
            l1.orientation != l2.orientation and
            some f: Face | (l1 & l2) in f.lines
    // all lines are on one face
    all l: Line | one (lines).l
    // all faces are on one cube
    all f: Face | one faces.f
    // there are the same number of squares of each colour
    all c1, c2 : Colour | #{colour :> c1} = #{colour :> c2}
}

pred twoByTwo {
    all f: Face | #f.neighbours = 4 and
        #f.lines = 4
    all l: Line | #l.squares = 2
    all c: Cube | #c.faces = 6
    // all c : Colour | #{colour :> c} = 4
    // all c1, c2 : Colour | #{colour :> c1} = #{colour :> c2}
    // ^ says the same thing as ^^ (in a more abstract way) but takes a LOT longer.
    // I have sped up the analysis by specifying the exact number of each sig instance
}

pred move [] {
    twoByTwo
}

run move for 0 but exactly 1 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour