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
        s in (l1 + l2).squares =>
            l1.orientation != l2.orientation and
            some f: Face | (l1 + l2) in f.lines
    // all lines are on one face
    all l: Line | one (lines).l
    // all faces are on one cube
    all f: Face | one faces.f
}

pred squaresOnOneFace{
    // all 
}

pred twoSquare {
    all f: Face | #f.neighbours = 4 and
        #f.lines = 4
    all l: Line | #l.squares = 2
    all c: Cube | #c.faces = 6
}

// pred threeSquare {
//     all f: Face | #f.neighbours = 4 and
//         #f.cols = 3 and 
//         #f.rows = 3
//     all l: Line | #l.squares = 3
//     all c: Cube | #c.faces = 6
// }

// pred 

pred move [] {
    twoSquare
}

run move for 0 but exactly 1 Cube, 6 Face, 24 Line, 24 Square, 6 Colour
// run move for 0 but exactly 1 Cube, 6 Face, 36 Line, 54 Square, 6 Colour