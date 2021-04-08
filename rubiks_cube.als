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

fact {
    all f1, f2: Face | f1 in f2.neighbours <=> f2 in f1.neighbours
}

enum Orientation { Vertical, Horizontal }

sig Line {
    orientation: one Orientation,
    squares: set Square
}

sig Square {
    colour: one Colour,
    borders: some Square
} {
    this not in borders
}

sig Colour {}

fact {
    // all squares are on two lines
    all s: Square | #squares.s = 2

    // if two lines share the same square,
    // they are on the same face and have a different orientation
    // and share at most one square
    all disj l1, l2: Line | some l1.squares :> l2.squares =>
            (l1.orientation != l2.orientation and
            one f: Face | (l1 + l2) in f.lines) and
            #{l1.squares :> l2.squares} = 1

    // all lines are on one face
    all l: Line | one (lines).l

    // all faces are on one cube
    all f: Face | one faces.f

    // there are the same number of squares of each colour
    all c1, c2 : Colour | #{colour :> c1} = #{colour :> c2}
}

pred edgeLine[l: Line] {
    #{s: l.squares | #s.borders = 2} = 2
}

pred faceHasFourEdgeLines[f: Face] {
    #{l: f.lines | edgeLine[l]} = 4
}

pred borderingSquaresRule {
    all f: Face | faceHasFourEdgeLines[f]
    all s1, s2: Square | s1 in s2.borders <=> s2 in s1.borders
    // lines that share borders are on neighbouring faces
    all f1, f2: Face | all s: f1.lines.squares | s in f2.lines.squares.borders =>
        f1 in f2.neighbours
    // the border of a square with two borders shares a border with the
    // original square
    all s1, s2: Square | some s: Square | s1 in s2.borders =>
        s in s1.borders and s in s2.borders
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
    borderingSquaresRule
    twoByTwo
}

run move for 0 but exactly 1 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour