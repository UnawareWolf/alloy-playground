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

// May need to rethink this for cubes > 2 x 2
enum Direction { Clockwise, Anticlockwise }

sig Twist {
    face: one Face,
    line: one Line,
    direction: one Direction
} {
    // line on face of neighbour
    line in face.neighbours.lines
    // line in same plane as face, ie does not have exactly one bordering square
    // (all or none)
    #{s: line.squares | s in face.lines.squares} != 1
}

pred linesRules {
    all c: Cube {
        // all squares are on two lines
        all s: c.faces.lines.squares | #{squares :> c.faces.lines.squares}.s = 2

        // if two lines share the same square,
        // they are on the same face and have a different orientation
        // and share at most one square
        all disj l1, l2: c.faces.lines | some l1.squares :> l2.squares =>
            (l1.orientation != l2.orientation and
            one f: Face | (l1 + l2) in f.lines) and
            #{l1.squares :> l2.squares} = 1

        // all lines are on one face
        all l: c.faces.lines | one (lines :> c.faces.lines).l
    }
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

pred doTwist[c, c': Cube, t: Twist] {
    t.face in c.faces
    t.face in c'.faces
    // lines that on the face of the line that moves, and pointing in the same direction,
    // remain the same
    // one f: c.faces | t.line in f.lines and t.line in f.lines =>
    //     (all l: f.lines | l != t.line and l.orientation = t.line.orientation =>
    //         l in c'.faces.lines)
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
    linesRules
    borderingSquaresRule
    twoByTwo
    some c, c': Cube, t: Twist | doTwist[c, c', t]
}

run move for 0 but exactly 1 Twist, exactly 2 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour