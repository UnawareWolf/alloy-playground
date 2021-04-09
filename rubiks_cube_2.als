open util/ordering[Cube]

sig Cube {
    faces: some Face,
    lines: faces one -> some Line,
    neighbours: faces -> faces,
    squares: Line -> Square,
    colours: Square -> one Colour
} {
    // no face is its own neighbour
    all f: faces | no f2: f.neighbours | f2 = f
    // a face is a neighbour of all its neighbouring faces
    all f1, f2: faces | f1 in f2.neighbours <=> f2 in f1.neighbours
    // same number of each colour
    all c1, c2: Colour | #{colours :> c1} = #{colours :> c2}
    // all squares are on two lines
    all s: Line.squares | #s.~squares = 2
    // if two lines share the same square,
    // they are on the same face and have a different orientation
    // and share at most one square
    all disj l1, l2: Face.lines | some l1.squares :> l2.squares =>
        one f: faces | (l1 + l2) in f.lines
        and #{l1.squares :> l2.squares} = 1
}

sig Face, Line, Square {}

sig Colour {}

pred twoByTwo {
    all c: Cube {
        #c.faces = 6
        all f: c.faces | #c.lines[f] = 4
            and #f.(c.neighbours) = 4
            and all l: c.lines[f] | #c.squares[l] = 2
    }
}

run twoByTwo for 0 but exactly 2 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour