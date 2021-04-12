open util/ordering[Cube]

sig Cube {
    faces: some Face,
    neighbours: faces -> faces,
    lines: faces one -> some Line,
    squares: faces.lines -> Square,
    colours: Square -> one Colour,
    borders: Line.squares -> Line.squares
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
        (one f: faces | (l1 + l2) in f.lines
        and #{l1.squares :> l2.squares} = 1)
    // each face has four edge lines, where an edge line is a line
    // that has two corner squares, and a corner square is a square
    // that has two borders
    all f: faces | #{l: f.lines | #{s: l.squares| #s.borders = 2} = 2} = 4
    // squares are in their borders' borders and do not border themselves
    // squares on corners border the same square
    all s1, s2: Line.squares | s1 in s2.borders =>
        (s2 in s1.borders
        and s1 != s2
        and (#s2.borders > 1 => some s: Line.squares | s in s1.borders and s in s2.borders))
    // lines that share borders are on neighbouring faces
    all f1, f2: faces | all s: f1.lines.squares | s in f2.lines.squares.borders =>
        f1 in f2.neighbours
}

sig Face, Line, Square {}

sig Colour {}

fun getOppositeFace[c: Cube, f: Face]: Face {
    {f1: Face | f1 not in c.neighbours[f]}
}

fun getSquaresOnFace[c: Cube, f: Face]: Square {
    {s: Square | s in c.squares[c.lines[f]]}
}

pred isParrallel[c: Cube, f: Face, l: Line] {
    one f1: c.neighbours[f] | l in c.lines[f1]
        and #{s: c.squares[l] | s in c.borders[getSquaresOnFace[c, f]]} != 1
}

pred doTwist[c, c': Cube, f: Face, l: Line, s: Square] {
    isParrallel[c, f, l]
    c'.faces = c.faces
    c'.neighbours = c.neighbours
    c'.colours = c.colours
    c'.borders = c.borders
    c'.lines[f] = c.lines[f]
    c'.lines[getOppositeFace[c, f]] = c.lines[getOppositeFace[c', f]]
    // the line parrallel to f that has a square bordering s will have its squares set
    // to the squares of l
    one l1: c'.lines[Face] | (isParrallel[c, f, l1]
        and c.squares[l1] in c.borders[s]) =>
            c'.squares[l1] = c.squares[l]
    // now rotate whole perimeter not just move single line...
}

pred twoByTwo {
    all c: Cube {
        #c.faces = 6
        all f: c.faces | #c.lines[f] = 4
            and #f.(c.neighbours) = 4
            and all l: c.lines[f] | #c.squares[l] = 2
    }
}

pred solveTwoByTwo {
    twoByTwo
    some c, c': Cube, f: Face, l: Line, s: Square | doTwist[c, c', f, l ,s]
}

run twoByTwo for 0 but exactly 2 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour