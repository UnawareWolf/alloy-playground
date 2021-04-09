open util/ordering[Cube]

sig Cube {
    faces: some Face,
    neighbours: faces -> faces,
    lines: faces one -> some Line,
    // orientation: faces.lines -> one Orientation,
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
    all disj l1, l2: Face.lines | some l1.squares :> l2.squares => (
        one f: faces | (l1 + l2) in f.lines
        and #{l1.squares :> l2.squares} = 1
        // and l1.orientation != l2.orientation
        )
    // 
    all f: faces | #{l: f.lines | #{s: l.squares| #s.borders = 2} = 2} = 4
    all s1, s2: Line.squares | s1 in s2.borders =>
        (s2 in s1.borders
        and s1 != s2
        and (#s2.borders > 1 => some s: Line.squares | s in s1.borders and s in s2.borders))
    all f1, f2: faces | all s: f1.lines.squares | s in f2.lines.squares.borders =>
        f1 in f2.neighbours
}

sig Face, Line, Square {}

sig Colour {}

enum Orientation { Horizontal, Vertical }

pred isParrallel[c: Cube, f: Face, l: Line] {
    
}

pred doTwist[c, c': Cube, f: Face, l: Line, s: Square] {

}

pred twoByTwo {
    all c: Cube {
        #c.faces = 6
        all f: c.faces | #c.lines[f] = 4
            and #f.(c.neighbours) = 4
            and all l: c.lines[f] | #c.squares[l] = 2
    }
}

run twoByTwo for 0 but exactly 1 Cube, exactly 6 Face, exactly 24 Line, exactly 24 Square, exactly 6 Colour