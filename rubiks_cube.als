open util/ordering[Cube]
open util/boolean

sig Cube {
    faces: seq Face,
    colours: Square -> one Colour
} {
    all c1, c2: Colour | #{colours :> c1} = #{colours :> c2}
    all s: Square | one s.colours
    Face in faces.elems
    all disj f1, f2: faces.elems | add[faces.indsOf[f1], faces.indsOf[f2]] = sub[#Face, 1] <=>
        f1.neighbours = f2.neighbours
}

sig Face {
    lines: set Line,
    neighbours: set Face
} {
    #neighbours = 4
    all f: neighbours | this in f.@neighbours and this != f
    #{l: lines | l.edge = True} = 4
    #{s: lines.squares} = mul[div[#lines, 2], div[#lines, 2]]
}

sig Line {
    squares: set Square,
    edge: Bool
} {
    edge = True implies
        (#{s: squares | s.corner = True} = 2 and
        all s: squares | #s.borders >= 1)
    #{lines :> this} = 1
}

sig Square {
    borders: set Square,
    corner: Bool
} {
    no s: borders | this = s
    corner = True implies
        #borders = 2
    #borders <= 2

    all s: Square | s in borders implies
        (this in s.@borders and
        this != s and
        (#borders = 2 implies some s2: Square | s2 in borders and s2 in s.@borders) and
        some disj f1, f2: Face | f2 in f1.neighbours and
        this in f1.lines.squares and
        s in f2.lines.squares)
    #{squares :> this} = 2
}

sig Colour {}

pred squareOnLine[l: Line, s: Square] {
    s in l.squares
}

pred lineParrallelToFace[f: Face, l: Line] {
    #{s: l.squares.borders | s in f.lines.squares} != 1 and
    l in f.neighbours.lines
}

pred squareOnFace[f: Face, s: Square] {
    s in f.lines.squares
}

pred cube {
    all c1, c2: Cube | c1.faces = c2.faces
}

pred twoByTwo {
    all f: Face | #f.lines = 4
    all l: Line | #l.squares = 2
}

pred doTwist[c, c': Cube, faceIdx: Int, s: Square] {
    s in c.faces[faceIdx].neighbours.lines.squares
    some s.borders
    some l1: Line | squareOnLine[l1, s] and
        lineParrallelToFace[c.faces[faceIdx], l1] and
        some f1, f2: Face | l1 in f1.lines and
            f2 in f1.neighbours and
            f2 in c.faces[faceIdx].neighbours  and
            some l2: Line | l2 in f2.lines and
                some s2: Square | s2 in l2.squares and
                    s2 in s.borders and
                    c'.colours[l2.squares] = c.colours[l1.squares]

    all s: Square, f: Face | ((f not in c.faces[faceIdx].neighbours and
        squareOnFace[f, s]) or squareOnFace[c.faces[faceIdx], s]) implies
        c'.colours[s] = c.colours[s]

}

pred solved[c: Cube] {
    all f: c.faces.elems | #{col: Colour | some s: Square | s in f.lines.squares and
    col in c.colours[s]} = 1
}

pred solve {
    cube
    twoByTwo
    some c1, c2: Cube, faceIdx: Int, s: Square | doTwist[c1, c2, faceIdx, s] and
        solved[c2]
        // specifying that the solved cube comes last makes the solution take 5x as long
        // and lt[c1, c2]
}

run solve for 6 but exactly 2 Cube, exactly 6 Face, exactly 6 Colour, exactly 24 Line, exactly 24 Square