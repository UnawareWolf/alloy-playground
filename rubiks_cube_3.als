open util/ordering[Cube]
open util/boolean

sig Cube {
    faces: seq Face,
    colours: Square -> one Colour
} {
    all c1, c2: Colour | #{colours :> c1} = #{colours :> c2}
    all s: Square | one s.colours
    all f: Face | f in faces.elems
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
    // #{l: lines.elems | #{s: l.squares.elems | #s.borders = 2} = 2} = 4
}

fact {
    // all disj l1, l2: Line | some {l1.squares.elems & l2.squares.elems} implies
    //     (one f: Face | {l1 + l2} in f.lines.elems and
    //     #{l1.squares.elems & l2.squares.elems} = 1)
    
    // all f1, f2: faces | all s: Square | s in f2.lines.elems.squares.elems.borders implies
    //     f1 in f2.neighbours
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
        // #borders = #s.@borders and
        (#borders = 2 implies some s2: Square | s2 in borders and s2 in s.@borders) and
        some disj f1, f2: Face | f2 in f1.neighbours and
            this in f1.lines.squares and
            s in f2.lines.squares)
    #{squares :> this} = 2
}

sig Colour {}

pred cube {
    all c1, c2: Cube | c1.faces = c2.faces
}

pred twoByTwo {
    cube
    all f: Face | #f.lines = 4
    all l: Line | #l.squares = 2
}

run twoByTwo for 6 but exactly 1 Cube, exactly 6 Face, exactly 6 Colour, exactly 24 Line, exactly 24 Square