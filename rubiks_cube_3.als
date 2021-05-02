open util/ordering[Cube]
open util/boolean

sig Cube {
    faces: seq Face,
    colours: Square -> Colour
} {
    all c1, c2: Colour | #{colours :> c1} = #{colours :> c2}
    all s: Square | some s.colours
    all f: Face | f in faces.elems
    all disj f1, f2: faces.elems | add[faces.indsOf[f1], faces.indsOf[f2]] = sub[#Face, 1] <=>
        f1.neighbours = f2.neighbours
}

sig Face {
    lines: seq Line,
    neighbours: set Face
} {
    all f: neighbours | this in f.@neighbours and this != f
    #{l: Line | #{s: l.squares.elems | #s.borders = 2} = 2} = 4
}

fact {
    all disj l1, l2: Line | some {l1.squares.elems & l2.squares.elems} implies
        (one f: Face | {l1 + l2} in f.lines.elems and
        #{l1.squares.elems & l2.squares.elems} = 1)
}

sig Line {
    squares: seq Square
}

sig Square {
    borders: set Square
} {
    no s: borders | this = s
}

sig Colour {}

pred twoByTwo {
    #Face = 6
    all c1, c2: Cube | c1.faces = c2.faces
    all f: Face | #f.lines = 4 and
    #f.neighbours = 4
    all l: Line | #l.squares = 2
    #Colour = 6
    #Cube = 2
}

run twoByTwo for 6 but exactly 2 Cube, exactly 6 Colour, exactly 24 Square