open util/ordering[Cube]
open util/boolean

enum X {x0, x1}
enum Y {y0, y1}
enum Z {z0, z1}

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
    all l: lines | some c: Cube | l.faceNo = c.faces.idxOf[this]
}

sig Line {
    squares: set Square,
    edge: Bool,
    faceNo: Int,
    lx: lone X,
    ly: lone Y,
    lz: lone Z
} {
    edge = True implies
        (#{s: squares | s.corner = True} = 2 and
        all s: squares | #s.borders >= 1)
    #{lines :> this} = 1
    all s: squares | some lx implies s.sx = lx and
        some ly implies s.sy = ly and
        some lz implies s.sz = lz
    #{lx + ly + lz} = 1
}

sig Square {
    borders: set Square,
    corner: Bool,
    sx: lone X,
    sy: lone Y,
    sz: lone Z
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

    #{sx + sy + sz} = 2
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

pred squareInRing[f: Face, turnLine: Line, ringSquare: Square] {
    some l1, l2: Line | lineParrallelToFace[f, l1] and
        lineParrallelToFace[f, l2] and
        some s1: l1.squares, s2: l2.squares | s1 in turnLine.squares.borders and
            s2 in l1.squares.borders and
            (ringSquare = s1 or ringSquare = s2)
}

pred linesConnected[l1, l2: Line] {
    l1.lx = l2.lx
    l1.ly = l2.ly
    l1.lz = l2.lz
}

sig Band {
    faceSeq: seq Int
} {
    #faceSeq = 4
    (faceSeq[0] = 0 and faceSeq[1] = 1 and faceSeq[2] = 5 and faceSeq[3] = 4) or
    (faceSeq[0] = 0 and faceSeq[1] = 2 and faceSeq[2] = 5 and faceSeq[3] = 3) or
    (faceSeq[0] = 1 and faceSeq[1] = 2 and faceSeq[2] = 4 and faceSeq[3] = 3)
}
fact {
    #Band = 3
    no disj b1, b2: Band | b1.faceSeq = b2.faceSeq
}

pred band[b: Band] {

}

run band for 0 but 1 Band

pred nextFaceIdx[currentIdx, focusIdx, nextIdx: Int] {
    some band: Band | let faceIds = band.faceSeq |
        faceIds.idxOf[focusIdx] = none and
        some i: Int | i = faceIds.idxOf[currentIdx] and
            (i != faceIds.lastIdx implies
                nextIdx = faceIds[i.add[1]]
            else nextIdx = faceIds[0])
}

pred doTwist[c, c': Cube, faceIdx: Int, s: Square] {
    s in c.faces[faceIdx].neighbours.lines.squares
    some s.borders
    some l1: Line | squareOnLine[l1, s] and
        lineParrallelToFace[c.faces[faceIdx], l1] and

        (all l2: Line | (not linesConnected[l1, l2] implies
            c'.colours[l2.squares] = c.colours[l2.squares]
        else some l3: Line | nextFaceIdx[l2.faceNo, faceIdx, l3.faceNo] and
            (all s3, s4: Square | (s3 in l2.squares and s4 in l3.squares) implies
                c'.colours[s4] = c.colours[s3])
        )) and
        // (all s1: Square | not squareInRing[c.faces[faceIdx], l1, s1] implies
        //     c'.colours[s1] = c.colours[s1]) and
        some f1, f2: Face | l1 in f1.lines and
            f2 in f1.neighbours and
            f2 in c.faces[faceIdx].neighbours and
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
    // specifying that the solved cube comes last (solved[last]) makes the solution take 5x as long
}

run solve for 6 but exactly 2 Cube, exactly 6 Face, exactly 6 Colour, exactly 24 Line, exactly 24 Square, exactly 3 Band