open util/boolean

sig Coord in Int {} {
    this >= 0
    this <= 1
}

sig Cube {
    // get rid of faces relation? or move out to separate sig?
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
    neighbours: set Face,
    isX, isY, isZ: Bool
} {
    #neighbours = 4
    all f: neighbours | this in f.@neighbours and this != f
    #{s: lines.squares} = mul[div[#lines, 2], div[#lines, 2]]
    all l: lines | some c: Cube | l.faceNo = c.faces.idxOf[this]
    no disj l1, l2: lines | l1.lx = l2.lx and
        l1.ly = l2.ly and l1.lz = l2. lz
    
    isX = False iff no lines <: lx
    isY = False iff no lines <: ly
    isZ = False iff no lines <: lz
    #{coord: {isX + isY + isZ} | coord = False} = 1
}

sig Line {
    squares: set Square,
    faceNo: Int,
    lx: lone Coord,
    ly: lone Coord,
    lz: lone Coord
} {
    #{lines :> this} = 1
    all s: squares | (some lx implies s.sx = lx) and
        (some ly implies s.sy = ly) and
        (some lz implies s.sz = lz)
    #{lx + ly + lz} = 1
}

sig Square {
    sx: lone Coord,
    sy: lone Coord,
    sz: lone Coord
} {
    #{squares :> this} = 2

    #{sx + sy + sz} <= 2
}

sig Colour {}

fact equalCoordinates {
    #lx = #ly
    #ly = #lz
    #{lx :> 0} = #{lx :> 1}
    #{ly :> 0} = #{ly :> 1}
    #{lz :> 0} = #{lz :> 1}
    #sx = #sy
    #sy = #sz
}

fact sharedSquares {
    all disj l1, l2 : Line |
        #{l1.squares & l2.squares} <= 1
}

pred squareOnLine[l: Line, s: Square] {
    s in l.squares
}

pred squareOnFace[f: Face, s: Square] {
    s in f.lines.squares
}

pred cube {
    all c1, c2: Cube | c1.faces = c2.faces
}

pred twoByTwo {
    all f: Face | #f.lines = 4 and
        #{f.lines <: lx} in {0 + 2} and
        #{f.lines <: ly} in {0 + 2} and
        #{f.lines <: lz} in {0 + 2}
    all l: Line | #l.squares = 2
    #lx = 8
    #sx = 16
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
fact threeBands {
    #Band = 3
    no disj b1, b2: Band | b1.faceSeq = b2.faceSeq
}

pred nextFaceIdx[currentIdx, focusIdx, nextIdx: Int] {
    some band: Band |
        band.faceSeq.idxOf[focusIdx] = none and
        some i: Int | i = band.faceSeq.idxOf[currentIdx] and
            (i != band.faceSeq.lastIdx implies
                nextIdx = band.faceSeq[i.add[1]]
            else nextIdx = band.faceSeq[0])
}

pred correspondingSquare[s1A, s1B, s2A, s2B: Coord] {
    some s1A implies (s1A = s2B)
    else (some s1B and some s2A and s1B != s2A)
}

pred mapLines[c, c': Cube, l1, l2: Line] {
    all s1: l1.squares | some s2: l2.squares |
        (some l1.lx and correspondingSquare[s1.sy, s1.sz, s2.sy, s2.sz]) implies
            c'.colours[s2] = c.colours[s1]
        else (some l1.ly and correspondingSquare[s1.sx, s1.sz, s2.sx, s2.sz]) implies
            c'.colours[s2] = c.colours[s1]
        else (some l1.lz and correspondingSquare[s1.sx, s1.sy, s2.sx, s2.sy]) and
            c'.colours[s2] = c.colours[s1]
}

pred lineParrallelToFace[f: Face, l: Line] {
    f.isX = False implies some l.lx
    else f.isY = False implies some l.ly
    else f.isZ = False and some l.lz
}

pred squareInBand[l: Line, s: Square] {
    some l.lx implies s.sx = l.lx
    some l.ly implies s.sy = l.ly
    some l.lz implies s.sz = l.lz
}

pred doTwist[c, c': Cube, faceIdx: Int, l: Line] {
    lineParrallelToFace[c.faces[faceIdx], l]
    all disj l1, l2: Line |
        (linesConnected[l, l1] and
        linesConnected[l, l2] and
        nextFaceIdx[l1.faceNo, faceIdx, l2.faceNo]) implies
            // l1, l2?
            mapLines[c, c', l2, l1]
    all s: Square |
        not squareInBand[l, s] implies
            c'.colours[s] = c.colours[s]
}

pred solved[c: Cube] {
    all f: c.faces.elems | #{col: Colour | some s: Square | s in f.lines.squares and
        col in c.colours[s]} = 1
}

pred solve {
    cube
    twoByTwo
    some disj c1, c2: Cube, faceIdx: Int, l: Line | doTwist[c1, c2, faceIdx, l] and
        solved[c2]
}

run solve for 6 but 6 Int, exactly 2 Cube, exactly 6 Face, exactly 6 Colour, exactly 24 Line, exactly 24 Square, exactly 3 Band