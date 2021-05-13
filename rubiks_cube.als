open util/ordering[Cube]
open util/boolean

// enum X {0, 1}
// enum Y {0, 1}
// enum Z {0, 1}

sig Coord in Int {} {
    this >= 0
    this <= 1
}

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
    neighbours: set Face,
    isX, isY, isZ: Bool
} {
    #neighbours = 4
    all f: neighbours | this in f.@neighbours and this != f
    // #{l: lines | l.edge = True} = 4
    #{s: lines.squares} = mul[div[#lines, 2], div[#lines, 2]]
    all l: lines | some c: Cube | l.faceNo = c.faces.idxOf[this]
    no disj l1, l2: lines | l1.lx = l2.lx and
        l1.ly = l2.ly and l1.lz = l2. lz
    isX = False iff
        no lines <: lx
    isY = False iff
        no lines <: ly
    isZ = False iff
        no lines <: lz
    #{coord: {isX + isY + isZ} | coord = False} = 1
}

sig Line {
    squares: set Square,
    // edge: Bool,
    faceNo: Int,
    lx: lone Coord,
    ly: lone Coord,
    lz: lone Coord
} {
    // edge = True implies
    //     (#{s: squares | s.corner = True} = 2 and
    //     all s: squares | #s.borders >= 1)
    #{lines :> this} = 1
    all s: squares | (some lx implies s.sx = lx) and
        (some ly implies s.sy = ly) and
        (some lz implies s.sz = lz)
    #{lx + ly + lz} = 1
}

sig Square {
    // borders: set Square,
    // corner: Bool,
    sx: lone Coord,
    sy: lone Coord,
    sz: lone Coord
} {
    // no s: borders | this = s
    // corner = True implies
    //     #borders = 2
    // #borders <= 2

    // all s: Square | s in borders implies
    //     (this in s.@borders and
    //     this != s and
    //     (#borders = 2 implies some s2: Square | s2 in borders and s2 in s.@borders) and
    //     some disj f1, f2: Face | f2 in f1.neighbours and
    //     this in f1.lines.squares and
    //     s in f2.lines.squares)
    #{squares :> this} = 2

    #{sx + sy + sz} = 2
}

sig Colour {}

fact equalCoordinates {
    #lx = #ly
    #ly = #lz
    #{lx :> 0} = #{lx :> 1}
    #{ly :> 0} = #{ly :> 1}
    #{lz :> 0} = #{lz :> 1}

    // #sx = #sy
    // #sy = #sz
    // #{sx :> x0} = #{sx :> x1}
    // #{sy :> y0} = #{sy :> y1}
    // #{sz :> z0} = #{sz :> z1}
}

pred squareOnLine[l: Line, s: Square] {
    s in l.squares
}

// pred lineParrallelToFace[f: Face, l: Line] {
//     #{s: l.squares.borders | s in f.lines.squares} != 1
//     l in f.neighbours.lines
// }

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
    // #ly = 8
    // #lz = 8
    #sx = 16
    // #sy = 16
    // #sz = 16

    // Coord = {0 + 1}
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

// pred nextFaceIdx[currentIdx, nextIdx: Int] {
//     some band: Band | let faceIds = band.faceSeq |
//         some i: Int | i = faceIds.idxOf[currentIdx] and
//             (i != faceIds.lastIdx implies
//                 nextIdx = faceIds[])
// }

pred nextFaceIdx[currentIdx, focusIdx, nextIdx: Int] {
    some band: Band | let faceIds = band.faceSeq |
        faceIds.idxOf[focusIdx] = none and
        some i: Int | i = faceIds.idxOf[currentIdx] and
            (i != faceIds.lastIdx implies
                nextIdx = faceIds[i.add[1]]
            else nextIdx = faceIds[0])
}

pred rotateLine[c, c': Cube, faceIdx: Int, l1: Line] {
    some l2: Line | nextFaceIdx[l1.faceNo, faceIdx, l2.faceNo] and
        (all s1, s2: Square | (s1 in l1.squares and s2 in l2.squares) implies
            c'.colours[s2] = c.colours[s1])
}

pred mapLines[c, c': Cube, l1, l2: Line] {
    all s1: l1.squares, s2: l2.squares |
        // some l1.ly...
        (some l1.lx and ((some l1.ly and l1.ly = l2.lz) or l1.lz != l2.ly)) implies
                c'.colours[s2] = c.colours[s1]

        else (some l1.ly and ((some l1.lx and l1.lx = l2.lz) or l1.lz != l2.lx)) implies
                c'.colours[s2] = c.colours[s1]
        else (some l1.lz and ((some l1.lx and l1.lx = l2.ly) or l1.ly != l2.lx)) implies
                c'.colours[s2] = c.colours[s1]
}

pred lineParrallelToFace[f: Face, l: Line] {
    f.isX = False implies some l.lx
    else f.isY = False implies some l.ly
    else f.isZ = False and some l.lz
}

pred doTwist[c, c': Cube, faceIdx: Int, l: Line] {
    lineParrallelToFace[c.faces[faceIdx], l]
    all l1: Line | linesConnected[l, l1] implies
        (some l2: Line | linesConnected[l1, l2] and
            nextFaceIdx[l1.faceNo, faceIdx, l2.faceNo] and
            mapLines[c, c', l1, l2])
        else c'.colours[l1.squares] = c.colours[l1.squares]
    // let conLines = {l : Line | linesConnected[l, l1]} |
    //     all l2: conLines | some l3: conLines, faceIdx: Int |
    //         nextFaceIdx[l2.faceNo, faceIdx, l3.faceNo] and
    //         (all s1, s2: Square | (s1 in l1.squares and s2 in l2.squares) implies
    //             c'.colours[s2] = c.colours[s1])
    // all l2: Line | linesConnected[l1, l2] implies (
    //     some l3: 
    // )
}

// pred doTwist[c, c': Cube, faceIdx: Int, s: Square] {
//     s in c.faces[faceIdx].neighbours.lines.squares
//     some s.borders
//     some l1: Line | squareOnLine[l1, s] and
//         lineParrallelToFace[c.faces[faceIdx], l1] and

//         (all l2: Line | linesConnected[l1, l2] implies
//             rotateLine[c, c', faceIdx, l1]
//         else c'.colours[l2.squares] = c.colours[l2.squares])


//         and

//         some f1, f2: Face | l1 in f1.lines and
//             f2 in f1.neighbours and
//             f2 in c.faces[faceIdx].neighbours and
//             some l2: Line | l2 in f2.lines and
//                 some s2: Square | s2 in l2.squares and
//                     s2 in s.borders and
//                     c'.colours[l2.squares] = c.colours[l1.squares]

//     all s: Square, f: Face | ((f not in c.faces[faceIdx].neighbours and
//         squareOnFace[f, s]) or squareOnFace[c.faces[faceIdx], s]) implies
//         c'.colours[s] = c.colours[s]
// }

pred solved[c: Cube] {
    all f: c.faces.elems | #{col: Colour | some s: Square | s in f.lines.squares and
        col in c.colours[s]} = 1
}

pred solve {
    cube
    twoByTwo
    some disj c1, c2: Cube, faceIdx: Int, l: Line | doTwist[c1, c2, faceIdx, l] and
        solved[c2]
    // some c1, c2: Cube, faceIdx: Int, s: Square | doTwist[c1, c2, faceIdx, s] and
    //     solved[c2]
    // specifying that the solved cube comes last (solved[last]) makes the solution take 5x as long
}

run solve for 6 but 6 Int, exactly 2 Cube, exactly 6 Face, exactly 6 Colour, exactly 24 Line, exactly 24 Square, exactly 3 Band