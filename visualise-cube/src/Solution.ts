import { Cube, getDefaultCube } from './Cube';

const getSigAtomLabels = (solution: Document, sigLabel: string): string[] => {
    let sigLabels: string[] = [];
    for (let sigAtom of Array.from(solution.getElementsByTagName('sig'))) {
        if (sigAtom.getAttribute('label') === sigLabel) {
            Array.from(sigAtom.children).map(atom => (
                pushIfNotNull(sigLabels, atom.getAttribute('label'))
            ));
            break;
        }
    }
    return sigLabels;
}

const pushIfNotNull = (array: string[], item: string | null) => {
    if (item !== null) array.push(item);
}

const getFieldTupleAtomLabel = (solution: Document, fieldLabel: string, atomLabels: string[]): string[] => {
    let labels: string[] = [];
    for (let field of Array.from(solution.getElementsByTagName('field'))) {
        if (field.getAttribute('label') === fieldLabel) {
            for (let tuple of Array.from(field.getElementsByTagName('tuple'))) {
                let match = true;
                for (let atomId in atomLabels) {
                    let tupleItem = tuple.getElementsByTagName('atom').item(+atomId);
                    if (tupleItem !== null && tupleItem.getAttribute('label') !== atomLabels[atomId]) {
                        match = false;
                        break;
                    }
                }
                let tupleItem = tuple.getElementsByTagName('atom').item(tuple.getElementsByTagName('atom').length - 1);
                if (match && tupleItem !== null) {
                    pushIfNotNull(labels, tupleItem.getAttribute('label'));
                }
            }
        }
    }
    return labels;
}

const getAlloyId = (label: string): number => {
    return +label.split('$')[1];
}

const getSquareId = (faceIdx: number, x: number, y: number, z: number): number => {
    let validCoords: string = '';
    switch (faceIdx) {
        case 0:
            validCoords += x;
            validCoords += 1 - z;
            break;
        case 3:
            validCoords += 1 - y;
            validCoords += z;
            break;
        case 1:
            validCoords += x;
            validCoords += 1 - y;
            break;
        default:
            for (let coord of [x, y, z]) {
                if (!Number.isNaN(coord)) {
                    validCoords += coord;
                }
            }
    }
    
    switch (validCoords) {
        case '00': return 0;
        case '10': return 1;
        case '01': return 2;
        default: return 3;
    }
}

export const getCubeSolution = (solnString: string): Cube[] => {
    let parser = new DOMParser();
    const solutionXml = parser.parseFromString(solnString, 'text/xml');
    let cubes: Cube[] = [getDefaultCube()];
    for (let cubeLabel of getSigAtomLabels(solutionXml, 'this/Cube')) {
        cubes[getAlloyId(cubeLabel)] = getDefaultCube();
        let faceIdx = 0;
        for (let faceLabel of getFieldTupleAtomLabel(solutionXml, 'faces', [cubeLabel])) {
            let squareLabels = new Set<string>();
            for (let lineLabel of getFieldTupleAtomLabel(solutionXml, 'lines', [faceLabel])) {
                for (let squareLabel of getFieldTupleAtomLabel(solutionXml, 'squares', [lineLabel])) {
                    squareLabels.add(squareLabel);
                }
            }
            // let squareId = 0;
            for (let squareLabel of Array.from(squareLabels)) {
                let colourId: number = getAlloyId(getFieldTupleAtomLabel(solutionXml, 'colours', [cubeLabel, squareLabel])[0]);
                let x: number = +getFieldTupleAtomLabel(solutionXml, 'sx', [squareLabel])[0];
                let y: number = +getFieldTupleAtomLabel(solutionXml, 'sy', [squareLabel])[0];
                let z: number = +getFieldTupleAtomLabel(solutionXml, 'sz', [squareLabel])[0];
                // face index should be seq int atom not the alloy id
                // cubes[getAlloyId(cubeLabel)].faces[faceIdx].squares[squareId].colour = colourId;
                let squareId = getSquareId(faceIdx, x, y, z);
                cubes[getAlloyId(cubeLabel)].faces[faceIdx].squares[squareId] = {
                    colour: colourId,
                    id: squareId,
                    x: x,
                    y: y,
                    z: z
                }
                // squareId++;
            }
            faceIdx++;
        }
    }
    return cubes;
}