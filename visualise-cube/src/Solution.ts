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
                let tupleItem = tuple.getElementsByTagName('atom').item(atomLabels.length);
                if (match && tupleItem !== null) {
                    pushIfNotNull(labels, tupleItem.getAttribute('label'));
                }
            }
        }
    }
    return labels;
}

const getAlloyId = (label: string): number => {
    return + label.split('$')[1];
}


export const getCubeSolution = (solnString: string): Cube[] => {
    let parser = new DOMParser();
    const solutionXML = parser.parseFromString(solnString, 'text/xml');
    let cubes: Cube[] = [getDefaultCube()];
    for (let cubeLabel of getSigAtomLabels(solutionXML, 'this/Cube')) {
        cubes[getAlloyId(cubeLabel)] = getDefaultCube();
        for (let faceLabel of getFieldTupleAtomLabel(solutionXML, 'faces', [cubeLabel])) {
            let squareLabels = new Set<string>();
            for (let lineLabel of getFieldTupleAtomLabel(solutionXML, 'lines', [cubeLabel, faceLabel])) {
                for (let squareLabel of getFieldTupleAtomLabel(solutionXML, 'squares', [cubeLabel, lineLabel])) {
                    squareLabels.add(squareLabel);
                }
            }
            let squareId = 0;
            for (let squareLabel of Array.from(squareLabels)) {
                let colourId: number = getAlloyId(getFieldTupleAtomLabel(solutionXML, 'colours', [cubeLabel, squareLabel])[0]);
                cubes[getAlloyId(cubeLabel)].faces[getAlloyId(faceLabel)].squares[squareId].colour = colourId;
                squareId++;
            }
        }
    }
    return cubes;
}