import { Cube, getDefaultCube } from './Cube';

const getCubeLabels = (solution: Document): string[] => {
    let cubeLabels: string[] = [];
    for (let cubeAtom of Object.values(solution.getElementsByTagName('sig'))) {
        if (cubeAtom.getAttribute('label') === 'this/Cube') {
            Array.from(cubeAtom.children).map(cube => (
                pushIfNotNull(cubeLabels, cube.getAttribute('label'))
            ));
            break;
        }
    }
    return cubeLabels;
}

const pushIfNotNull = (array: string[], item: string | null) => {
    if (item !== null) array.push(item);
}

const getAttributeNullChecks = (htmlElement : Element | null, attribute : string): string => {
    if (htmlElement === null) return '';
    let value: string | null = htmlElement.getAttribute(attribute);
    if (value === null) return '';
    else return value;
}

const getFaceLabels = (solution: Document, cubeLabel: string): string[] => {
    let faceLabels: string[] = [];
    for (let field of Object.values(solution.getElementsByTagName('field'))) {
        if (field.getAttribute('label') === 'faces') {
            for (let tuple of Object.values(field.getElementsByTagName('tuple'))) {
                if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(0), 'label') === cubeLabel) {
                    // console.log(Object.values(tuple.getElementsByTagName('atom'))[1]);
                    faceLabels.push(getAttributeNullChecks(tuple.getElementsByTagName('atom').item(1), 'label'));
                }
            }
            break;
        }
    }
    // console.log(faceLabels);
    return faceLabels;
}

const getLineLabels = (solution: Document, cubeLabel: string, faceLabel: string): string[] => {
    let lineLabels: string[] = [];
    for (let field of Object.values(solution.getElementsByTagName('field'))) {
        if (field.getAttribute('label') === 'lines') {
            for (let tuple of Object.values(field.getElementsByTagName('tuple'))) {
                if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(0), 'label') === cubeLabel) {
                    if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(1), 'label') === faceLabel) {
                        lineLabels.push(getAttributeNullChecks(tuple.getElementsByTagName('atom').item(2), 'label'));
                    }
                }
            }
            break;
        }
    }
    return lineLabels;
}

const getSquareLabels = (solution: Document, cubeLabel: string, lineLabel: string): string[] => {
    let squareLabels: string[] = [];
    for (let field of Object.values(solution.getElementsByTagName('field'))) {
        if (field.getAttribute('label') === 'squares') {
            for (let tuple of Object.values(field.getElementsByTagName('tuple'))) {
                if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(0), 'label') === cubeLabel) {
                    if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(1), 'label') === lineLabel) {
                        squareLabels.push(getAttributeNullChecks(tuple.getElementsByTagName('atom').item(2), 'label'));
                    }
                }
            }
            break;
        }
    }
    return squareLabels;
}

const getColourLabels = (solution: Document, cubeLabel: string, squareLabel: string): string[] => {
    let colourLabels: string[] = [];
    for (let field of Object.values(solution.getElementsByTagName('field'))) {
        if (field.getAttribute('label') === 'colours') {
            for (let tuple of Object.values(field.getElementsByTagName('tuple'))) {
                if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(0), 'label') === cubeLabel) {
                    if (getAttributeNullChecks(tuple.getElementsByTagName('atom').item(1), 'label') === squareLabel) {
                        colourLabels.push(getAttributeNullChecks(tuple.getElementsByTagName('atom').item(2), 'label'));
                    }
                }
            }
            break;
        }
    }
    return colourLabels;
}


const getAlloyId = (label: string): number => {
    return + label.split('$')[1];
}


export const getCubeSolution = (solnString: string): Cube[] => {
    let parser = new DOMParser();
    const solutionXML = parser.parseFromString(solnString, 'text/xml');
    let cubes: Cube[] = [getDefaultCube()];
    for (let cubeLabel of getCubeLabels(solutionXML)) {
        cubes[getAlloyId(cubeLabel)] = getDefaultCube();
        for (let faceLabel of getFaceLabels(solutionXML, cubeLabel)) {
            let squareLabels = new Set<string>();
            for (let lineLabel of getLineLabels(solutionXML, cubeLabel, faceLabel)) {
                for (let squareLabel of getSquareLabels(solutionXML, cubeLabel, lineLabel)) {
                    squareLabels.add(squareLabel);
                }
            }
            let squareId = 0;
            for (let squareLabel of Array.from(squareLabels)) {
                let colourId: number = getAlloyId(getColourLabels(solutionXML, cubeLabel, squareLabel)[0]);
                // console.log(`face ${faceLabel} square ${squareId} colour ${colourId}`);
                cubes[getAlloyId(cubeLabel)].faces[getAlloyId(faceLabel)].squares[squareId].colour = colourId;
                squareId++;
            }
        }
    }
    return cubes;
    // return [getDefaultCube()];
}