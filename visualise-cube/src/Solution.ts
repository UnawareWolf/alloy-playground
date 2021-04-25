import { Cube, getDefaultCube } from './Cube';

export const getCubeSolution = (solnString: string): Cube[] => {
    let parser = new DOMParser();
    const solutionXML = parser.parseFromString(solnString, 'text/html');
    // console.log(solnString);
    console.log(solutionXML.getElementsByTagName('atom')[0]);
    return [getDefaultCube()];
}