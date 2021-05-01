import { FC } from 'react';
import { Face, FaceFC } from './Face';
import { Square } from './Square';
import './Cube.css';

export interface Cube {
   faces: Face[]
}

export const getDefaultCube = (): Cube => {
   let cube: Cube = {
      faces: Array<Face>()
   };
   for (let i = 0; i < 6; i++) {
      let face: Face = {
         pos: i,
         squares: Array<Square>()
      };
      let squareCount = 0;
      for (let x = 0; x < 2; x++) {
         for (let y = 0; y < 2; y++) {
            face.squares.push({
               x: x,
               y: y,
               z: 0,
               id: squareCount,
               colour: i
            });
            squareCount += 1;
         }
      }
      cube.faces.push(face);
   }
   return cube;
}

interface CubeProps {
   cube: Cube | null
}

export const CubeFC: FC<CubeProps> = ({ cube }) => {
   if (cube == null) return (<div></div>);

   return (
      <div id='cubeWrapper'>
         <div id='cube'>
            {cube.faces.map((face) => (
               <FaceFC face={face} />
            ))}
         </div>
      </div>
   );
}