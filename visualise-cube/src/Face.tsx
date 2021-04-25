import { FC } from 'react';
import { Square, SquareFC } from './Square';
import './Face.css';

enum FacePosition {
   Front, Back, Top, Bottom, Left, Right
}

export interface Face {
   squares: Square[],
   pos: FacePosition
}

interface FaceProps {
   face: Face
}

export const FaceFC: FC<FaceProps> = ({ face }) => {
   return (
      <div id={'face' + face.pos} className={'face'}>
         {face.squares.map((square) => (
            <SquareFC square={square} />
         ))}
      </div>
   );
}