import { FC } from 'react';
import './Square.css';

export enum Colour {
   White, Yellow, Green, Blue, Red, Black
}

export interface Square {
   x: number,
   y: number,
   z: number,
   id: number,
   colour: Colour
}

const defaultSquare: Square = {
   x: 0,
   y: 0,
   z: 0,
   id: 0,
   colour: Colour.Blue
}

interface SquareProps {
   square: Square
}

export const SquareFC: FC<SquareProps> = ({ square }) => {
   return (
      <div className={'square' + square.id +
         ' square c' + square.colour.toString()} />
   );
}