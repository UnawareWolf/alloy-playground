import { FC, useEffect, useState } from 'react';
import { Cube, CubeFC, getDefaultCube } from './Cube';
import { getCubeSolution } from './Solution';
import './App.css';

const App: FC = () => {
   const [loading, setLoading] = useState<boolean>(true);
   const [cubes, setCubes] = useState<Cube[]>([getDefaultCube()]);
   const [selectedCube, setSelectedCube] = useState<number>(0);

   useEffect(() => {
      fetch('/two_cubes.xml').then(r => r.text()).then(text => {
         setCubes(getCubeSolution(text));
         setLoading(false);
      });
   }, []);

   return (
      <div className="App">
         {loading && 'parsing solution'}
         {!loading && <CubeFC cube={cubes[selectedCube]} />}
      </div>
   );
}

export default App;
