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
         {!loading && 
            <div id='selectors'>
               {<button className={selectedCube !== 0 ? '' : 'hide'} onClick={() => setSelectedCube(selectedCube - 1)}>{'<'}</button>}
               <span id='selection'>{selectedCube}</span>
               {<button className={selectedCube < cubes.length - 1 ? '' : 'hide'} onClick={() => setSelectedCube(selectedCube + 1)}>{'>'}</button>}
            </div>
         }
         {!loading && <CubeFC cube={cubes[selectedCube]} />}
      </div>
   );
}

export default App;
