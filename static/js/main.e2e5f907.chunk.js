(this["webpackJsonpvisualise-cube"]=this["webpackJsonpvisualise-cube"]||[]).push([[0],[,,,,,,,,,,,function(e,t,r){},function(e,t,r){},,function(e,t,r){},function(e,t,r){},function(e,t,r){},function(e,t,r){"use strict";r.r(t);var n,a=r(1),c=r.n(a),u=r(6),i=r.n(u),o=(r(11),r(4)),s=(r(12),r(0));!function(e){e[e.White=0]="White",e[e.Yellow=1]="Yellow",e[e.Green=2]="Green",e[e.Blue=3]="Blue",e[e.Red=4]="Red",e[e.Black=5]="Black"}(n||(n={}));var l,f=function(e){var t=e.square;return Object(s.jsx)("div",{className:"square"+t.id+" square c"+t.colour.toString()})};r(14);!function(e){e[e.Front=0]="Front",e[e.Back=1]="Back",e[e.Top=2]="Top",e[e.Bottom=3]="Bottom",e[e.Left=4]="Left",e[e.Right=5]="Right"}(l||(l={}));var b=function(e){var t=e.face;return Object(s.jsx)("div",{id:"face"+t.pos,className:"face",children:t.squares.map((function(e){return Object(s.jsx)(f,{square:e})}))})},j=(r(15),function(){for(var e={faces:Array()},t=0;t<6;t++){for(var r={pos:t,squares:Array()},n=0,a=0;a<2;a++)for(var c=0;c<2;c++)r.squares.push({x:a,y:c,z:0,id:n,colour:t}),n+=1;e.faces.push(r)}return e}),d=function(e){var t=e.cube;return null==t?Object(s.jsx)("div",{}):Object(s.jsx)("div",{id:"cubeWrapper",children:Object(s.jsx)("div",{id:"cube",children:t.faces.map((function(e){return Object(s.jsx)(b,{face:e})}))})})},v=r(2),m=function(e,t){null!==t&&e.push(t)},h=function(e,t,r){for(var n=[],a=0,c=Array.from(e.getElementsByTagName("field"));a<c.length;a++){var u=c[a];if(u.getAttribute("label")===t)for(var i=0,o=Array.from(u.getElementsByTagName("tuple"));i<o.length;i++){var s=o[i],l=!0;for(var f in r){var b=s.getElementsByTagName("atom").item(+f);if(null!==b&&b.getAttribute("label")!==r[f]){l=!1;break}}var j=s.getElementsByTagName("atom").item(s.getElementsByTagName("atom").length-1);l&&null!==j&&m(n,j.getAttribute("label"))}}return n},g=function(e){return+e.split("$")[1]},O=function(e){var t,r=(new DOMParser).parseFromString(e,"text/xml"),n=[j()],a=Object(v.a)(function(e,t){for(var r=[],n=0,a=Array.from(e.getElementsByTagName("sig"));n<a.length;n++){var c=a[n];if(c.getAttribute("label")===t){Array.from(c.children).map((function(e){return m(r,e.getAttribute("label"))}));break}}return r}(r,"this/Cube"));try{for(a.s();!(t=a.n()).done;){var c=t.value;n[g(c)]=j();var u,i=0,o=Object(v.a)(h(r,"faces",[c]));try{for(o.s();!(u=o.n()).done;){var s,l=u.value,f=new Set,b=Object(v.a)(h(r,"lines",[l]));try{for(b.s();!(s=b.n()).done;){var d,O=s.value,p=Object(v.a)(h(r,"squares",[O]));try{for(p.s();!(d=p.n()).done;){var y=d.value;f.add(y)}}catch(q){p.e(q)}finally{p.f()}}}catch(q){b.e(q)}finally{b.f()}for(var x=0,B=0,A=Array.from(f);B<A.length;B++){var N=A[B],k=g(h(r,"colours",[c,N])[0]);n[g(c)].faces[i].squares[x].colour=k,x++}i++}}catch(q){o.e(q)}finally{o.f()}}}catch(q){a.e(q)}finally{a.f()}return n},p=(r(16),function(){var e=Object(a.useState)(!0),t=Object(o.a)(e,2),r=t[0],n=t[1],c=Object(a.useState)([j()]),u=Object(o.a)(c,2),i=u[0],l=u[1],f=Object(a.useState)(0),b=Object(o.a)(f,2),v=b[0],m=b[1];return Object(a.useEffect)((function(){fetch("/alloy-playground/solution.xml").then((function(e){return e.text()})).then((function(e){l(O(e)),n(!1)}))}),[]),Object(s.jsxs)("div",{className:"App",children:[r&&"parsing solution",!r&&Object(s.jsxs)("div",{id:"selectors",children:[Object(s.jsx)("button",{className:0!==v?"":"hide",onClick:function(){return m(v-1)},children:"<"}),Object(s.jsx)("span",{id:"selection",children:v}),Object(s.jsx)("button",{className:v<i.length-1?"":"hide",onClick:function(){return m(v+1)},children:">"})]}),!r&&Object(s.jsx)(d,{cube:i[v]})]})});i.a.render(Object(s.jsx)(c.a.StrictMode,{children:Object(s.jsx)(p,{})}),document.getElementById("root"))}],[[17,1,2]]]);
//# sourceMappingURL=main.e2e5f907.chunk.js.map