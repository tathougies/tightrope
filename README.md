# tightrope: Virtual DOM implementation for Haskell

Tightrope is a virtual DOM implementation for Haskell. It differs from most virtual DOM implementations in that what needs to be diffed is decided at compile time, and we rely on compiler optimizations to write an efficient 
differ customized to our markup.
