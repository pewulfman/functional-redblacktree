# functional-redblacktree
A Functional Red-Black tree with insertion and deletion implemented in OCaml.

## Motivation
During my work at Marigold on LigoLang. We wanted at some point a custom polymorphic Map and Set types.
Though using Functor and first-class module is probably a wiser choice. We decided to make it from
a polymorphic Red-Black tree implementation. Our colleague having [one](https://github.com/rinderknecht/RedBlackTrees) ready.
However, the module didn't feature a deletion function that we required.

I search over the internet in order to find a functional red-black tree deletion algorithm in functional. Most result made reference to
the double-black tree propose by Matthew Might and a few to research paper that I could not understand with my beginner level at functional programming.
(I think there was intensive usage of GADT)

Looking closely at Might's algorithm. I realize that the added double-black color was unnecessary, and make the algorithm confusing.
I decided to adapt his algorithm by replacing the double-black color with a carry value (internal of the algorithm) which present
the advantage of keeping the Red-Black tree structure and the Okasaki algorithm intact as well as making the algorithm easier to follow
in my honest opinion.

Feel free to use the OCaml implementation as is, and to read the rest of the file to implement your own.

## Description of the Algorithm

see [pdf](./article/Deletion_in_red-black_tree.pdf)
