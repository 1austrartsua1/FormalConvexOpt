# Formal Convex Opt

Have you ever confronted a long proof in an optimization paper and thought: "Well I have no idea if this is correct". Many optimization papers have proofs that are long and tedious. While the arguments can be clever, they are often obscured by pages and pages of algebraic manipulations. Wouldn't it be great if a computer could do the checking for you? How much easier would it be to review papers! You would just need to check if the paper "compiles" correctly.

Few people know this, but there are growing movements to make this a possibility throughout the mathematical community.  This work is based on the Lean interactive proof assistant, which has attracted significant interest from mathematicians trying to "formalize" and "computerize" mathematical proofs. 

This repo is an attempt to formalize in Lean some basic convex optimization algorithm proofs. I focus on gradient descent with constant stepsize and (thusfar) prove

1. The well-known $O(1/k)$ convergence rate. 
2. Under strong convexity, the well-known linear convergence rate. (aka: exponential, geometric rate). 

The main source for the proof are the excellent lecture notes [here](http://www.seas.ucla.edu/~vandenbe/ee236c.html). 

As far as I know, this is the first formalization of these proofs in Lean and perhaps in any theorem prover. But it is totally possible someone has formalized this stuff long ago in Coq or some other framework. 

The proof (as of Jan 5th 2022) covers the vector-case (real inner product spaces) only for the linear convergence proof under strong convexity. The $O(1/k)$ proof is only for functions on scalars, but I will hopefully port it to vectors shortly, now that I know a bit more about how to handle vectors in Lean. 

I will hopefully be updating the repo regularly as I finish new proofs - pending other commitments. 

Ultimately, the benefits of this project might go beyond making the reviewer's life much easier and include:

* Making a search-able database of theorems/results/algorithms/convergence rates. 
* Can potentially write proof-carrying code. You can implement your algorithm in Lean and then also provide a proof that it actually does what it's supposed to do (modulo floating point arithmetic and other impurities). 
* Reveal errors in previous proofs. 
* Reveal extensions of previous proofs. 

This repo is hopefully a step in this direction. There is still a long way to go. And writing proofs in Lean is really tricky and has a steep learning curve. 

## Installation

For now, I only uploaded the source code in the src directory. If you want to play with this, download an empty lean project using [leanproject](https://leanprover-community.github.io/leanproject.html). Follow the instructions there for installing the leanproject command line tool and downloading an empty project with the *mathlib* library. Then, copy the source code in the **src** directory over to your new project to play around with it and see for yourself that it compiles correctly. 