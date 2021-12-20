# Formal Convex Opt

Have you ever confronted a long proof in an optimization paper and thought: "Well I have no idea if this is correct". Many optimization papers have proofs that are long and tedious. While the arguments can be clever, they are often obscured by pages and pages of algebraic manipulations. Wouldn't it be great if a computer could do the checking for you? How much easier would it be to review papers! You would just need to check if the paper "compiles" correctly.

Few people know this, but there are growing movements to make this a possibility throughout the mathematical community.  This work is based on the Lean theorem prover, which has attracted significant interest from mathematicians trying to "formalize" and "mechanize" mathematical proofs. 

This repo is an attempt to formalize in Lean some basic convex optimization algorithm proofs. I focus on gradient descent and prove the $O(1/k)$ convergence rate. The main source for the proof is the excellent lecture notes [here](http://www.seas.ucla.edu/~vandenbe/ee236c.html). As far as I know, this is the first formalization of this proof in Lean and perhaps in any theorem prover. But it is totally possible someone has formalized this stuff long ago in Coq or some other framework. 

The proof (as of Dec 2021) only covers functions of scalar inputs (i.e. no vectors). As a beginner to Lean, this was hard enough! I hope to extend the proofs to vector/Hilbert spaces soon. 

I will hopefully be updating the repo regularly as I finish new proofs - pending other commitments. 

Ultimately, the benefits of this project go beyond making the reviewer's life much easier and include:

* Making a search-able database of theorems/results/algorithms/convergence rates. 
* Can write proof-carrying code. You can implement your algorithm in Lean and then also provide a proof that it actually does what it's supposed to do. 
* Reveal errors in previous proofs. 
* Reveal extensions of previous proofs. 

This repo is hopefully a step in this direction. There is still a long way to go. And writing proofs in Lean is really tricky! And has a steep learning curve. 