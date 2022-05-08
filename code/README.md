# Sized Types Mechanizations and Examples
* Sizes-*.agda: Sized types with three interpretations of infinite sizes:
  * Pair: An infinitely-sized natural is pair of *some* size and a natural of that size.
  * HIT: Infinite sizes are equal to their successors via higher-inductive types.
  * Conat: Sizes are conaturals, with the infinite size as the infinite conatural.
* SizeLoop.agda: An example showing the necessity of semi-continuous sized types from Abel's [dissertation](http://www.cse.chalmers.se/~abela/diss.pdf).
* SizeOrd.agda: An implementation of sizes as generalized Brouwer ordinals, examples with sized W types, and proving well-founded induction for sizes.
* SizeOrd.v: Coq equivalent of the Agda file, with transitivity left as a postulate.
