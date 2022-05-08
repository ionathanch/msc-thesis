Hello! My name is Jonathan Chan and I'm a Master's student at UBC.
I'll be talking about my work on a syntactic model for a sized dependent type theory.

First of all, dependent types are used by a lot of modern theorem provers
that are founded on the types-as-propositions paradigm
where type checking corresponds to checking a proof in some logical system.
To ensure that type checking is decidable and that the logic is consistent,
for the type theories of theorem provers such as Agda or Coq,
they have to ensure that their recursive functions are terminating.

This is currently done using syntactic checks ensuring that the functions are
structurally recursive and recur only on syntactically smaller arguments,
but this is sometimes too restrictive.
Some checks will inline definitions along the way, but then this makes definitions nonmodular,
and even minor syntactic changes can affect whether later functions pass the check.

Instead of these checks, another option is to use a type-based termination checking method
called sized types, where inductive types carry additional size information,
and constructors build inductives with larger sizes.
In fixpoints, recursive calls have to be done on arguments with smaller sizes so that they terminate,
and type checking will guarantee this, with no additional syntactic checking required.

There's a fair amount of relevant past work on sized types falling roughly into three groups,
covering various combinations of dependent types, higher-rank sized types, and bounded size quantification,
but to my knowledge no theoretical work covers all three, so my work seeks to fill this gap
with a higher-rank sized dependent type theory with bounded size quantification.

In short, this is the Generalized Calculus of Constructions with sized types,
naturals, W types, case expressions, and fixpoints.
To show that the theory consistent, I use a syntactic model in extensional CIC, or CIC_E,
which is a standard, well-studied dependent type theory.
The syntactic model is essentially a type-preserving compiler from the source type theory into CIC_E.
With this model, since we know that CIC_E is consistent,
an inconsistency in the source would compile to one in the target,
which would therefore be a contradiction.

In the model, size expressions translate to an inductively-defined representation of (Brouwer) ordinals,
along with a representation of the less-than relation on them,
and naturals and W types translate to their corresponding inductive definitions but parametrized by a Size.
The interesting part of the translation is fixpoints, shown on this slide:
they now translate to applications of well-founded induction on Sizes.

Proving that the translation is type preserving is still ongoing work.
One notable challenge is ensuring that the universe levels of all the inductive types are correct.
Other future work include handling general inductives, coinductives, and an "infinite" size.
If you have any questions or want to learn more, be sure to drop by the SRC discussion session.

Thanks for watching!

Questions:
* Why a syntactic model rather than usual set-theoretic models?
* Why an extensional CIC?
* Why are sizes ordinals and not just naturals?
* Aren't sized types in Agda inconsistent? Does it apply here?
* What's the problem with universe levels and how will you fix it?