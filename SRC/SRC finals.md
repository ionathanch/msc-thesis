Hello! My name is Jonathan Chan, I'm a Master's student at UBC,
I'll be talking about my work on a syntactic model for a sized dependent type theory.

First of all, dependent types are used by a lot of modern theorem provers
that are founded on the types-as-propositions paradigm
where type checking corresponds to checking a proof in some logical system.
To ensure that the logic is consistent and that type checking is decidable,
for the type theories of theorem provers such as Agda or Coq,
they have to ensure that their recursive functions are terminating.

This is currently done using syntactic checks ensuring that the functions are
structurally recursive and recur only on syntactically smaller arguments,
but this is sometimes too restrictive.
Some checks will inline definitions along the way, but then this makes definitions nonmodular,
and even minor syntactic changes can affect whether later functions pass the check.

Instead of these checks, another option is to use a type-based termination checking method called *sized types*,
where inductive types carry additional size information,
and constructors build inductives with larger sizes.
In fixpoints, recursive calls have to be done on arguments with smaller sizes to guarantee termination;
there's no other syntactic checks required,
and they no longer depend on the bodies of prior definitions,
only on their types.
The trick here is that functions can now be typed to be *size-preserving*,
while proving similar properties without sized types would be quite a large burden on the user in comparison.

There's a fair amount of relevant past work on sized types which I've divided into three groups,
based on their coverage of dependent types, higher-rank sized types,
and bounded size quantification.
The first row here introduces sized types to the Calculus of Inductive Constructions,
but with only prenex size quantification,
which means for instance that you can't pass around a size-preserving function.
The second row introduces higher-rank size quantification *and* bounded size quantification,
which is a feature that ensures that pattern-matching with sized types is consistent
and eliminates the need for complex monotonicity checks,
but this is only for System Fω.
Finally, the third row proves normalization of a higher-rank sized dependent type theory with naturals,
but without bounded size quantification.

To my knowledge, there is no formal model of a type theory with all three of these features,
while all these and more are implemented in Agda.
My goal is to fill this gap and show that a type theory with all three can in fact be consistent.

I start with the Generalized Calculus of Constructions with sized types,
naturals, W types, case expressions, and fixpoints.
To show its consistency, I use a syntactic model in extensional CIC,
which is a standard, well-studied dependent type theory.
The syntactic model is essentially a type-preserving compiler from the source type theory into CIC.
Since an inconsistency in the source would compile to one in the target,
and we know what CIC is consistent,
if the model is correct (meaning type-preserving),
the source must be consistent as well.

In the model, sizes translate to an inductively-defined notation of (Brouwer) ordinals and their order,
and we can show that sizes are indeed well-founded with respect to that order using a standard accessibility predicate.
This is important because it turns out that fixpoints in the source,
regardless of what they recur on,
translate to applications of well-founded induction on Sizes.
I only have naturals and W types,
which translate to their corresponding inductive definitions but parametrized by a Size,
but in principle the translation should apply to any inductive definition.

Proving that the translation is type preserving is still ongoing work.
One notable challenge is ensuring that the universe levels of all the inductive types are correct.
Other future work include handling inductives in general, coinductives,
and some notion of the "infinite" size.

That's all for my talk, and thanks for watching!