# A Syntactic Model of Sized Dependent Types

## ???

The types-as-propositions paradigm associates certain type theories with formal logical systems,
and consequently types in those theories with propositions in those logics.
Furthermore, well-typed programs are associated with proofs of the corresponding proposition.
Many dependent type theories, for instance, correspond to higher-order logics,
and having an automated type checker means having the ability to automatically verify proofs.
One must be careful, however, not to allow nonterminating programs,
because they correspond to logical inconsistencies, i.e. proofs of falsehood;
additionally, in dependent type checkers where programs may be evaluated during type checking,
failure to rule out nonterminating programs leads to nonterminating type checking.
Contemporary proof assistants based on dependent type theories, such as Coq, Agda, Lean, Idris,
and many more, typically restrict recursive functions to _structurally-recursive_ ones,
where the argument of recursive calls must be _syntactically_ smaller.
As an example, consider the following function `minus n m` that computes $\min(n - m, 0)$.

```agda
minus : Nat → Nat → Nat
minus Zero m = Zero
minus n Zero = n
minus (Succ n) (Succ m) = minus n m
```

Inuitively, any well-typed call to `minus` is guaranteed to terminate because the recursive call
only occurs on constructor arguments, and the base cases must be reached eventually.
However, we often wish to write terminating functions that aren't necessarily syntactically recursive.
Consider now the following function `div n m` that computes $\lceil\frac{n}{m+1}\rceil$ using `minus`.

```agda
div : Nat → Nat → Nat
div Zero m = Zero
div (Succ n) m = Succ (div (minus n m) m)
```

Despite the fact that `minus` returns a natural no greater than its first argument,
meaning that the first argument of the recursive call to `div` has a smaller magnitude
than the original argument,
the type checker is unable to conclude that this is a terminating function,
because the first argument isn't _syntactically_ smaller (i.e. `n`).
The programmer would have to alter the definition of `minus` to prove this property,
as well as the definition of `div` to use this proof, making writing otherwise simple code burdensome.
Sometimes it would be possible to make the type checker a little more clever by selectively inlining
certain functions that allow the syntactic termination check to pass,
but this is not always possible, and requiring inlining just to pass termination checking is anti-modular.
If inlining `minus` in the body of `div` helped, then we are forced to import its entire definition,
rather than merely its name and type, as is only required for type checking alone.

<!-- Paragraph break -->

A _type-based_ rather than syntactic method of termination checking uses _sized types_ (Hughes 1996),
where a function is guaranteed to terminate simply if it type checks.
To use sized types, we first alter our definition of naturals to take a size expression as a parameter.

```agda
data Nat [α] : Type where
  Zero : ∀β < α. Nat [α]
  Succ : ∀β < α. Nat [β] → Nat [α]
```

The bounded size quantification `∀β < α.` asks for some size `β` strictly smaller than `α`.
So to construct the successor of some natural `n : Nat [s]`, we need a size larger than `s`.
Let `↑s` denote the next size up from `s`.
Then the successor is simply `Succ {↑s} [s] n` (using curly braces for the implicit size parameter).
Next, let us express the fact that `minus` returns a natural no larger than its first argument using sizes,
i.e. that `minus` is in fact _size-preserving_.

```agda
minus : ∀α β. Nat [α] → Nat [β] → Nat [α]
```

Now we are able to write a `div` function that the type checker will accept to be terminating
with just a few more annotations.

```agda
div : ∀α β. Nat [α] → Nat [β] → Nat [α]
div [α] [β] (Zero {α} [γ]) m = Zero {α} [γ]
div [α] [β] (Succ {α} [γ] n) m = Succ {α} [γ] (div [γ] [β] (minus [γ] [β] n m) m)
```

In the second branch, when matching on the first argument of size `α`, we have the successor of `n`,
which itself has size `γ < α`.
Then the call to `minus` returns a natural of size `γ`, which is then passed to the recursive call of `div`.
Type checking passes without problem because the size `γ` of the recursive call is strictly smaller
than the size `α` of the original call to `div`.
More precisely, when expressing recursive functions as fixpoints,
their typing rule and reduction behaviour is the following
(using e[x ↦ e'] to denote substitution of x by e' in e):

```
Γ, α, f : ∀β < α. σ[α ↦ β] ⊢ e : σ
---------------------------------- fix
Γ ⊢ fix f [α] : σ := e : ∀α. σ

(fix f [α] : σ := e) [s] e' ⊳ e[α ↦ s, f ↦ Λβ < s. (fix f [α] : σ := e) [β]] e'
```

A fixpoint is well-typed if the body has the same type under the environment where
the recursive reference to the fixpoint quantifies over a _smaller_ size.
When reducing the fixpoint applied to some size, we substitute in the body the fixpoint bounded by that size.

<!-- Leave the rest of this subsection out if short on space.

`div` as written out above looks a lot more syntactically heavy than the original unsized function,
but if we treat sizes like ordinary terms, then we can apply the same elaboration techniques,
and leave certain sizes as implicit.
For instance, replacing sizes in `div` with $\_$ where they can be inferred,
the function would instead look like the following.

```agda
div : ∀α β. Nat [α] → Nat [β] → Nat [α]
div [_] [_] (Zero {_} [γ]) m = Zero {_} [γ]
div [_] [_] (Succ {_} [_] n) m = Succ {_} [_] (div [_] [_] (minus [_] [_] n m) m)
```

The only size that needs to be implicitly written out is the size argument to the `Zero` constructor;
the remaining ones can all be inferred from the types of the arguments and function calls.

-->

## ???

Once we have a program and correctness proofs about the program, we may wish to compile and run our program.
In Coq and Agda, programs get _extracted_ to OCaml and Haskell code, respectively, which are then compiled.
However, the process of extraction necessarily discards some type information,
since the extraction targets are not dependently typed.
This makes it possible to link our proven-safe program after extraction with unsafe code,
which might cause runtime errors, making all of the work proving it correct in vain.
To ensure that our proofs are preserved and verified even during linking,
we want to compile our code in a _type-preserving_ manner (Bowman, 2018).
The type-based nature of sized types makes it more amenable than syntactic termination checking
to type-preserving compilation of recursive functions.

Traditionally in dependent type theories, there are two mutually-dependent judgements:
the typing judgement, and the (typed) equality judgement.
Equality is used in the following typing rule:

```
Γ ⊢ e : τ
Γ ⊢ τ ≡ σ : Type
---------------- conv
Γ ⊢ e : σ
```

Meanwhile, typing premises are used in various equality rules.
However, the mutual dependency between the judgements greatly complicate proving type preservation of compilers.
As an alternative, type theories with untyped equality are used,
meaning that typing premises do not appear in equality judgements, breaking the mutual dependency.

<!-- Paragraph break -->

The ultimate goal is to define a sized dependent type theory for use as the core calculus of a proof assistant,
and a type-preserving compiler so that we can run the programs about which we prove properties.
This work is merely the modest beginnings of such an endeavour,
starting with showing that we have a suitable type theory to work with.
We therefore seek to prove the logical consistency of a type theory with the following features:

* Dependent types;
* Untyped equality;
* Bounded size quantification (i.e. ∀α. τ); and
* Higher-rank size quantification (i.e. ∀α. (∀β. τ) → σ).

To our knowledge, there is no past theoretical work on a type theory with all four features.
Barthe et al. (2006), Grégoire and Sacchini (2010), Sacchini (2011), and Sacchini (2013)
introduce and prove consistent a lineage of Calculi of (Co)Inductive Constructions (CIC)
with no bounded size quantification and rank-1 (that is, prenex) size quantification.
Meanwhile, Abel (2006), Abel (2010), Abel (2012), and Abel and Pientka (2016) introduce first
higher-rank size quantification followed by bounded size quantification, but in variants of System Fω.
The most recent work on dependent sized types is Abel (2017),
who proves the consistency of a dependent type theory with naturals and higher-rank size quantification.
However, not only does that type theory use typed equality,
but the method by which consistency is proven relies on it as well,
so it cannot easily be extended to suit our needs.

The usual methods of proving consistency involve vastly complex set-theoretic models of the type theory
requiring a lot of work to set up correctly and knowledge of advanced set-theoretic methods.
The majority of Sacchini's dissertation (2011), for instance, is devoted to proving consistency.
Instead of taking the set-theoretic model approach, we define a _syntactic_ model (Boulier et al. 2017),
which is essentially a type-preserving compiler from our source type theory
into a target type theory that is known to be consistent.
If there is such a compiler, then the source type theory must be consistent as well,
for if one could prove an inconsistency in the source,
then its type-preserving interpretation would be a proof of inconsistency in the target, which is a contradiction.
The remainder of this abstract discusses an attempt at a syntactic model of a sized type theory
with all four of the above features in _extensional CIC_,
along with problems with the model that remain to be solved.

## The Syntactic Model

The source language is the Generalized Calclulus of Constructions with definitions (CCω) (Harper and Pollack, 1991) —
that is, a Calculus of Constructions with untyped equality, a cumulative universe hierarchy, and `let` expressions —
extended with bounded and unbounded size quantification, abstraction, and application,
as well as size expressions consisting of size variables, a base size, and the size successor operator `↑·`.
We can add to this fixpoints and inductive types in general, but for the purposes of this discussion we add only fixpoints and two well-known examples:
naturals and the W type.
The target language is the Extensional Calculus of Inductive Constructions (CICᴱ) (Oury, 2005).
Inductive definitions provide us with the expressivity needed to translate naturals, W types, sizes, and their ordering relation,
while extensionality (that is, equality reflection) is a technical requirement of the proofs.

Notice that in our sized definition of the naturals,
we treat its size as if it were a parameter.
This is exactly what we do in the interpretation:
we parametrize inductive definitions by a `Size` inductive type.
Because the source only has base and successor sizes,
it might be tempting to implement `Size` with only these constructors.
While this works for expressing naturals of all sizes,
this doesn't scale to _general_ inductive definitions like the W type,
where a construction might conceptually have an "infinite" number of subconstructions, so to speak.
Taking inspiration from the set-theoretic models where sizes are interpreted as set-theoretic ordinals,
we define `Size` as an inductive similar to type-theoretic ordinals, namely Brouwer ordinals (Kraus et al. 2021).
A `Size` is then either a successor size or a limit size.

```agda
data Size : Type where
  ↑_ : Size → Size
  ⊔_ : {A : Type} → (A → Size) → Size
```

The limit size constructor, given some function `f : A → Size`,
can be thought of as the least upper bound of all the sizes produced by `f`.
In fact, we can define a nonstrict preorder on `Size` that ensures this property.

```agda
data _≤_ : Size → Size → Type where
  mono   : ∀ α β → α ≤ β → ↑ α ≤ ↑ β
  cocone : ∀ β f → (∃[ x ] β ≤ f x) → β ≤ ⊔ f
  limit  : ∀ β f → (∀  x → f x ≤ β) → ⊔ f ≤ β
```

`cocone` asserts that `⊔ f` is an upper bound of sizes returned by `f`,
while `limit` asserts that it a _least_ upper bound;
`mono` is the usual monotonicity of the successor operator with respect to the order.
From this nonstrict preorder, we define the corresponding strict preorder `α < β` simply as `↑ α ≤ β`.
Now we are able to define the interpretation of naturals and the W type in the target language.

```agda
data ℕ (α : Size) : Type where
  zero : ∀ β → β < α → ℕ α
  succ : ∀ β → β < α → ℕ β → ℕ α

data 𝕎 (α : Size) (A : Type) (B : A → Type) : Type where
  sup : ∀ β → β < α → (x : A) → (B x → 𝕎 β A B) → 𝕎 α A B
```

The translation for universes, functions, `let` expressions, and `case` expressions are fairly straightforward.
But what about for fixpoints?
The key insight is that fixpoints no longer correspond to structural induction on some inductive datum,
but instead _well-founded induction_ on `Size`, which we can prove via an _accessibility predicate_.

```agda
data Acc (α : Size) : Type where
  acc : (∀ β → β < α → Acc β) → Acc α

accSize : ∀ α → Acc α
elim : (P : Size → Type) → (∀ α → (∀ β → β < α → P β) → P α) → (∀ α → P α)
```

Intuitively, accessibility of sizes says that there is no infinitely-descending chain of sizes ordered by `<`,
while well-founded induction says that to prove a property about a size,
it suffices to show that it can be proven assuming that it holds for all smaller sizes.
Now consider a fixpoint `fix f [α] : σ := e`, whose type is `∀α. σ`.
If we informally associate `σ` with the first argument `P` of `elim`,
then the type of the fixpoint looks a lot like the return type of `elim`.
In fact, recalling the premise of the fixpoint typing rule,

```
Γ, α, (f : ∀β < α. σ[α ↦ β]) ⊢ e : σ
```

this looks exactly like the second argument type of `elim`.
Formally, we define the translation of a fixpoint as follows,
using `⟦·⟧` to denote the translation of a source term,
completing the translation to target terms.

```
⟦fix f [α] : σ := e⟧ ≝ elim (λα : Size. ⟦σ⟧) (λα : Size. λf : ∀β → β < α → ⟦σ[α ↦ β]⟧. ⟦e⟧)
```

## Problems with the Model and Future Work
