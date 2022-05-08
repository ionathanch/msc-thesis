ASSUME:
* All binding variables are unique.
* For each binding α < s, α* is a fresh term variable in the target only.
* ≡-trans and ≡-cong will be used implicitly and liberally
  in equational-style proofs over equivalence.

# Source Metatheorems

## Environments and Typing

Lemma (renaming):
  (1) If Φ; Γ₁(x: σ)Γ₂ ⊢ e : τ then Φ; Γ₁(y: σ)Γ₂ ⊢ e[x ↦ y] : τ[x ↦ y].
  (2) If Φ₁(α)Φ₂; Γ ⊢ e : τ then Φ₁(β)Φ₂; Γ ⊢ e[α ↦ β] : τ[α ↦ β].
  (3) If Φ₁(α < s)Φ₂; Γ ⊢ e : τ then Φ₁(β < s)Φ₂; Γ ⊢ e[α ↦ β] : τ[α ↦ β].
Proof: Left as tedious exercise.

Lemma (size well-formedness in subsizing): If Φ ⊢ r ⩽ s, then Φ ⊢ r and Φ ⊢ s.
Proof: By induction on the derivation of Φ ⊢ r ⩽ s.
  Case ⩽-var: Φ ⊢ α̂ ⩽ s.
    Since (α < s) ∈ Γ, we have Φ ⊢ α̂.
    Since ⊢ Φ, by cons-size< we have Φ ⊢ s.
  Cases ⩽-refl, ⩽-base, ⩽-suc: Trivial.
  Case ⩽-trans: Φ ⊢ s₁ ⩽ s₂  Φ ⊢ s₂ ⩽ s₃
                -------------------------.
                Φ ⊢ s₁ ⩽ s₃
    IHs: Φ ⊢ s₁, Φ ⊢ s₂, and Φ ⊢ s₃.
    Trivial by first and last IHs.

Lemma (well-formedness of environments):
  (1) If Φ ⊢ Γ, then ⊢ Φ is a subderivation.
  (2) If Φ ⊢ Γ₁Γ₂, then Φ ⊢ Γ₁ is a subderivation.
  (3) If Φ ⊢ Γ and (x: τ) ∈ Γ then Φ; Γ ⊢ τ : U for some U is a subderivation.
  (4) If Φ; Γ ⊢ e : τ, then Φ ⊢ Γ is a subderivation.
Proof (1): Trivial by induction on the derivation of Φ ⊢ Γ.
Proof (2): Trivial if Γ₂ is empty; otherwise,
  by straightforward induction on the derivation of Φ ⊢ Γ₁Γ₂.
Proof (3): Trivial by induction on the derivation of Φ ⊢ Γ.
Proof (4): By straightforward induction on the derivation of Φ; Γ ⊢ e : τ.

Lemma (well-typedness of types): If Φ; Γ ⊢ e : τ, then Φ; Γ ⊢ τ : U for some U.
Proof: By induction on the derivation of Φ; Γ ⊢ e : τ.
  Case conv: Direct by premise.
  Case var: By well-formedness of Γ.
  Case univ, pi, forall, forall<, sigma, eq, nat, W: By rule univ.
  Case lam, slam, slam<, refl: By rules pi, forall, forall<, eq using the appropriate IH.
  Case fst, snd: By inversion on the IH.
  Case zero, succ: By size well-formedness in subsizing using the premises and rule nat.
  Case sup: By size well-formedness in subsizing, the appropriate premises, and rule W.
  Case fix: By the appropriate premise and rule forall.
  Case app, let, sapp, sapp<, pair, J, match-nat, match-sup:
    [TODO: Luo 3.2.7, depends on substitutivity: Luo 3.2.6]

## Confluence and Subject Reduction

Theorem (confluence): If Φ; Γ ⊢ e ⊳* e₁ and Φ; Γ ⊢ e ⊳* e₂ then there is some e' such that Φ; Γ ⊢ e₁ ⊳* e' and Φ; Γ ⊢ e₂ ⊳* e'.
Proof: [TODO: Luo 3.1.1]

Theorem (subject reduction):
  (1) If Φ; Γ ⊢ e: τ and Φ; Γ ⊢ e ⊳ e' then Φ; Γ ⊢ e': τ.
  (2) If Φ; Γ ⊢ e: τ and Φ; Γ ⊢ e ⊳* e' then Φ; Γ ⊢ e': τ.
Proof: [TODO: Luo 3.2.8]

## Subtyping and Inversion

Lemma (transitivity of term ordering): If e₁ ⊑ e₂ and e₂ ⊑ e₃ then e₁ ⊑ e₃.
Proof: By induction on the derviation of e₁ ⊑ e₂ and e₂ ⊑ e₃.
  Case ⊑-refl, ℛ or ℛ, ⊑-refl for any rule ℛ: Holds trivially by ℛ.
  Case ⊑-prop, ⊑-type: Holds by ⊑-prop.
  Case ⊑-type, ⊑-type: Holds by ⊑-type.
  Cases ⊑-pi or ⊑-forall or ⊑-forall< or ⊑-sigma on both sides:
    Holds by the given rule using the IH(s).

Lemma (confluence up to term ordering): If e₁ ⊑ e₂ and Φ; Γ ⊢ e₁ ⊳* e₁' then e₁' ⊑ e₂' for some Φ; Γ ⊢ e₂ ⊳* e₂'.
Proof: By induction on the derivation of e₁ ⊑ e₂.
  Case ⊑-refl: Trivial by ⊑-refl, letting e₂' ≝ e₁'.
  Case ⊑-prop, ⊑-type: Trivial by ⊑-prop and ⊑-type since Prop and Type can only reduce to themselves.
  Case ⊑-pi:        τ₁ ⊑ τ₂
             ---------------------.
             Πx: σ. τ₁ ⊑ Πx: σ. τ₂
    Suppose Φ; Γ ⊢ Πx: σ. τ₁ ⊳ Πx: σ'. τ₁'.
    Then Φ; Γ ⊢ σ ⊳* σ' and Φ; Γ(x: σ') ⊢ τ₁'.
    IH: τ₁' ⊑ τ₂' where Φ; Γ(x: σ') ⊢ τ₂ ⊳* τ₂'.
    By ⊳*-cong, Φ; Γ ⊢ Πx: σ. τ₂ ⊳* Πx: σ'. τ₂',
    and Πx: σ'. τ₁' ⊑ Πx: σ'. τ₂' by the IH.
  Case ⊑-forall, ⊑-forall<, ⊑-sigma: By similar arguments to ⊑-pi.
Corollary: If e₁ ⊑ e₂ and Φ; Γ ⊢ e₂ ⊳* e₂' then e₁' ⊑ e₂' for some Φ; Γ ⊢ e₁ ⊳* e₁'
  by symmetry to the above argument.

Lemma (transitivity of subtyping): If Φ; Γ ⊢ τ₁ ≼ τ₂ and Φ; Γ ⊢ τ₂ ≼ τ₃ then Φ; Γ ⊢ τ₁ ≼ τ₃.
Proof: By inversion on the subtyping judgements, we have the following:
  - Φ; Γ ⊢ τ₁ ⊳* τ₁'
  - Φ; Γ ⊢ τ₂ ⊳* τ₂₁
  - Φ; Γ ⊢ τ₂ ⊳* τ₂₂
  - Φ; Γ ⊢ τ₃ ⊳* τ₃'
  - τ₁' ⊑ τ₂₁
  - τ₂₂ ⊑ τ₃'
  By confluence, there is some τ₂' such that Φ; Γ ⊢ τ₂₁ ⊳* τ₂' and Φ; Γ ⊢ τ₂₂ ⊳* τ₂'.
  By confluence up to term ordering, we then have
  - Φ; Γ ⊢ τ₁' ⊳* τ₁'' and τ₁'' ⊑ τ₂'
  - Φ; Γ ⊢ τ₃' ⊳* τ₃'' and τ₂' ⊑ τ₃''
  By ⊳*-trans, we then have Φ; Γ ⊢ τ₁ ⊳* τ₁'' and Φ; Γ τ₃ ⊳* τ₃''.
  Finally, by transitivity of term ordering and by ≼-red, we have Φ; Γ ⊢ τ₁ ≼ τ₃.

Lemma (inversion): Given a syntactic form e and a typing rule ℛ ending in that form
  (i.e. any rule excluding conv), if 𝒟 is a derivation ending in Φ; Γ ⊢ e : τ
  and 𝒥ᵢ are judgement forms in the premises of ℛ,
  then there are derivations 𝒟ᵢ ending in 𝒥ᵢ such that ℛ builds a derivation ending in Φ; Γ ⊢ e : σ,
  and Φ; Γ ⊢ σ ≼ τ holds.
Proof: By induction on the derivation of Φ; Γ ⊢ e : τ.
  Case ℛ: The premises of the given derivation are the desired ones,
    and Φ; Γ ⊢ τ ≼ τ holds by ⊑-refl and ≼-red.
  Case conv: Φ; Γ ⊢ e : σ  Φ; Γ ⊢ τ : U  Φ; Γ ⊢ σ : U  Φ; Γ ⊢ σ ≼ τ
             ------------------------------------------------------.
             Φ; Γ ⊢ e : τ
    IH: There are derivations 𝒟ᵢ that build Φ; Γ ⊢ e : σ' such that Φ; Γ ⊢ σ' ≼ σ.
    The derivations from the IH are the desired ones,
    with Γ ⊢ σ' ≼ τ by transitivity.

# Target Metatheorems

Lemma (function extensionality): If Γ ⊢ f : (x: τ) → σ, Γ ⊢ g : (x: τ) → σ, and Γ ⊢ h : (x: τ) → f x == g x,
  then Γ ⊢ f ≡ g : (x: τ) → σ.
Proof: Using ≡-cong and ≡-trans,
  f ≡ λx: τ. f x (by ≡-β, ≡-η)
    ≡ λx: τ. let h' := h x in f x (by ≡-ζ)
    ≡ λx: τ. let h' := h x in g x (by ≡-δ, ≡-reflect)
    ≡ λx: τ. g x (by ≡-ζ)
    ≡ g (by ≡-β, ≡-η)
    : (x: τ) → σ.
Corollary: If Γ ⊢ h: (x: τ) → f x == g x then Γ ⊢ refl f: f == g,
  by function extensionality, ≼-eq, ≡-conv, ≼-conv and the conv rule.

Lemma (substitutivity of subtyping): If we have the following:
- Γ₁(x: σ)Γ₂ ⊢ τ₁ ≼ τ₂
- Γ₁ ⊢ e : σ
then Γ₁(Γ₂[x ↦ e]) ⊢ τ₁[x ↦ e] ≼ τ₂[x ↦ e] holds.
Proof: [TODO: Luo 3.2.6]

Lemma (environment subtyping): Suppose Γ₁ ⊢ σ₁ ≼ σ₂.
- If Γ₁(x: σ₂)Γ₂ ⊢ e : τ then Γ₁(x: σ₁)Γ₂ ⊢ e : τ.
- If Γ₁(x: σ₂)Γ₂ ⊢ τ₁ ≼ τ₂ then Γ₁(x: σ₁)Γ₂ ⊢ τ₁ ≼ τ₂.
- If Γ₁(x: σ₂)Γ₂ ⊢ e₁ ≡ e₂ : τ then Γ₁(x: σ₁)Γ₂ ⊢ e₁ ≡ e₂ : τ
Proof: By mutual induction on the typing and subtyping derivations.
  Case var: ⊢ Γ  (x: σ₂) ∈ Γ
            ----------------.
            Γ ⊢ x : σ₂
    By inversion on ⊢ Γ and rules var and conv.
  Case conv: Γ ⊢ τ : U
             Γ ⊢ e : τ'
             Γ ⊢ τ' ≼ τ
             ----------.
             Γ ⊢ e : τ
    IH: Γ ⊢ e: τ',
        Γ ⊢ τ: U, and
        Γ ⊢ τ' ≼ τ, where (x: σ₁) ∈ Γ.
    By rule conv.
  Case ≡-δ: (x := e) ∈ Γ  (x: σ₂) ∈ Γ
            -----------------------.
            Γ ⊢ x ≡ e : σ₂
    By ≡-δ and ≡-conv.
  All other cases: Direct by induction hypotheses; left as exercise.
  (Note that this is Luo 3.2.5.)

Lemma (equivalence well-typedness): If Γ ⊢ e₁ ≡ e₂ : τ then Γ ⊢ eᵢ : τ.
Proof: [TODO]

Lemma (inversion): Given a syntactic form e and a typing rule ℛ ending in that form
  (i.e. any rule excluding conv), if 𝒟 is a derivation ending in Γ ⊢ e : τ
  and 𝒥ᵢ are judgement forms in the premises of ℛ,
  then there are derivations 𝒟ᵢ ending in 𝒥ᵢ such that ℛ builds a derivation ending in Γ ⊢ e : σ,
  and Γ ⊢ σ ≼ τ holds.
Proof: By induction on the derivation of Γ ⊢ e : τ.
  Case ℛ: The premises of the given derivation are the desired ones,
    and Γ ⊢ τ ≼ τ holds by ≡-refl and ≼-conv.
  Case conv: Γ ⊢ e : σ  Γ ⊢ τ : U  Γ ⊢ σ : U  Γ ⊢ σ ≼ τ
             ------------------------------------------.
             Γ ⊢ e : τ
    IH: There are derivations 𝒟ᵢ that build Γ ⊢ e : σ' such that Γ ⊢ σ' ≼ σ.
    The derivations from the IH are the desired ones,
    with Γ ⊢ σ' ≼ τ by transitivity.

# Compositionality Lemmas

Lemma (term substitution for sizes): ⟦s⟧[x ↦ ⟦e⟧] = ⟦s⟧.
Proof: By induction on the structure of s.
  Case ∘: Trivial.
  Case α: Trivial since α ≠ x.
  Case ŝ:
    ⟦ŝ⟧[x ↦ ⟦e⟧]
    = suc ⟦s⟧[x ↦ ⟦e⟧]
    = suc ⟦s⟧ by the IH
    = ⟦ŝ⟧.
Corollary: ⟦s⟧[α* ↦ e] = ⟦s⟧ since α* must be fresh term variable.

Lemma (compositionality for sizes): ⟦s⟧[α ↦ ⟦r⟧] = ⟦s[α ↦ r]⟧.
Proof: By induction on the structure of s.
  Case ∘: Trivial.
  Case β: If β = α, both sides are ⟦r⟧; otherwise, both sides are β.
  Case ŝ:
    ⟦ŝ⟧[α ↦ ⟦r⟧]
    = suc ⟦s⟧[α ↦ ⟦r⟧]
    = suc ⟦s[α ↦ r]⟧ by the IH
    = ⟦ŝ[α ↦ r]⟧.

Lemma (term substitution for subsizing): If Φ ⊢ s₁ ⩽ s₂ ⇝ e, then e[x ↦ ⟦e'⟧] = e,
  where x is a term variable from the source.
Proof: By induction on the derivation of Φ ⊢ s₁ ⩽ s₂ ⇝ e.
  Case var≤: Φ ⊢ β̂ ⩽ s ⇝ β* where (β < s) ∈ Φ.
    Trivial since β* is a fresh term variable in the target only and β* ≠ x.
  Cases refl≤, base≤, suc≤: Trivial by term substitution for sizes.
  Case trans≤: Φ ⊢ s₁ ⩽ s₂ ⇝ e₁  Φ ⊢ s₂ ⩽ s₃ ⇝ e₂
               -----------------------------------------.
               Φ ⊢ s₁ ⩽ s₃ ⇝ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂
    IHs: e₁[x ↦ ⟦e'⟧] = e₁ and e₂[x ↦ ⟦e'⟧] = e₂.
    Then we have
      (trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂)[x ↦ ⟦e'⟧]
      = trans≤ ⟦s₁⟧[x ↦ ⟦e'⟧] ⟦s₂⟧[x ↦ ⟦e'⟧] ⟦s₃⟧[x ↦ ⟦e'⟧] e₁[x ↦ ⟦e'⟧] e₂[x ↦ ⟦e'⟧]
      = trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂
    by above lemma and the IHs.

Lemma (bounded compositionality for subsizing):
  If Φ₁(α < r')Φ₂ ⊢ s ⩽ r ⇝ e≤ and Φ₁ ⊢ ŝ' ⩽ r' ⇝ e≤',
  then Φ₁(Φ₂[α ↦ s']) ⊢ s[α ↦ s'] ⩽ r[α ↦ s'] ⇝ e≤[α ↦ ⟦s'⟧, α* ↦ e≤'].
Proof: By induction on the derivation of Φ₁(α < r')Φ₂ ⊢ ŝ ⩽ r ⇝ e≤.
  Case var≤: Φ₁(α < r')Φ₂ ⊢ β̂ ⩽ r ⇝ β* where (β < r) ∈ Φ₁(α < r')Φ₂.
    Subcase β ≠ α:
      If (β < r) ∈ Φ₁, then α ∉ FV(r), so
        Φ₁(Φ₂[α ↦ s']) ⊢ β̂[α ↦ s'] ⩽ r[α ↦ s'] ⇝ β*[α ↦ ⟦s'⟧, α* ↦ e≤']
        ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ β̂ ⩽ r ⇝ β* holds.
      If (β < r) ∈ Φ₂, we have (β < r[α ↦ s']) ∈ Φ₂[α ↦ s'], so
        Φ₁(Φ₂[α ↦ s']) ⊢ β̂[α ↦ s'] ⩽ r[α ↦ s'] ⇝ β*[α ↦ ⟦s'⟧, α* ↦ e≤']
        ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ β̂ ⩽ r[α ↦ s'] ⇝ β* holds.
    Subcase β = α:
      Since bound variables are unique, we must have r = r'.
      Then Φ₁(Φ₂[α ↦ s']) ⊢ α̂[α ↦ s'] ⩽ r[α ↦ s'] ⇝ α*[α ↦ ⟦s'⟧, α* ↦ e≤'] ⇒ Φ ⊢ s' ⩽ r' ⇝ e≤' holds.
  Case base≤, refl≤, suc≤: Trivial by compositionality for sizes.
  Case trans≤: Φ₁(α < r')Φ₂ ⊢ s₁ ⩽ s₂ ⇝ e≤₁  Φ₁(α < r')Φ₂ ⊢ s₂ ⩽ s₃ ⇝ e≤₂
               -----------------------------------------------------------.
               Φ₁(α < r')Φ₂ ⊢ s₁ ⩽ s₃ ⇝ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e≤₁ e≤₂
    IHs: Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₂[α ↦ s'] ⇝ e≤₁[α ↦ ⟦s'⟧, α* ↦ e≤] and
         Φ₁(Φ₂[α ↦ s']) ⊢ s₂[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ e≤₂[α ↦ ⟦s'⟧, α* ↦ e≤].
    Then Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ (trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e≤₁ e≤₂)[α ↦ ⟦s'⟧, α* ↦ e≤]
      ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ trans≤ ⟦s₁[α ↦ s']⟧ ⟦s₂[α ↦ s']⟧ ⟦s₃[α ↦ s']⟧ e≤₁[α ↦ ⟦s'⟧, α* ↦ e≤] e≤₂[α ↦ ⟦s'⟧, α* ↦ e≤]
      holds by the IHs and compositionality for sizes.

Lemma (unbounded compositionality for subsizing):
  If Φ₁(α)Φ₂ ⊢ s ⩽ r ⇝ e≤ then Φ₁(Φ₂[α ↦ s']) ⊢ s[α ↦ s'] ⩽ r[α ↦ s'] ⇝ e≤[α ↦ ⟦s'⟧].
Proof: By induction on the derivation of Φ(α) ⊢ s ⩽ r ⇝ e≤.
  Case var≤: Φ₁(α)Φ₂ ⊢ β̂ ⩽ r ⇝ r* where (β < r) ∈ Φ₁(α)Φ₂.
    Note that since bound variables are unique, we cannot have that β = α.
    If (β < r) ∈ Φ₁, then α ∉ FV(r), so
      Φ₁(Φ₂[α ↦ s']) ⊢ β̂[α ↦ s'] ⩽ r[α ↦ s'] ⇝ β*[α ↦ ⟦s'⟧]
      ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ β̂ ⩽ r ⇝ β* holds.
    If (β < r) ∈ Φ₂, then (β < r[α ↦ s']) ∈ Φ₂[α ↦ s'], so
      Φ₁(Φ₂[α ↦ s']) ⊢ β̂[α ↦ s'] ⩽ r[α ↦ s'] ⇝ β*[α ↦ ⟦s'⟧]
      ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ β̂ ⩽ r[α ↦ s'] ⇝ β* holds.
  Case base≤, refl≤, suc≤: Trivial by compositionality for sizes.
  Case trans≤: Φ₁(α)Φ₂ ⊢ s₁ ⩽ s₂ ⇝ e≤₁ Φ₁(α)Φ₂ ⊢ s₂ ⩽ s₃ ⇝ e≤₂
               -------------------------------------------------.
               Φ₁(α)Φ₂ ⊢ s₁ ⩽ s₃ ⇝ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e≤₁ e≤₂
    IHs: Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₂[α ↦ s'] ⇝ e≤₁[α ↦ ⟦s'⟧] and
         Φ₁(Φ₂[α ↦ s']) ⊢ s₂[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ e≤₂[α ↦ ⟦s'⟧].
    Then Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ (trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e≤₁ e≤₂)[α ↦ ⟦s'⟧]
      ⇒ Φ₁(Φ₂[α ↦ s']) ⊢ s₁[α ↦ s'] ⩽ s₃[α ↦ s'] ⇝ trans≤ ⟦s₁[α ↦ s']⟧ ⟦s₂[α ↦ s']⟧ ⟦s₃[α ↦ s']⟧ e≤₁[α ↦ ⟦s'⟧] e≤₂[α ↦ ⟦s'⟧]
      holds by the IHs and compositionality for sizes.

Lemma: If Φ; Γ ⊢ e : τ then ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧,
  where x is a term variable from the source.
Proof: By induction on the derivation of Φ; Γ ⊢ e : τ.
  Case conv: Φ; Γ ⊢ e : σ  Φ; Γ ⊢ σ ≼ τ  Φ; Γ ⊢ σ : U  Φ; Γ ⊢ τ : U
             ------------------------------------------------------.
             Φ; Γ ⊢ e : τ
    IH: ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧.
    Trivial by IH.
  Case var: Φ; Γ ⊢ y : τ.
    If y ≠ x, then ⟦y⟧[x ↦ ⟦e'⟧] =  y   = ⟦y[x ↦ e']⟧.
    If y = x, then ⟦x⟧[x ↦ ⟦e'⟧] = ⟦e'⟧ = ⟦x[x ↦ e']⟧.
  Case univ: Trivial.
  Case pi: Φ; Γ ⊢ σ : U₁  Φ; Γ(y: σ) ⊢ τ : U₂
           ----------------------------------.
           Φ; Γ ⊢ Πy: σ. τ : rule(U₁, U₂)
    IHs: ⟦σ⟧[x ↦ ⟦e'⟧] = ⟦σ[x ↦ e']⟧ and
         ⟦τ⟧[x ↦ ⟦e'⟧] = ⟦τ[x ↦ e']⟧.
    Then we have
      ⟦Πy: σ. τ⟧[x ↦ ⟦e'⟧]
      = Πy: ⟦σ⟧[x ↦ ⟦e'⟧]. ⟦τ⟧[x ↦ ⟦e'⟧]
      = Πy: ⟦σ[x ↦ e']⟧. ⟦τ[x ↦ e']⟧ by IHs
      = ⟦(Πy: σ. τ)[x ↦ e']⟧.
  Cases lam, sigma: Similar to proof for case pi.
  Case app: Φ; Γ ⊢ e₁ : Πy: σ. τ  Φ; Γ ⊢ e₂ : σ
            -----------------------------------.
            Φ; Γ ⊢ e₁ e₂ : τ[y ↦ e₁]
    IHs: ⟦e₁⟧[x ↦ ⟦e'⟧] = ⟦e₁[x ↦ e']⟧ and
         ⟦e₂⟧[x ↦ ⟦e'⟧] = ⟦e₂[x ↦ e']⟧.
    Then we have
      ⟦e₁ e₂⟧[x ↦ ⟦e'⟧]
      = ⟦e₁⟧[x ↦ ⟦e'⟧] ⟦e₂⟧[x ↦ ⟦e'⟧]
      = ⟦e₁[x ↦ e']⟧ ⟦e₂[x ↦ e']⟧ by IHs
      = ⟦(e₁ e₂)[x ↦ e']⟧.
  Case let: Φ; Γ ⊢ e₁ : σ  Φ; Γ(y: σ)(y := e₁) ⊢ e₂ : τ
            -------------------------------------------.
            Φ; Γ ⊢ let y := e₁ in e₂ : τ[y ↦ e₁]
    IHs: ⟦e₁⟧[x ↦ ⟦e'⟧] = ⟦e₁[x ↦ e']⟧ and
         ⟦e₂⟧[x ↦ ⟦e'⟧] = ⟦e₂[x ↦ e']⟧.
    Then we have
      ⟦let y := e₁ in e₂⟧[x ↦ ⟦e'⟧]
      = let y := ⟦e₁⟧[x ↦ ⟦e'⟧] in ⟦e₂⟧[x ↦ ⟦e'⟧]
      = let y := ⟦e₁[x ↦ e']⟧ in ⟦e₂[x ↦ e']⟧ by the IHs
      = ⟦(let y := e₁ in e₂)[x ↦ e']⟧.
  Case pair: Similar to proof for cases pi (for the type annotation) and app (for the pair elements).
  Case right: Φ; Γ ⊢ e : Σy: σ. τ
              -------------------------.
              Φ; Γ ⊢ π₂ e : τ[y ↦ π₁ e]
    IH: ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧.
    Then we have
      ⟦π₂ e⟧[x ↦ ⟦e'⟧]
      = π₂ ⟦e⟧[x ↦ ⟦e'⟧]
      = π₂ ⟦e[x ↦ e']⟧ by the IH
      = ⟦(π₂ e)[x ↦ e']⟧.
  Case left: Similar to proof for case right.
  Case forall<: Φ; Γ ⊢ s  Φ(α < s); Γ ⊢ τ
                -------------------------.
                Φ; Γ ⊢ ∀α < s. τ
    IH: ⟦τ⟧[x ↦ ⟦e'⟧] = ⟦τ[x ↦ e']⟧.
    Then we have
      ⟦∀α < s. τ⟧[x ↦ ⟦e'⟧]
      = Πα: Size. Πα*: suc α ≤ ⟦s⟧[x ↦ ⟦e'⟧]. ⟦τ⟧[x ↦ ⟦e'⟧]
      = Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ[x ↦ e']⟧ by the IH and term substitution for sizes
      = ⟦(∀α < s. τ)[x ↦ e']⟧.
  Case slam<: Similar to proof for case forall<.
  Cases forall, slam: Similar to proof for cases forall<, slam< without needing term substitution for sizes.
  Case sapp<: Φ; Γ ⊢ e : ∀α < r. τ  Φ ⊢ ŝ ⩽ r
              -------------------------------.
              Φ; Γ ⊢ e [s] : τ[α ↦ s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[x ↦ e'] = ⟦e[x ↦ e']⟧.
    Let Φ ⊢ ŝ ⩽ r ⇝ e≤.
    Then we have
      ⟦e [s]⟧[x ↦ ⟦e'⟧]
      = ⟦e⟧[x ↦ ⟦e'⟧] ⟦s⟧[x ↦ ⟦e'⟧] e≤[x ↦ ⟦e'⟧]
      = ⟦e[x ↦ e']⟧ ⟦s⟧ e≤ by the IH and term substitution for sizes and subsizing
      = ⟦e[x ↦ e'] [s]⟧
      = ⟦(e [s])[x ↦ e']⟧
  Case sapp: Similar to proof for case sapp< without needing term substitution for subsizing.
  Case W: Similar to proof for case pi, using term substitution for sizes.
  Case nat: Trivial using term substitution for sizes.
  Case sup: Φ; Γ ⊢ r̂ ⩽ s  Φ; Γ ⊢ σ : U₁  Φ; Γ(y: σ) ⊢ τ : U₂
            Φ; Γ ⊢ e₁ : σ  Φ; Γ ⊢ e₂ : τ[y ↦ e₁] → 𝕎y: σ. τ [r]
            -----------------------------------------------------.
            Φ; Γ ⊢ sup {𝕎y: σ. τ [s]} [r] e₁ e₂ : 𝕎y: σ. τ [s]
    IHs: (1) ⟦σ⟧[x ↦ ⟦e'⟧] = ⟦σ[x ↦ e']⟧,
         (2) ⟦τ⟧[x ↦ ⟦e'⟧] = ⟦τ[x ↦ e']⟧,
         (3) ⟦e₁⟧[x ↦ ⟦e'⟧] = ⟦e₁[x ↦ e']⟧, and
         (4) ⟦e₂⟧[x ↦ ⟦e'⟧] = ⟦e₂[x ↦ e']⟧.
    Let Φ ⊢ r̂ ⩽ s ⇝ e≤.
    Then we have
      (6) ⟦λy: σ. τ⟧[x ↦ ⟦e'⟧]
          = λy: ⟦σ⟧[x ↦ ⟦e'⟧]. ⟦τ⟧[x ↦ ⟦e'⟧] by definition of the translation and substitution
          = λy: ⟦σ[x ↦ e']⟧. ⟦τ[x ↦ e']⟧ by (1) and (2)
          = ⟦(λy: σ. τ)[x ↦ e']⟧ by definitions again.
    Finally, we have
      ⟦sup {𝕎y: σ. τ [s]} [r] e₁ e₂⟧[x ↦ ⟦e'⟧]
      = sup ⟦s⟧[x ↦ ⟦e'⟧] ⟦σ⟧[x ↦ ⟦e'⟧] ⟦λx: σ. τ⟧[x ↦ ⟦e'⟧] ⟦r⟧[x ↦ ⟦e'⟧] e≤[x ↦ ⟦e'⟧] ⟦e₁⟧[x ↦ ⟦e'⟧] ⟦e₂⟧[x ↦ ⟦e'⟧]
      = sup ⟦s⟧ ⟦σ[x ↦ e']⟧ ⟦(λx: σ. τ)[x ↦ e']⟧ ⟦r⟧ e≤ ⟦e₁[x ↦ e']⟧ ⟦e₂[x ↦ e']⟧
        by (1), (3), (4), (6), and term substitution for sizes and subsizing
      = ⟦(sup {𝕎y: σ. τ [s]} [r] e₁ e₂)[x ↦ e']⟧
  Cases zero and succ: Similar to proof for case sup.
  Case match-nat: Φ; Γ ⊢ e : N [s]  Φ; Γ(y: N [s]) ⊢ P : U
                  Φ(α < s); Γ ⊢ ez : P[y ↦ zero {ℕ [s]} [α]]
                  Φ(β < s); Γ(z: N [β]) ⊢ es : P[y ↦ succ {ℕ [s]} [β] z]
                  ------------------------------------------------------------------------.
                  Γ ⊢ match e return λy.P with (zero [α] ⇒ ez) (succ [β] ⇒ es) : P [y ↦ e]
    IHs: ⟦P⟧[x ↦ ⟦e'⟧] = ⟦P[x ↦ e']⟧,
         ⟦ez⟧[x ↦ ⟦e'⟧] = ⟦ez[x ↦ e']⟧, and
         ⟦es⟧[x ↦ ⟦e'⟧] = ⟦es[x ↦ e']⟧.
    By ≈-cong and ≈-trans,
      ⟦match e return λy.P with (zero [α] ⇒ ez) (succ [β] ⇒ es)⟧[x ↦ e']
      = match ⟦e⟧[x ↦ ⟦e'⟧] return λ().y.⟦P⟧[x ↦ ⟦e'⟧] with (zero α α* ⇒ ⟦ez⟧[x ↦ ⟦e'⟧]) (succ β β* ⇒ ⟦es⟧[x ↦ ⟦e'⟧])
      = match ⟦e[x ↦ e']⟧ return λ().y.⟦P[x ↦ e']⟧ with (zero α α* ⇒ ⟦ez[x ↦ e']⟧) (succ β β* ⇒ ⟦es[x ↦ e']⟧) by the IHs
      = ⟦(match e return λx.P with (zero [α] ⇒ ez) (succ [β] ⇒ es))[x ↦ e']⟧.
  Case match-sup: Similar to proof for case match-nat.
  Case ind, constr: Trivial.
  Case match: data X [α] ΔP : ΔI → U where Δ
              Φ; Γ ⊢ e : X [s] p... eᵢ...
              Φ; Γ(ΔI[α ↦ s][ΔP ↦ p...])(x: X [s] p... dom(ΔI)) ⊢ P : U'
              ∀(c: τc) ∈ Δ, τc[α ↦ s][ΔP ↦ p...] ≡ ∀β < s. Δc → X [s] p... e'ᵢ...
              Φ(β < s); ΓΔc ⊢ ec : P[ΔI ↦ e'ᵢ...][x ↦ c [s] p... [β] dom(Δc)]
              ----------------------------------------------------------------------------------------.
              Φ; Γ ⊢ match e return λ(dom(ΔI)).x.P with (c [β] dom(Δc) ⇒ ec)... : P[ΔI ↦ eᵢ...][x ↦ e]
    IHs: ⟦P⟧[x ↦ ⟦e'⟧] = ⟦P[x ↦ e']⟧,
         ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧, and
         for each constructor c, ⟦ec⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧.
    By ≈-cong and ≈-trans,
      ⟦match e return λ(dom(ΔI)).x.P with (c [β] dom(Δc) ⇒ ec)...⟧[x ↦ ⟦e'⟧]
      = match ⟦e⟧[x ↦ ⟦e'⟧] return λ(dom(ΔI)).x.⟦P⟧[x ↦ ⟦e'⟧] with (c β β* dom(Δc) ⇒ ⟦ec⟧[x ↦ ⟦e'⟧])...
      = match ⟦e[x ↦ e']⟧ return λ(dom(ΔI)).x.⟦P[x ↦ e']⟧ with (c β β* dom(Δc) ⇒ ⟦ec[x ↦ e']⟧)...
        by the IHs
      = ⟦(match e return λ(dom(ΔI)).x.P with (c β dom(Δc) ⇒ ec)...)[x ↦ e']⟧.
  Case fix: Φ(α); Γ ⊢ σ : U  Φ(α); Γ(f: ∀β < α. σ[α ↦ β]) ⊢ e : σ
            -----------------------------------------------------.
            Γ ⊢ fix f [α]: σ := e : ∀α. σ
    IHs: ⟦σ⟧[x ↦ ⟦e'⟧] = ⟦σ[x ↦ e']⟧ and
         ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧.
    By ≈-cong and ≈-trans,
      ⟦fix f [α]: σ := e⟧[x ↦ ⟦e'⟧]
      = elim (λα: Size. ⟦σ⟧[x ↦ ⟦e'⟧]) (λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ[α ↦ β]⟧[x ↦ ⟦e'⟧]. ⟦e⟧[x ↦ ⟦e'⟧])
      = elim (λα: Size. ⟦σ[x ↦ e']⟧) (λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ[α ↦ β][x ↦ e']⟧. ⟦e[x ↦ e']⟧) by IHs
      = ⟦(fix f [α]: σ := e)[x ↦ ⟦e'⟧]⟧.

Lemma: If Φ₁(α < r)Φ₂; Γ ⊢ e : τ and Φ₁ ⊢ ŝ ⩽ r ⇝ e≤,
  then ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] = ⟦e[α ↦ s]⟧.
Proof: By induction on the derivation of Γ ⊢ e : τ.
  We implicitly use the fact that ⟦s'⟧[α* ↦ e≤] = ⟦s'⟧ for any s throughout.
  Case var: Φ₁(α < r)Φ₂; Γ ⊢ y : τ. Trivial since α* is fresh.
  Cases univ, pi, lam, sigma, app, let, pair, left, right:
    Similar to the proof of compositionality above since these don't involve sizes.
  Cases match-nat, match-sup, match, and fix:
    Also similar, despite involving sizes, since substitution is never done on a translation of a size or a subsizing judgement.
  Case slam<: Φ₁(α < r)Φ₂ ⊢ s  Φ₁(α < r)Φ₂; Γ(β < s') ⊢ e : τ
              ----------------------------------------------.
              Φ₁(α < r)Φ₂; Γ ⊢ Λβ < s'. e : ∀β < s'. τ
    IH: ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] = ⟦e[α ↦ s]⟧.
    Then we have
      ⟦Λβ < s'. e⟧[α ↦ ⟦s⟧, α* ↦ e≤]
      = λβ: Size. λβ*: suc β ≤ ⟦s'⟧[α ↦ ⟦s⟧, α* ↦ e≤]. ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤]
      = λβ: Size. λβ*: suc β ≤ ⟦s'[α ↦ s]⟧. ⟦e[α ↦ s]⟧ by the IH and compositionality for sizes
      = ⟦Λβ < s'[α ↦ s]. e[α ↦ s]⟧
      = ⟦(Λβ < s'. e)[α ↦ s]⟧.
  Case forall<: Similar to the proof of case slam<.
  Cases forall, slam: Similar to the proof of cases forall< and slam< without needing compositionality for sizes.
  Case sapp<: Φ₁(α < r)Φ₂; Γ ⊢ e : ∀β < r'. τ  Φ₁(α < r)Φ₂; Γ ⊢ ŝ' ⩽ r'
              ---------------------------------------------------------.
              Φ₁(α < r)Φ₂; Γ ⊢ e [s'] : τ[β ↦ s']
    IH: ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] = ⟦e[α ↦ s]⟧.
    Let Φ₁(α < r)Φ₂ ⊢ ŝ' ⩽ r' ⇝ e≤' and Φ₁(Φ₂[α ↦ s]) ⊢ ŝ'[α ↦ s] ⩽ r'[α ↦ s] ⇝ e≤'[α ↦ s, α* ↦ e≤]
    by bounded compositionality for subsizing.
    Then we have
      ⟦e [s']⟧[α ↦ ⟦s⟧, α* ↦ e≤]
      = ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] ⟦s'⟧[α ↦ ⟦s⟧, α* ↦ e≤] e≤'[α ↦ ⟦s⟧, α* ↦ e≤]
      = ⟦e[α ↦ s]⟧ ⟦s'[α ↦ s]⟧ e≤'[α ↦ ⟦s⟧, α* ↦ e≤] by the IH and compositionality for sizes
      = ⟦e[α ↦ s] [s'[α ↦ s]]⟧
      = ⟦(e [s'])[α ↦ s]⟧.
  Cases sapp, W, nat: Similar to the proof of case slam without needing bounded compositionality for subsizing.
  Case succ: Φ₁(α < r)Φ₂; Γ ⊢ r̂' ⩽ s'  Φ₁(α < r)Φ₂; Γ ⊢ e : N [r']
             -----------------------------------------------------.
             Φ₁(α < r)Φ₂; Γ ⊢ succ {ℕ [s']} [r'] e
    IH: ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] = ⟦e[α ↦ s]⟧.
    Let Φ₁(α < r)Φ₂ ⊢ r̂' ⩽ s' ⇝ e≤' and Φ₁(Φ₂[α ↦ s]) ⊢ r̂'[α ↦ s] ⩽ s'[α ↦ s] ⇝ e≤'[α ↦ ⟦s⟧, α* ↦ e≤]
    by bounded compositionality for subsizing.
    Then we have
      ⟦succ {ℕ [s']} [r'] e⟧[α ↦ ⟦s⟧, α* ↦ e≤]
      = succ ⟦s'⟧[α ↦ ⟦s⟧, α* ↦ e≤] ⟦r'⟧[α ↦ ⟦s⟧, α* ↦ e≤] e≤'[α ↦ ⟦s⟧, α* ↦ e≤] ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤]
      = succ ⟦s'[α ↦ s]⟧ ⟦r'[α ↦ s]⟧ e≤'[α ↦ ⟦s⟧, α* ↦ e≤] ⟦e[α ↦ s]⟧ by the IH and compositionality for sizes
      = ⟦succ {ℕ [s'[α ↦ s]]} [r'[α ↦ s]] e[α ↦ s]⟧
      = ⟦(succ {ℕ [s']} [r'] e)[α ↦ s]⟧.
  Cases zero, sup: Similar to proof for case succ.

Lemma: If Φ₁(α)Φ₂; Γ ⊢ e : τ, then ⟦e⟧[α ↦ ⟦s⟧] = ⟦e[α ↦ s]⟧.
Proof: By induction on the derivation of Γ ⊢ e : τ.
  The proofs for every case is exactly like those for the above,
  using unbounded compositionality for subsizing instead of bounded compositionality.

Lemma (term compositionality for environments): If Φ ⊢ Γ, then ⟦Γ⟧[x ↦ ⟦e⟧] = ⟦Γ[x ↦ e]⟧.
Proof: By induction on the derivation of Φ ⊢ Γ.
  Case cons-nil: Trivial.
  Case cons-ass: Φ ⊢ Γ  Φ; Γ ⊢ τ : U
                 -------------------.
                 Φ ⊢ Γ(y: τ)
    IH: ⟦Γ⟧[x ↦ ⟦e⟧] = ⟦Γ[x ↦ e]⟧.
    By compositionality, ⟦τ⟧[x ↦ ⟦e⟧] = ⟦τ[x ↦ e]⟧.
    Then ⟦Γ(y: τ)⟧[x ↦ ⟦e⟧] = ⟦Γ(y: τ)[x ↦ e]⟧ holds by the IH and cons-ass.
  Case cons-def: Φ ⊢ Γ  Φ; Γ ⊢ e' : τ
                 --------------------.
                 Φ ⊢ Γ(y := e')
    IH: ⟦Γ⟧[x ↦ ⟦e⟧] = ⟦Γ[x ↦ e]⟧.
    By compositionality, ⟦e'⟧[x ↦ ⟦e⟧] = ⟦e'[x ↦ e]⟧.
    Then ⟦Γ(y := e')⟧[x ↦ ⟦e⟧] = ⟦Γ(y := e')[x ↦ e]⟧ holds by the IH and cons-def.

Lemma (size compositionality for environments): If Φ₁(α)Φ₂ ⊢ Γ, then ⟦Γ⟧[α ↦ ⟦s⟧] = ⟦Γ[α ↦ s]⟧.
  Case cons-nil: Trivial.
  Case cons-ass: Φ ⊢ Γ  Φ; Γ ⊢ τ : U
                 -------------------.
                 Φ ⊢ Γ(x: τ)
    IH: ⟦Γ⟧[α ↦ ⟦s⟧] = ⟦Γ[α ↦ s]⟧.
    By compositionality, ⟦τ⟧[α ↦ ⟦s⟧] = ⟦τ[α ↦ s]⟧.
    Then ⟦Γ(x: τ)⟧[α ↦ ⟦s⟧] = ⟦Γ(x: τ)[α ↦ s]⟧ holds by the IH and cons-ass.
  Case cons-def: Φ ⊢ Γ  Φ; Γ ⊢ e : τ
                 -------------------.
                 Φ ⊢ Γ(x := e)
    IH: ⟦Γ⟧[α ↦ ⟦s⟧] = ⟦Γ[α ↦ s]⟧.
    By compositionality, ⟦e⟧[α ↦ ⟦s⟧] = ⟦e[α ↦ s]⟧.
    Then ⟦Γ(x := e)⟧[α ↦ ⟦s⟧] = ⟦Γ(x := e)[α ↦ s]⟧ holds by the IH and cons-def.

# Equivalence of Reduction

Lemma: Given the following:
  - Φ; Γ ⊢ e ⊳ e'
  - Φ; Γ ⊢ e : τ
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧
  we have that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ≡ ⟦e'⟧ : ⟦τ⟧,
  where Φ; Γ ⊢ e': τ by subject reduction.

Proof: By cases on the derivation of Φ; Γ ⊢ e ⊳ e'.
  Case ⊳δ: Φ; Γ ⊢ x ⊳ e where (x := e) ∈ Γ and (x: τ) ∈ Γ.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦x⟧ ≡ ⟦e⟧ : ⟦τ⟧.
    Trivial by preservation of environment membership and ≡-δ.
  Case ⊳β: Φ; Γ ⊢ (λx: σ. e) e' ⊳ e[x ↦ e'].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦σ⟧. ⟦e⟧) ⟦e'⟧ ≡ ⟦e[x ↦ e']⟧ : ⟦τ⟧.
    By inversion on ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦σ⟧. ⟦e⟧) ⟦e'⟧ : ⟦τ⟧, we have that
    - ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦σ⟧. ⟦e⟧) ⟦e'⟧ : τ'[x ↦ ⟦e'⟧],
    - ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦e⟧ : Πx: σ'. τ',
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e'⟧ : σ', and
    - ⟦Φ⟧⟦Γ⟧ ⊢ τ'[x ↦ ⟦e'⟧] ≼ ⟦τ⟧.
    By inversion yet again on ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦e⟧ : Πx: σ'. τ', we have that
    - ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦e⟧ : Πx: ⟦σ⟧. ⟦τ''⟧,
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U,
    - ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦e⟧ : ⟦τ''⟧, and
    - ⟦Φ⟧⟦Γ⟧ ⊢ Πx: ⟦σ⟧. ⟦τ''⟧ ≼ Πx: σ'. τ'.
    By inversion on ⟦Φ⟧⟦Γ⟧ ⊢ Πx: ⟦σ⟧. ⟦τ''⟧ ≼ Πx: σ'. τ', we must have
    - ⟦σ⟧ = σ' and
    - ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦τ''⟧ ≼ τ'.
    Then by ≡-β, we have ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦σ⟧. ⟦e⟧) ⟦e'⟧ ≡ ⟦e⟧[x ↦ ⟦e'⟧] : ⟦τ''⟧[x ↦ ⟦e'⟧].
    By substitutivity of subtyping, we have ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ''⟧[x ↦ ⟦e'⟧] ≼ τ'[x ↦ ⟦e'⟧].
    By ≼-trans, we have ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ''⟧[x ↦ ⟦e'⟧] ≼ ⟦τ⟧.
    Finally, by compositionality and ≡-conv, we have the goal.
  Case ⊳ζ: Φ; Γ ⊢ let x : σ := e₁ in e₂ ⊳ e₂[x ↦ e₁].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ ≡ ⟦e₂[x ↦ e₁]⟧ : ⟦τ⟧.
    By inversion on ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ : ⟦τ⟧, we have that
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ : ⟦σ⟧
    - ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧)(x := ⟦e₁⟧) ⊢ ⟦e₂⟧ : τ'
    - ⟦Φ⟧⟦Γ⟧ ⊢ τ'[x ↦ ⟦e₁⟧] ≼ ⟦τ⟧
    By ≡-ζ, we have ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ ≡ ⟦e₂⟧[x ↦ ⟦e₁⟧] : τ'[x ↦ ⟦e₁⟧].
    By ≡-conv, we have ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ ≡ ⟦e₂⟧[x ↦ ⟦e₁⟧] : ⟦τ⟧.
    Finally, by compositionality, we have the goal.
  Cases ⊳πᵢ, ⊳ρ: By inversion on the target typing derivation, ≼-trans, ≡-conv,
    and ≡-πᵢ, ≡-ρ, respectively, following pattern of above.
  Case ⊳ϛ: Φ; Γ ⊢ (Λα.e) [s] ⊳ e[α ↦ s].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. ⟦e⟧) ⟦s⟧ ≡ ⟦e[α ↦ s]⟧ : ⟦τ⟧.
    By inversion on ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. ⟦e⟧) ⟦s⟧ : ⟦τ⟧, we have that
    - ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. ⟦e⟧ : Πα: Size. τ'
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦s⟧ : Size
    - ⟦Φ⟧⟦Γ⟧ ⊢ τ'[α ↦ ⟦s⟧] ≼ ⟦τ⟧
    By inversion yet again on ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. ⟦e⟧ : Πα: Size. τ', we have that
    - ⟦Φ⟧⟦Γ⟧(α: Size) ⊢ ⟦e⟧ : τ''
    - ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. τ'' ≼ Πα: Size. τ'
    By inversion on ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. τ'' ≼ Πα: Size. τ', we must have that ⟦Φ⟧⟦Γ⟧(α: Size) ⊢ τ'' ≼ τ'.
    By ≡-β, we have ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. ⟦e⟧) ⟦s⟧ ≡ ⟦e⟧[α ↦ ⟦s⟧] : τ''[α ↦ ⟦s⟧].
    By substitutivity of subtyping, we have ⟦Φ⟧⟦Γ⟧ ⊢ τ''[α ↦ ⟦s⟧] ≼ τ'[α ↦ ⟦s⟧].
    By ≼-trans, we have ⟦Φ⟧⟦Γ⟧ ⊢ τ''[α ↦ ⟦s⟧] ≼ ⟦τ⟧.
    Finally, by compositionality and ≡-conv, we have the goal.
  Case ⊳ϛ<: Φ; Γ ⊢ (Λα < r. e) [s] ⊳ e[α ↦ s].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. λα*: suc α ≤ ⟦r⟧. ⟦e⟧) ⟦s⟧ e≤ ≡ ⟦e[α ↦ s]⟧ : ⟦τ⟧,
      where Φ ⊢ ŝ ⩽ r ⇝ e≤.
    As above: inversion thrice, yielding
      ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. λα*: suc α ≤ ⟦r⟧. ⟦e⟧) ⟦s⟧ e≤ ≡ ⟦e⟧[α ↦ ⟦s⟧][α* ↦ e≤] : τ'''[α ↦ ⟦s⟧][α* ↦ e≤]
    then substitutivity of subtyping and ≼-trans to yield
      ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. λα*: suc α ≤ ⟦r⟧. ⟦e⟧) ⟦s⟧ e≤ ≡ ⟦e⟧[α ↦ ⟦s⟧][α* ↦ e≤] : ⟦τ⟧
    and finally the goal using compositionality and ≡-conv.
  Case ⊳ι: Φ; Γ ⊢ match c [s] p... [r] e... return _ with ...(c [β] z... ⇒ ec)... ⊳ ec[β, z... ↦ r, e...].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match c ⟦s⟧ ⟦p⟧... ⟦r⟧ e≤ ⟦e⟧... return _ with ...(c β β* z... ⇒ ⟦ec⟧)... ≡ ⟦ec[β, z... ↦ r, e...]⟧ : ⟦τ⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    As above: inversion of match, of every app for each constructor argument, and of constr,
    then substitutivity of subtyping, ≼-trans, compositionality, and ≡-conv to yield the goal.
  <!--
  Case ⊳ι (zero): Φ; Γ ⊢ match (zero {ℕ [s]} [r]) return λx.P with (zero [α] ⇒ ez) (succ [β] z ⇒ es) ⊳ ez[α ↦ s].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match (zero ⟦s⟧ ⟦r⟧ e≤) return λ().x.⟦P⟧ with (zero α α* ⇒ ⟦ez⟧) (succ β β* z ⇒ ⟦es⟧) ≡ ⟦ez[α ↦ r]⟧ : ⟦τ⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
  Case ⊳ι (succ): Φ; Γ ⊢ match (succ {ℕ [s]} [r] e) return λx.P with (zero [α] ⇒ ez) (succ [β] z ⇒ es) ⊳ ez[α ↦ s, z ↦ e].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match (succ ⟦s⟧ ⟦r⟧ e≤ ⟦e⟧) return λ().x.⟦P⟧ with (zero α α* ⇒ ⟦ez⟧) (succ β β* z ⇒ ⟦es⟧) ≡ ⟦ez[β ↦ r, z ↦ e]⟧ : ⟦τ⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
  Case ⊳ι (sup): Φ; Γ ⊢ match (sup {𝕎x: σ. τ [s]} [r] e₁ e₂) return λx.P with (sup [α] z₁ z₂ ⇒ e) ⊳ e[α ↦ r, z₁ ↦ e₁, z₂ ↦ e₂].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match (sup ⟦s⟧ ⟦σ⟧ ⟦λx: σ. τ⟧ ⟦r⟧ e≤ ⟦e₁⟧ ⟦e₂⟧) return λx.⟦P⟧ with (sup α α* z₁ z₂ ⇒ ⟦e⟧) ≡ ⟦e[α ↦ r, z₁ ↦ e₁, z₂ ↦ e₂]⟧ : ⟦τ⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
  Case ⊳ι: Φ; Γ ⊢ match c [s] p... [r] e... return _ with ...(c [β] z... ⇒ ec)... ⊳ ec[β, z... ↦ r, e...].
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match c ⟦s⟧ ⟦p⟧... ⟦r⟧ e≤ ⟦e⟧... return _ with ...(c β β* z... ⇒ ⟦ec⟧)... ≡ ⟦ec[β, z... ↦ r, e...]⟧ : ⟦τ⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    By compositionality, we have
      ⟦ec⟧[β, β*, z... ↦ ⟦r⟧ e≤ ⟦e⟧...]
      = ⟦ec[β ↦ r]⟧[z... ↦ ⟦e⟧...]
      = ⟦ec[β ↦ r][z... ↦ e...]⟧.
  -->
  Case ⊳μ: Φ; Γ ⊢ (fix f [α]: σ := e) [s] t₁ ... tₙ (c e₁ ... eₘ) ⊳ e[α ↦ s, f ↦ Λβ < s. (fix f [α]: σ := e) [β]] t₁ ... tₙ (c e₁ ... eₘ).
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ elim (λα: Size. ⟦σ⟧) (λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧) ⟦s⟧ ⟦t₁⟧ ... ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧ ≡ ⟦e[α ↦ s, f ↦ Λβ < s. (fix f [α]: σ := e) [β]]⟧ ⟦t₁⟧ ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧ : ⟦τ'⟧.
    For notational convenience, let P ≝ λα: Size. ⟦σ⟧ and g ≝ λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧,
    and recall that elim P g s = elimAcc s (accessible s) where
      acc< ≝ λ β: Size. λ β*: suc β ≤ ⟦s⟧. λ access: Acc ⟦s⟧.
        match access return λ()._.Acc β with (acc p ⇒ p β β*),
      elimAcc ≝ fix₁ elimAccRec: (α: Size) → Acc α → P α :=
          λα: Size. λaccess: Acc α.
            g α (λβ: Size. λβ*: suc β ≤ α.
              elimAccRec β (acc< β β* access)).
    By repeated inversion on ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧ ⟦t₁⟧ ... ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧ : ⟦τ⟧,
    we know that ⟦tᵢ⟧ and ⟦c e₁ ... eₘ⟧ are well-typed.
    To show the goal, by ≡-cong and compositionality, it then suffices to show that
      ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧ ≡ ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elim P g β] : τ',
    where ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧ : τ' by inversion.
    Proceeding again by inversion, we have that
    - ⟦Φ⟧⟦Γ⟧ ⊢ elim : (P: Size → Type) → ((α: Size) → ((β: Size) → suc β ≤ α → P) → P α) → (α: Size) → P α (by definition of elim)
    - ⟦Φ⟧⟦Γ⟧ ⊢ P : Size → Type
    - ⟦Φ⟧⟦Γ⟧ ⊢ g : (α: Size) → ((β: Size) → suc β ≤ α → P) → P α
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦s⟧ : Size
    - ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧ : P ⟦s⟧
    - ⟦Φ⟧⟦Γ⟧ ⊢ P ⟦s⟧ ≼ τ'
    With liberal use of ≡-cong, ≡-sym, and ≡-trans, we have that
      ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧
      ≡ elimAcc ⟦s⟧ (accessible ⟦s⟧)
        by definition of elim
      ≡ g ⟦s⟧ (λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (acc< β β* (accessible ⟦s⟧)))
        by ≡-μ and ≡-β
      ≡ ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (acc< β β* (accessible ⟦s⟧))]
        by further ≡-β
      : P ⟦s⟧ (†)
    Knowing that ⟦s⟧ is well-typed, we have that
      ⟦Φ⟧⟦Γ⟧(β: Size)(β*: suc β ≤ ⟦s⟧) ⊢ accessible ⟦s⟧ : Acc ⟦s⟧.
    Furthermore, by the definition of acc<, we can conclude that
      ⟦Φ⟧⟦Γ⟧(β: Size)(β*: suc β ≤ ⟦s⟧) ⊢ acc< β β* (accessible ⟦s⟧) : Acc β.
    Then using the well-typed accIsProp and equality reflection,
    we can conclude that (accessible β) and (acc< β β* (accessible ⟦s⟧)) are equivalent
    in the environment with β and β*.
      ⟦Φ⟧⟦Γ⟧(β: Size)(β*: suc β ≤ ⟦s⟧) ⊢ acc< β β* (accessible ⟦s⟧)
      ≡ let p := accIsProp β (accessible β) (acc< β β* (accessible ⟦s⟧))
        in acc< β β* (accessible ⟦s⟧)
        by ≡-ζ
      ≡ let p := accIsProp β (accessible β) (acc< β β* (accessible ⟦s⟧))
        in accessible β
        by ≡-reflect
      ≡ accessible β
        by ≡-ζ
      : Acc β
    Then continuing (†), we have that
      ⟦Φ⟧⟦Γ⟧ ⊢ elim P g ⟦s⟧
      ≡ ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (accessible β)]
        by equivalence of the two elements of Acc β
      ≡ ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elim P g β]
        by definition of elim
      : P ⟦s⟧
    Finally, we have the new goal by ≡-conv.

# Equivalence of (reflexive, transitive, congruent) Closure of Reduction and Conversion

Lemma (equivalence of closure of reduction): Given the following:
  - Φ; Γ ⊢ e ⊳* e'
  - Φ; Γ ⊢ e : τ
  - Φ; Γ ⊢ τ : U
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧
  we have that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ≡ ⟦e'⟧ : ⟦τ⟧,
  where Φ; Γ ⊢ e' : τ by subject reduction.

Proof: By lexicographical induction on the derivations of Φ; Γ ⊢ e ⊳* e' and of Φ; Γ ⊢ e : τ.
  (That is, the IH can also be called on subderivations of Φ; Γ ⊢ e : τ
  so long as Φ; Γ ⊢ e ⊳* e' is unchanged.)
  Case ⊳*-refl: Φ; Γ ⊢ e ⊳* e. Trivial by ≡-refl.
  Case ⊳*-trans: Φ; Γ ⊢ e ⊳ e'  Γ ⊢ e' ⊳* e''
                 ----------------------------.
                 Φ; Γ ⊢ e ⊳* e''
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e'⟧ ≡ ⟦e''⟧ : ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ≡ ⟦e''⟧ : ⟦τ⟧.
    By equivalence of reduction, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ≡ ⟦e'⟧ : ⟦τ⟧.
    Then the goal holds by ≡-trans.
  Case ⊳*-cong: Consider congruence for functions as an example.
      Φ; Γ ⊢ σ₁ ⊳* σ₂  Φ; Γ(x: σ₁) ⊢ e₁ ⊳* e₂
      ---------------------------------------.
      Φ; Γ ⊢ λx: σ₁. e₁ ⊳* λx: σ₂. e₂
    By induction on Φ; Γ ⊢ λx: σ₁. e₁ : τ, we have two possible cases.
    Case lam: Φ; Γ ⊢ σ₁ : U  Φ; Γ(x: σ₁) ⊢ e₁ : τ₁
              ------------------------------------,
              Φ; Γ ⊢ λx: σ₁. e₁ : Πx: σ₁. τ₁
      where τ = Πx: σ₁. τ₁.
      By type preservation, we have
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ₁⟧ : ⟦U⟧ and
      - ⟦Φ⟧⟦Γ⟧(x: ⟦σ₁⟧) ⊢ ⟦e₁⟧ : ⟦τ₁⟧.
      Then the IH gives us
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ₁⟧ ≡ ⟦σ₂⟧ : ⟦U⟧ and
      - ⟦Φ⟧⟦Γ⟧(x: ⟦σ₁⟧) ⊢ ⟦e₁⟧ ≡ ⟦e₂⟧ : ⟦τ₁⟧.
      Finally, by ≡-cong and the definition of ⟦τ⟧, we have
        ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ₁⟧. ⟦e₁⟧ ≡ λx: ⟦σ₂⟧. ⟦e₂⟧ : Πx: ⟦σ₁⟧. ⟦τ₁⟧.
    Case conv: Φ; Γ ⊢ λx: σ₁. e₁ : σ
               Φ; Γ ⊢ τ : U
               Φ; Γ ⊢ σ : U
               Φ; Γ ⊢ σ ≼ τ
               ---------------------,
               Φ; Γ ⊢ λx: σ₁. e₁ : τ
      where e = λx: σ₁. e₁.
      By type preservation and preservation of subtyping, we have
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦λx: σ₁. e₁⟧ : ⟦σ⟧,
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : ⟦U⟧,
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : ⟦U⟧, and
      - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ ≼ ⟦τ⟧.
      Then the IH gives us ⟦Φ⟧⟦Γ⟧ ⊢ ⟦λx: σ₁. e₁⟧ ≡ ⟦λx: σ₂. e₂⟧ : ⟦σ⟧.
      Finally, by ≡-conv, we have ⟦Φ⟧⟦Γ⟧ ⊢ ⟦λx: σ₁. e₁⟧ ≡ ⟦λx: σ₂. e₂⟧ : ⟦τ⟧.
    Other cases of congruence proceed similarly,
    making use of compositionality as needed.

Lemma (equivalence of conversion): Given the following:
  - Φ; Γ ⊢ e₁ ≈ e₂
  - Φ; Γ ⊢ e₁ : τ
  - Φ; Γ ⊢ e₂ : τ
  - Φ; Γ ⊢ τ : U
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ : ⟦τ⟧
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : ⟦τ⟧
  we have that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≡ ⟦e₂⟧ : ⟦τ⟧.

Proof: By cases on the derivation of Γ ⊢ e₁ ≈ e₂. (I mean there's only one case.)
  Case ≈-red: Φ; Γ ⊢ e₁ ⊳* e
              Φ; Γ ⊢ e₂ ⊳* e
              --------------.
              Φ; Γ ⊢ e₁ ≈ e₂
    Using ≡-sym and ≡-trans,
    ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≡ ⟦e⟧  (by equivalence of closure of reduction)
                  ≡ ⟦e₂⟧ (by equivalence of closure of reduction).
                  : ⟦τ⟧

# Preservation of Subtyping

Lemma (subtyping of term ordering): Given the following:
  - τ₁ ⊑ τ₂
  - Φ; Γ ⊢ τ₁: U₁
  - Φ; Γ ⊢ τ₂: U₂
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧: U'₁
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₂⟧: U'₂
  we have that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.
Proof: By induction on the derivation of Φ; Γ ⊢ τ₁ ⊑ τ₂.
  Case ⊑-refl: τ ⊑ τ.
    By ≡-refl and ≼-conv using the hypothesis that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧: U' for some U'.
  Case ⊑-prop, ⊑-type: Trivial.
  Case ⊑-pi:        τ₁ ⊑ τ₂
             ---------------------.
             Πx: σ. τ₁ ⊑ Πx: σ. τ₂
    IH: ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.
    By inversion on well-typedness of Πx: σ. τᵢ and of ⟦Πx: σ. τᵢ⟧,
    we have that for some U'', U''ᵢ, U'''ᵢ,
    - Φ; Γ(x: σ) ⊢ τᵢ: U''ᵢ
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧: U''
    - ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦τᵢ⟧: U'''ᵢ
    By ≡-refl, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ ≡ ⟦σ⟧: U'''.
    Then by ≼-pi and the IH, we have ⟦Φ⟧⟦Γ⟧ ⊢ Πx: ⟦σ⟧. ⟦τ₁⟧ ≼ Πx: ⟦σ⟧. ⟦τ₂⟧.
  Case ⊑-forall:     τ₁ ⊑ τ₂
                 ---------------.
                 ∀α. τ₁ ⊑ ∀α. τ₂
    IH: ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.
    By inversion on well-typedness of ∀α. τᵢ and of ⟦∀α. τᵢ⟧,
    we have that for some U''ᵢ and U'''ᵢ,
    - Φ(α); Γ ⊢ τᵢ: U''ᵢ
    - ⟦Φ⟧⟦Γ⟧ ⊢ Size: U''
    - ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦τᵢ⟧: U'''ᵢ
    By ≡-refl, ⟦Φ⟧⟦Γ⟧ ⊢ Size ≡ Size : U''.
    Then by ≼-pi and the IH, we have ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. ⟦τ₁⟧ ≼ Πα: Size. ⟦τ₂⟧.
  Case ⊑-forall<:        τ₁ ⊑ τ₂
                 -----------------------.
                 ∀α < s. τ₁ ⊑ ∀α < s. τ₂
    IH: ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.
    By inversion on well-typedness of ∀α < s. τᵢ and of ⟦∀α < s. τᵢ⟧,
    we have that for some U''ᵢ and U'''ᵢ,
    - Φ(α < s); Γ ⊢ τᵢ: U''ᵢ
    - ⟦Φ⟧⟦Γ⟧ ⊢ Size: U''
    - ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ suc ≤ ⟦s⟧: U'''
    - ⟦Φ⟧(α: Size)(α*: suc ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦τᵢ⟧: U'''ᵢ
    By ≡-refl, ⟦Φ⟧⟦Γ⟧ ⊢ Size ≡ Size : U'' and
    ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ suc α ≤ ⟦s⟧ ≡ suc α ≤ ⟦s⟧ : U'''.
    Then by ≼-pi twice and the IH, we have
    ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ₁⟧ ≼ Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ₂⟧.
  Case ⊑-sigma:     σ₁ ⊑ σ₂  τ₁ ⊑ τ₂
                -----------------------.
                Σx: σ₁. τ₁ ⊑ Σx: σ₂. τ₂
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ₁⟧ ≼ ⟦σ₂⟧ and
         ⟦Φ⟧(x: σ₁)⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.
    By inversion on well-typedness of Σx: σᵢ. τᵢ and of ⟦Σx: σᵢ. τᵢ⟧,
    we have that for some ,
    - Φ; Γ ⊢ σᵢ: U''ᵢ
    - Φ; Γ(x: σᵢ) ⊢ τᵢ: U''ᵢ
    - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σᵢ⟧: U'''ᵢ
    - ⟦Φ⟧⟦Γ⟧(x: ⟦σᵢ⟧) ⊢ ⟦τᵢ⟧: U'''ᵢ
    By environment subtyping and the first IH, ⟦Φ⟧⟦Γ⟧(x: ⟦σ₁⟧) ⊢ ⟦τ₂⟧: U'''₂.
    Then by ≼-sigma and the IHs, we have ⟦Φ⟧⟦Γ⟧ ⊢ Σx: ⟦σ₁⟧. ⟦τ₁⟧ ≼ Σx: ⟦σ₂⟧. ⟦τ₂⟧.

Lemma (preservation of subtyping): Given the following:
  - Φ; Γ ⊢ τ₁ ≼ τ₂
  - Φ; Γ ⊢ τ₁ : U
  - Φ; Γ ⊢ τ₂ : U
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ : ⟦U⟧
  - ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₂⟧ : ⟦U⟧
  we have that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.

Proof: By cases on the derivation of Γ ⊢ τ₁ ≼ τ₂. (I mean there's only one case.)
  Case ≼-red: Φ; Γ ⊢ τ₁ ⊳* σ₁
              Φ; Γ ⊢ τ₂ ⊳* σ₂
              Φ; Γ ⊢ σ₁ ⊑ σ₂
              ---------------.
              Φ; Γ ⊢ τ₁ ≼ τ₂
    By equivalence of closure of reduction, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τᵢ⟧ ≡ ⟦σᵢ⟧ : ⟦U⟧.
    By subject reduction, Φ; Γ ⊢ σᵢ : U.
    By equivalence well-typedness, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σᵢ⟧ : ⟦U⟧.
    Then by subtyping of term ordering, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ₁⟧ ≼ ⟦σ₂⟧.
    Finally, by ≡-sym, ≼-conv, and ≼-trans, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.

# Preservation of Environment Membership

Lemma: Suppose Φ ⊢ Γ.
  (1) If (x: τ) ∈ Γ then (x: ⟦τ⟧) ∈ ⟦Γ⟧;
  (2) If (x := e) ∈ Γ then (x := ⟦e⟧) ∈ ⟦Γ⟧;
  (3) If (α) ∈ Φ then (α: Size) ∈ ⟦Φ⟧;
  (4) If (α < s) ∈ Φ then (α: Size) ∈ ⟦Φ⟧ and (α*: suc α ≤ ⟦s⟧) ∈ ⟦Φ⟧, and
  (5) dom(Γ) = dom(⟦Γ⟧) and dom(Φ) ⊆ dom(⟦Φ⟧).
Proof: Straightforward induction on the derivations of Φ ⊢ Γ and ⊢ Φ.

# Type Preservation

Lemma (preservation of sizes):
  (1) If ⊢ Φ then ⊢ ⟦Φ⟧, and
  (2) If Φ ⊢ s then ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
Proof: By simultaneous induction on the derivations of ⊢ Φ and Φ ⊢ s.

  SIZE ENVIRONMENT WELL-FORMEDNESS CASES
  Case nil: Trivial.
  Case cons-size: ⊢ Φ
                  ------.
                  ⊢ Φ(α)
    IH: ⊢ ⟦Φ⟧.
    ⊢ ⟦Φ⟧(α: Size) holds by the IH and cons-ass via ind.
  Case cons-size<: ⊢ Φ  Φ ⊢ s
                   ----------.
                   ⊢ Φ(α < s)
    IHs: ⊢ ⟦Φ⟧ and ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    ⊢ ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧) holds by the IHs and cons-ass via ind.

  SIZE WELL-FORMEDNESS CASES
  Case ∘: ⊢ Φ
          -----.
          Φ ⊢ ∘
    IH: ⊢ ⟦Φ⟧.
    ⟦Φ⟧ ⊢ base : Size holds by inspection of the definition of base,
    using the IH and constr, among other rules.
  Case α: ⊢ Φ
          (α) ∈ Φ or (α < s) ∈ Φ
          ----------------------.
          Φ ⊢ α
    IH: ⊢ ⟦Φ⟧.
    In either case, (α : Size) ∈ ⟦Φ⟧ holds by preservation of environment membership,
      so ⟦Φ⟧ ⊢ α : Size holds by var and the IH.
  Case ŝ: Φ ⊢ s
          -----.
          Φ ⊢ ŝ
    IH: ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    ⟦Φ⟧ ⊢ suc ⟦s⟧ : Size holds trivially by the IH and constr.

Lemma (preservation of subsizing): If Φ ⊢ r ⩽ s ⇝ e then ⟦Φ⟧ ⊢ e : ⟦r⟧ ≤ ⟦s⟧.
Proof: By induction on the derivation of Φ ⊢ r ⩽ s ⇝ e.
  Case var≤: ⊢ Φ  (β < s) ∈ Φ
             ----------------.
             Φ ⊢ β̂ ⩽ s ⇝ β*
    Goal: ⟦Φ⟧ ⊢ β* : suc β ≤ ⟦s⟧.
    Since (β* : suc β ≤ ⟦s⟧) ∈ ⟦Φ⟧ by preservation of environment membership, this holds by var and preservation of sizes.
  Cases refl≤, base≤, suc≤:
      Φ ⊢ s
      ---------------------.
      Φ ⊢ s ⩽ s ⇝ refl≤ ⟦s⟧
      Φ ⊢ ∘ ⩽ s ⇝ base≤ ⟦s⟧
      Φ ⊢ s ⩽ ŝ ⇝ suc≤  ⟦s⟧
    Goals: ⟦Φ⟧ ⊢ refl≤ ⟦s⟧ : ⟦s⟧ ≤ ⟦s⟧,
           ⟦Φ⟧ ⊢ base≤ ⟦s⟧ : ⟦s⟧ ≤ ⟦s⟧,
           ⟦Φ⟧ ⊢ suc≤  ⟦s⟧ : ⟦s⟧ ≤ ⟦s⟧,
    Holds by inspection of the definitions of refl≤, base≤, and suc≤, using preservation of sizes.
    (Definitions can be found in the Agda proofs.)
  Case trans≤: Φ ⊢ s₁ ⩽ s₂ ⇝ e₁  Φ ⊢ s₂ ⩽ s₃ ⇝ e₂
               -----------------------------------------.
               Φ ⊢ s₁ ⩽ s₃ ⇝ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂
    IHs: ⟦Φ⟧ ⊢ e₁ : ⟦s₁⟧ ≤ ⟦s₂⟧ and
         ⟦Φ⟧ ⊢ e₂ : ⟦s₂⟧ ≤ ⟦s₃⟧.
    By size well-formedness in subsizing and preservation of sizes we also have
      (†) ⟦Φ⟧ ⊢ s₁ : Size, ⟦Φ⟧ ⊢ s₂ : Size, and ⟦Φ⟧ ⊢ s₃ : Size.
    Goal: ⟦Φ⟧ ⊢ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂ : ⟦s₁⟧ ≤ ⟦s₃⟧
    Holds by inspection of the definition of trans≤, using the IHs and (†).
    (Definition of trans≤ can be found in the Agda proof.)

Theorem: (1) If Φ ⊢ Γ then ⊢ ⟦Φ⟧⟦Γ⟧,
             where ⊢ Φ by well-formedness of environments, and
         (2) If Φ; Γ ⊢ e : τ then ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧,
             where Φ; Γ ⊢ τ : U for some U by well-typedness of types.
Proof: By simultaneous strong induction on the derivations of Φ ⊢ Γ and Φ; Γ ⊢ e : τ.
  We implicitly use uniqueness of binding variables and structural exchange and weakening throughout.

  ENVIRONMENT WELL-FORMEDNESS CASES
  Case nil: ⊢ ⟦Φ⟧ holds by preservation of sizes.
  Case cons-ass: Φ ⊢ Γ  Φ; Γ ⊢ τ : U
                 -------------------.
                 Φ ⊢ Γ(x: τ)
    IHs: ⊢ ⟦Φ⟧⟦Γ⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : U.
    ⊢ ⟦Φ⟧⟦Γ⟧(x: ⟦τ⟧) holds by IHs and cons-ass.
  Case cons-def: ⊢ Γ  Γ ⊢ e : τ
                 --------------.
                 ⊢ Γ(x := e)
    IHs: ⊢ ⟦Φ⟧⟦Γ⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧.
    ⊢ ⟦Φ⟧⟦Γ⟧(x : ⟦e⟧) holds by the IHs and cons-def.

  TYPING CASES
  Case var: Φ ⊢ Γ  (x: τ) ∈ Γ
            -----------------.
            Φ; Γ ⊢ x : τ
    IH: ⊢ ⟦Φ⟧⟦Γ⟧.
    By preservation of environment membership, (x: ⟦τ⟧) ∈ ⟦Γ⟧,
      so ⟦Φ⟧⟦Γ⟧ ⊢ x : ⟦τ⟧ follows from rule var and the IH.
  Case conv: Φ; Γ ⊢ e : τ'
             Φ; Γ ⊢ τ : U
             Φ; Γ ⊢ τ' : U
             Φ; Γ ⊢ τ' ≼ τ
             -------------.
             Φ; Γ ⊢ e : τ
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ'⟧,
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : U, and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ'⟧ : U.
    By preservation of subtyping, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ'⟧ ≼ ⟦τ⟧.
    Then ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧ follows from rule conv and the IHs.
  Case univ: Trivial by rule univ.
  Cases pi, lam, app, let: Directly by the respective IHs and rules pi/lam/app/let.
  Case sigma: Φ; Γ ⊢ σ : U  Φ; Γ(x: σ) ⊢ U
              ----------------------------.
              Φ; Γ ⊢ Σx: σ. τ : U
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U and
         ⟦Φ⟧⟦Γ⟧(x : ⟦σ⟧) ⊢ ⟦τ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) : U.
    By well-formedness of environments, Φ ⊢ Γ is a subderivation, so we have ⊢ ⟦Φ⟧⟦Γ⟧.
    By the IHs, we have that ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦τ⟧ : Πx: ⟦σ⟧. U by rule lam.
    Then we have the goal via rules app and ind.
  Case pair: Φ; Γ ⊢ σ : U  Φ; Γ(x: σ) ⊢ τ : U
             Φ; Γ ⊢ e₁ : σ  Φ; Γ ⊢ e₂ : τ[x ↦ e₁]
             ------------------------------------.
             Φ; Γ ⊢ 〈e₁, e₂〉 {Σx: σ. τ} : Σx: σ. τ
    IHs: (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U
         (2) ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦τ⟧ : U
         (3) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ : ⟦σ⟧ and
         (4) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : ⟦τ[x ↦ e₁]⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) ⟦e₁⟧ ⟦e₂⟧ : Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧).
    By well-formedness of environments, Φ ⊢ Γ is a subderivation, so we have (†) ⊢ ⟦Φ⟧⟦Γ⟧.
    By rule lam, from (1) and (2) we have
      (5) ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦τ⟧ : Πx: ⟦σ⟧. U.
    By compositionality, (4) becomes
      (6) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : ⟦τ⟧[x ↦ ⟦e₁⟧].
    By β-reduction and ≈-red, we have that (λx: ⟦σ⟧. ⟦τ⟧) ⟦e₁⟧ ≈ ⟦τ⟧[x ↦ ⟦e₁⟧], so by rule conv, we have
      (7) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : (λx: ⟦σ⟧. ⟦τ⟧) ⟦e₁⟧.
    Finally, using (†), (1), (3), (5), and (7), by rule constr and app four times, we have the goal.
  Case left: Φ; Γ ⊢ e : Σx: σ. τ  Φ; Γ ⊢ σ : U
             ---------------------------------.
             Φ; Γ ⊢ π₁ e : σ
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ()._.⟦σ⟧ with (pair z _ ⇒ z) : ⟦σ⟧.
    By rule var, we have that
      ⟦Φ⟧⟦Γ⟧(z: ⟦σ⟧) ⊢ z : ⟦σ⟧.
    Then the goal holds by the IHs and rule match.
  Case right: Φ; Γ ⊢ e : Σx: σ. τ  Φ; Γ(x: σ) ⊢ τ : U
              ---------------------------------------.
              Φ; Γ ⊢ π₂ e : τ[x ↦ π₁ e]
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) and
         ⟦Φ⟧⟦Γ⟧(x : ⟦σ⟧) ⊢ τ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ().y.⟦τ⟧[x ↦ match y return λ()._.⟦σ⟧ with (pair z _ ⇒ z)] with (pair _ z ⇒ z) : ⟦τ[x ↦ π₁ e]⟧.
    By rule var, we have that
      ⟦Φ⟧⟦Γ⟧(z: ⟦σ⟧)(y: (λx: ⟦σ⟧. ⟦τ⟧) z) ⊢ y : (λx: ⟦σ⟧. ⟦τ⟧) z.
    By compositionality, we have
      ⟦τ[x ↦ π₁ e]⟧
      = ⟦τ⟧[x ↦ ⟦π₁ e⟧]
      = ⟦τ⟧[x ↦ match ⟦e⟧ return λ()._.⟦σ⟧ with (pair z _ ⇒ z)].
    Then the goal holds by the IHs and rule match.
  Case forall: Φ(α); Γ ⊢ τ : U
               ----------------.
               Φ; Γ ⊢ ∀α. τ : U
    IH: ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦τ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. ⟦τ⟧ : U.
    Note that in all cases of U, we have rule(Set, U) = U.
    Since · ⊢ Size : Set, the goal follows by the IH and rule pi.
  Case forall<: Φ ⊢ s  Φ(α < s); Γ ⊢ τ : U
                --------------------------.
                Φ; Γ ⊢ ∀α < s. τ : U
    IH: ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦τ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ⟧ : U.
    Note that in all cases of U, we have rule(Prop, U) = U and rule(Set, U) = U.
    By preservation of sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ : Size, and also · ⊢ Size : Set.
    Then we also have that ⟦Φ⟧(α: Size) ⊢ suc α ≤ ⟦s⟧ : Prop.
    Therefore, the goal follows by the IH and rule pi twice.
  Case slam: Φ(α); Γ ⊢ e : τ
             --------------------.
             Φ; Γ ⊢ Λα. e : ∀α. τ
    IH: ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. ⟦e⟧ : Πα: Size. ⟦τ⟧.
    Since · ⊢ Size : Set, the goal follows by rule lam and the IH.
  Case slam<: Φ ⊢ s  Φ(α < s); Γ ⊢ e : τ
              ----------------------------.
              Φ; Γ ⊢ Λα < s. e : ∀α < s. τ
    IH: ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. λα*: suc α ≤ ⟦s⟧. ⟦e⟧ : Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ⟧.
    By preservation of sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    Then ⟦Φ⟧(α: Size) ⊢ suc α ≤ ⟦s⟧ : Prop, so by rule lam and the IH,
      ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ λα*: suc α ≤ ⟦s⟧ : Πα*: suc α ≤ ⟦s⟧. ⟦τ⟧ holds.
    Finally, since · ⊢ Size : Set, the goal follows again by rule lam again.
  Case sapp: Φ ⊢ s  Φ; Γ ⊢ e : ∀α. τ
             -----------------------.
             Φ; Γ ⊢ e [s] : τ[α ↦ s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Πα: Size. ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ : ⟦τ[α ↦ s]⟧.
    Then by compositionality, it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ : ⟦τ⟧[α ↦ ⟦s⟧].
    By preservation of sizes, we have ⟦Φ⟧⟦Γ⟧ ⊢ ⟦s⟧ : Size.
    Then the goal follows by rule app.
  Case sapp<: Φ ⊢ ŝ ⩽ r  Φ; Γ ⊢ e : ∀α < r. τ
              -------------------------------.
              Φ; Γ ⊢ e [s] : τ[α ↦ s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ e≤ : ⟦τ[α ↦ s]⟧, where Φ ⊢ ŝ ⩽ r ⇝ e≤.
    Then by compositionality, it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ e≤ : ⟦τ⟧[α ↦ ⟦s⟧, α* ↦ e≤].
    By size well-formedness in subsizing and preservation of sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    By preservation of subsizing, we have ⟦Φ⟧ ⊢ e≤ : suc ⟦s⟧ ≤ ⟦r⟧.
    Then the goal follows by the IH and rule app applied twice.
  Case nat: Φ ⊢ Γ  Φ ⊢ s
            --------------------.
            Φ; Γ ⊢ ℕ [s] : Set
    IH: ⊢ ⟦Φ⟧⟦Γ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Nat ⟦s⟧ : Set.
    By preservation of sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    Then the goal holds by rules app and ind.
  Case zero: Φ ⊢ Γ  Φ ⊢ r̂ ⩽ s
             -------------------------------.
             Φ; Γ ⊢ zero {ℕ [s]} [r] : ℕ [s]
    IH: ⊢ ⟦Φ⟧⟦Γ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ zero ⟦s⟧ ⟦r⟧ e≤ : Nat ⟦s⟧, where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    By size well-formedness in subsizing and preservation of sizes,
      we have ⟦Φ⟧ ⊢ suc ⟦r⟧ : Size and ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    By preservation of subsizing, we have ⟦Φ⟧ ⊢ e≤ : suc ⟦r⟧ ≤ ⟦s⟧.
    Then the goal holds by rules constr and app thrice.
  Case succ: Φ ⊢ r̂ ⩽ s  Φ; Γ ⊢ e : ℕ [r]
             ---------------------------------.
             Φ; Γ ⊢ succ {ℕ [s]} [r] e : ℕ [s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Nat ⟦r⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ succ ⟦s⟧ ⟦r⟧ e≤ ⟦e⟧ : Nat ⟦s⟧, where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    By size well-formedness in subsizing and preservation fo sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ and ⟦Φ⟧ ⊢ ⟦s⟧.
    By preservation of subsizing, we have ⟦Φ⟧ ⊢ e≤ : suc ⟦r⟧ ≤ ⟦s⟧.
    By well-formedness of environments, Φ ⊢ Γ is a subderivation, so we have ⊢ ⟦Φ⟧⟦Γ⟧.
    Then the goal holds by rules constr and app four times.
  Case W: Φ ⊢ s  Φ; Γ ⊢ σ : U  Φ; Γ(x: σ) ⊢ τ : U
          ------------------------------------------.
          Φ; Γ ⊢ 𝕎x: σ. τ [s] : max{⊑}(U, Set)
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ W ⟦s⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) : max{⊑}(U, Set)
    By preservation of sizes, we have (1) ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    By well-formedness of environments, Φ ⊢ Γ is a subderivation, so we have (2) ⊢ ⟦Φ⟧⟦Γ⟧.
    By the IHs and possibly ≼-univ and rule conv, we have by rule lam that
      (3) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : Type{i} and
      (4) ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦τ⟧ : Πx: ⟦σ⟧. Type{i}.
    Using (2), (3), and (4), by rules ind and app three times, we have
      ⟦Φ⟧⟦Γ⟧ ⊢ W ⟦s⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) : Set.
    If U = Prop or Set, this is the goal; otherwise, if U = Type{i},
      we can lift Set up to Type{i} via ≼-univ and rule conv.
  Case sup: Φ ⊢ r̂ ⩽ s  Φ; Γ ⊢ σ : U  Φ; Γ(x: σ) ⊢ τ : U
            Φ; Γ ⊢ e₁ : σ  Φ; Γ ⊢ e₂ : τ[x ↦ e₁] → 𝕎x: σ. τ [r]
            ----------------------------------------------------.
            Φ; Γ ⊢ sup {𝕎x: σ. τ [s]} [r] e₁ e₂ : 𝕎x: σ. τ [s]
    IHs: (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U,
         (2) ⟦Φ⟧⟦Γ⟧(x: ⟦σ⟧) ⊢ ⟦τ⟧ : U,
         (3) ⟦Φ⟧⟦Γ⟧ ⊢ e₁ : ⟦σ⟧, and
         (4) ⟦Φ⟧⟦Γ⟧ ⊢ e₂ : ⟦τ[x ↦ e₁]⟧ → W ⟦r⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧).
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ sup ⟦s⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) ⟦r⟧ e≤ ⟦e₁⟧ ⟦e₂⟧ : W ⟦s⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧),
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    By (1) and (2), we have that (5) ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦τ⟧ : Πx: ⟦σ⟧. U by rule lam.
    By size well-formedness in subsizing and preservation of sizes, we have
      (6) ⟦Φ⟧ ⊢ ⟦s⟧ : Size and
      (7) ⟦Φ⟧ ⊢ ⟦r⟧ : Size.
    By preservation of subtyping, we have
      (8) ⟦Φ⟧ ⊢ e≤ : suc ⟦r⟧ ≤ ⟦s⟧.
    Putting it all together, using (1) and (3) through (8), we then have the goal by rules constr and app seven times.
  Case match-nat: Φ; Γ ⊢ e : ℕ [s]  Φ; Γ(x: ℕ [s]) ⊢ P : U
                  Φ;(α < s); Γ ⊢ ez : P[x ↦ zero {ℕ [s]} [α]]
                  Φ;(β < s); Γ(z: ℕ [β]) ⊢ es : P[x ↦ succ {ℕ [s]} [β] z]
                  -----------------------------------------------------------------------------.
                  Φ; Γ ⊢ match e return λx.P with (zero [α] ⇒ ez) (succ [β] z ⇒ es) : P[x ↦ e]
    IHs: (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Nat ⟦s⟧,
         (2) ⟦Φ⟧⟦Γ⟧(x: Nat ⟦s⟧) ⊢ ⟦P⟧ : U,
         (3) ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦ez⟧ : ⟦P[x ↦ zero {ℕ [s]} [α]]⟧, and
         (4) ⟦Φ⟧(β: Size)(β*: suc β ≤ ⟦β⟧)⟦Γ⟧(z: Nat ⟦β⟧) ⊢ ⟦es⟧ : ⟦P[x ↦ succ {ℕ [s]} [β] z]⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ().x.⟦P⟧ with (zero α α* ⇒ ⟦ez⟧) (succ β β* z ⇒ ⟦es⟧) : ⟦P[x ↦ e]⟧.
    By well-formedness of environments, Φ ⊢ Γ is a subderivation.
    Furthermore, by well-typedness of types, Φ; Γ ⊢ ℕ [s] : Set, so Φ ⊢ s.
    Then we can construct the following:
      (5) Φ(α < s); Γ ⊢ zero {ℕ [s]} [α] : ℕ [s], and
      (6) Φ(β < s); Γ(z: ℕ [β]) ⊢ succ {ℕ [s]} [β] z : ℕ [s],
    so by compositionality, the type in (3) and (4) become ⟦P⟧[x ↦ zero ⟦s⟧ α α*] and ⟦P⟧[x ↦ succ ⟦s⟧ β β* z],
    while the type in the goal becomes ⟦P⟧[x ↦ ⟦e⟧].
    Finally, using the IHs, we have the goal by rule match.
  Case match-sup: Φ; Γ ⊢ e : 𝕎y: σ. τ [s]  Φ; Γ(x: 𝕎y: σ. τ [s]) ⊢ P : U
                  Φ(α < s); Γ(z₁: σ)(z₂: τ[y ↦ z₁] → 𝕎y: σ. τ [α]) ⊢ es : P[x ↦ sup {𝕎y: σ. τ [s]} [α] z₁ z₂]
                  ---------------------------------------------------------------------------------------------.
                  Φ; Γ ⊢ match e return λx.P with (sup [α] z₁ z₂ ⇒ es) : P[x ↦ e]
    IHs: (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : W ⟦s⟧ ⟦σ⟧ (λy: ⟦σ⟧. ⟦τ⟧),
         (2) ⟦Φ⟧⟦Γ⟧(x: W ⟦s⟧ ⟦σ⟧ (λy: ⟦σ⟧. ⟦τ⟧)) ⊢ ⟦P⟧ : U, and
         (3) ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧(z₁: ⟦σ⟧)(z₂: ⟦τ[y ↦ z₁]⟧ → W α ⟦σ⟧ (λy: ⟦σ⟧. ⟦τ⟧)) ⊢ ⟦es⟧ : ⟦P[x ↦ sup {𝕎y: σ. τ [s]} [α] z₁ z₂]⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ().x.P with (sup α α* z₁ z₂ ⇒ ⟦es⟧) : ⟦P[x ↦ e]⟧.
    By well-formedness of environments, Φ ⊢ Γ is a subderivation.
    Furthermore, by well-typedness of types, Φ; Γ ⊢ 𝕎y: σ. τ [s] : max{⊑}(U, Set), so we have
      (4) Φ; Γ ⊢ σ : U,
      (5) Φ; Γ(y: σ) ⊢ τ : U, and
      (6) Φ ⊢ s.
    Then we can construct
      (7) Φ(α < s); Γ(z₁: σ)(z₂: τ[y ↦ z₁] → 𝕎y: σ. τ [α]) ⊢ sup {𝕎y: σ. τ [s]} [α] z₁ z₂ and
      (8) Φ; Γ(z₁: σ) ⊢ τ[y ↦ z₁] : U by renaming,
    so by compositionality, the type of (3) becomes ⟦P⟧[x ↦ sup ⟦s⟧ α α* z₁ z₂],
    while the type of the goal becomes ⟦P⟧[x ↦ ⟦e⟧], and ⟦τ[y ↦ z₁]⟧ = ⟦τ⟧[y ↦ z₁].
    Finally, using the IHs, we have the goal by rule match.
  Case ind: Φ ⊢ Γ  data X [α] ΔP : ΔI → U where Δ
            -------------------------------------.
            Φ; Γ ⊢ X : ∀α. ΔPΔI → U
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ X : (α: Size) → ⟦ΔPΔI → U⟧.
    By definition, the translation of the data type is
      data X (α: Size) ⟦ΔP⟧ : ⟦ΔI → U⟧ where _.
    Then the goal holds by rule ind.
  Case constr: Φ ⊢ Γ  data X [α] ΔP : ΔI → U where ...(c: τ)...
               ------------------------------------------------.
               Φ; Γ ⊢ c : ∀α. ΔP → τ
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ c : (α: Size) → ⟦ΔP → τ⟧.
    By definition, the translation of the data type is
      data X (α: Size) ⟦ΔP⟧ : ⟦ΔI → U⟧ where ...(c: ⟦τ⟧)....
    Then the goal holds by rule constr.
  Case match: data X [α] ΔP : ΔI → U where Δ
              Φ; Γ ⊢ e : X [s] p... eᵢ...
              Φ; Γ(ΔI[α ↦ s][ΔP ↦ p...])(x: X [s] p... dom(ΔI)) ⊢ P : U'
              ∀(c: τc) ∈ Δ, τc[α ↦ s][ΔP ↦ p...] ≡ ∀β < s. Δc → X [s] p... e'ᵢ...
              Φ(β < s); ΓΔc ⊢ ec : P[ΔI ↦ e'ᵢ...][x ↦ c [s] p... [β] dom(Δc)]
              ----------------------------------------------------------------------------------------.
              Φ; Γ ⊢ match e return λ(dom(ΔI)).x.P with (c [β] dom(Δc) ⇒ ec)... : P[ΔI ↦ eᵢ...][x ↦ e]
    IHs: (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : X ⟦s⟧ ⟦p⟧... ⟦eᵢ⟧...,
         (2) ⟦Φ⟧⟦Γ⟧⟦ΔI[α ↦ s][ΔP ↦ p...]⟧(x: X ⟦s⟧ ⟦p⟧... dom(ΔI)) ⊢ ⟦P⟧ : U', and
         (3) for each constructor c, ⟦Φ⟧(β: Size)(β*: suc β ≤ ⟦s⟧)⟦Γ⟧⟦Δc⟧ ⊢ ⟦ec⟧ : ⟦P[ΔI ↦ e'ᵢ...][x ↦ c [s] p... [β] dom(Δc)]⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ(dom(ΔI)).x.⟦P⟧ with (c β β* dom(Δc) ⇒ ⟦ec⟧)... : ⟦P[ΔI ↦ eᵢ...][x ↦ e]⟧.
    By term and size compositionality for environments, (2) becomes
      (4) ⟦Φ⟧⟦Γ⟧⟦ΔI⟧[α ↦ ⟦s⟧][ΔP ↦ ⟦p⟧...](x: X ⟦s⟧ ⟦p⟧... dom(ΔI)) ⊢ ⟦P⟧ : U',
    and by compositionality, (3) becomes
      (5) for each constructor c, ⟦Φ⟧(β: Size)(β*: suc β ≤ ⟦s⟧)⟦Γ⟧⟦Δc⟧ ⊢ ⟦ec⟧ : ⟦P⟧[ΔI ↦ ⟦e'ᵢ⟧...][x ↦ c ⟦s⟧ ⟦p⟧... β β* dom(Δc)].
    Furthermore, again by compositionality, we have that for each constructor (c: ⟦τc⟧) ∈ ⟦Δ⟧,
      ⟦τc⟧[α ↦ ⟦s⟧][ΔP ↦ ⟦p⟧...]
      = ⟦τc[α ↦ s][ΔP ↦ p...]⟧
      = ⟦∀β < s. Δc → X [s] p... e'ᵢ...⟧
      = (β: Size) → (β*: suc β ≤ ⟦s⟧) → ⟦Δc⟧ → X ⟦s⟧ ⟦p⟧... ⟦e'ᵢ⟧...,
    so with (1), (4), and (5), rule match gives us
      (6) ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ(dom(ΔI)).x.P with (c β β* dom(Δc) ⇒ ⟦ec⟧)... : ⟦P⟧[ΔI ↦ ⟦eᵢ⟧][x ↦ ⟦e⟧].
    Finally, by compositionality yet again, we have
      ⟦P⟧[ΔI ↦ ⟦eᵢ⟧][x ↦ ⟦e⟧] = ⟦P[ΔI ↦ eᵢ...][x ↦ e]⟧,
    so (6) becomes the desired goal.
  Case fix: Φ(α); Γ ⊢ σ : U  Φ(α); Γ(f: ∀β < α. σ[α ↦ β]) ⊢ e : σ
            --------------------------------------------------------.
            Φ; Γ ⊢ fix f [α] : σ := e : ∀α. σ
    IHs: (1) ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦σ⟧ : U and
         (2) ⟦Φ⟧(α: Size)⟦Γ⟧(f: (β: Size) → suc β ≤ α → ⟦σ[α ↦ β]⟧) ⊢ ⟦e⟧ : ⟦σ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ elim (λα: Size. ⟦σ⟧) (λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧) : (α: Size) → ⟦σ⟧.
    Since · ⊢ Size : Set, by rule lam twice, we have from (1) that
      (3) ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. ⟦σ⟧ : Size → U.
    By the definition of elim (see the Agda proof), we can construct the following:
      (4) · ⊢ elim : (P: Size → Type{i}) → ((α: Size) → ((β: Size) → suc β ≤ α → P β) → P α) → (α: Size) → P α.
    Then by rule app applied twice, we have
      (5) ⟦Φ⟧⟦Γ⟧ ⊢ elim (λα: Size. ⟦σ⟧) : ((α: Size) → ((β: Size) → suc β ≤ α → (λα: Size. ⟦σ⟧) β) → (λα: Size. ⟦σ⟧) α) → (α: Size) → (λα: Size. ⟦σ⟧) α.
    By β-reduction, ≈-red, ≈-cong, ≼-conv, and rule conv, this simplifies to
      (6) ⟦Φ⟧⟦Γ⟧ ⊢ elim (λα: Size. ⟦σ⟧) : ((α: Size) → ((β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]) → ⟦σ⟧) → (α: Size) → ⟦σ⟧.
    By renaming, Φ(β); Γ ⊢ σ[α ↦ β] : U, so by compositionality, ⟦σ[α ↦ β]⟧ = ⟦σ⟧[α ↦ β].
    Then by rules ind, pi, and lam from (1) and (2), we can construct the following:
      (7) ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β] : U, and
      (8) ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧) ⊢ (α: Size) → ((β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]) → ⟦σ⟧.
    Finally, applying (8) to (6), by rule app, we have the goal.

# Metatheoretical Results

Theorem (consistency): There exists a type τ such that ·; · ⊢ τ : U for some U,
  but there is no term e such that ·; · ⊢ e : τ.
Proof: Let τ ≝ ΠA: Prop. A. Note that ·; · ⊢ ΠA: Prop. A : Prop.
  Suppose we have some e such that ·; · ⊢ e : ΠA: Prop. A.
  By type preservation, we must have · ⊢ ⟦e⟧ : ΠA: Prop. A.
  However, the target language is consistent, i.e. ΠA: Prop. A is uninhabited.
  Then this is a contradiction, so it must be that no such e exists.
