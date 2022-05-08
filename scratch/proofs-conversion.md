ASSUME:
* All binding variables are unique.
* For each binding α < s, α* is a fresh term variable in the target only.
* ≈-trans and ≈-cong will be used implicitly and liberally
  in equational-style proofs over convertibility.

NOTE:
* Congruence of convertibility is required in the presence of ≈-*-η rules.
  Otherwise, (g: (Prop → Prop) → Prop)(f: Prop → Prop) ⊢ g f ≈ g (λ x: Prop. f x) is not derivable.
* Transitivity of convertibility is also required in the presence of ≈-*-η rules in the source.
  Otherwise, (f: ΠP: Prop. P) ⊢ λx: Prop. f x ≈ f and (f: ΠP: Prop. P) ⊢ f ≈ Λα. f [α] are both derivable,
  since convertibility doesn't require well-typedness,
  while (f: ΠP: Prop. P) ⊢ λx: Prop. f x ≈ Λα. f [α] is evidently not.

# Subsizing, Wellformedness, and Typing Lemmas (source)

Lemma (term cut): If Φ; Γ₁(x: σ)Γ₂ ⊢ e : τ, then Φ; Γ₁(Γ₂[x ↦ e']) ⊢ e[x ↦ e'] : τ[x ↦ e'].
Proof: [TODO: Luo ECC Thm. 3.2.6]

Lemma (unbounded size cut): If Φ₁(α < r)Φ₂; Γ ⊢ e : τ, then Φ₁(Φ₂[α ↦ s]); Γ[α ↦ s] ⊢ e[α ↦ s] : τ[α ↦ s].
Proof: [TODO: Luo ECC Thm. 3.2.6]

Lemma (bounded size cut): If Φ₁(α)Φ₂; Γ ⊢ e : τ, then Φ₁(Φ₂[α ↦ s]); Γ[α ↦ s] ⊢ e[α ↦ s] : τ[α ↦ s].
Proof: [TODO: Luo ECC Thm. 3.2.6]

Lemma (size wellformedness in subsizing): If Φ ⊢ r ⩽ s, then Φ ⊢ r and Φ ⊢ s.
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

Lemma (well-typedness of types): If Φ; Γ ⊢ e : τ, then Φ; Γ ⊢ τ : U for some U.
Proof: By induction on the derivation of Φ; Γ ⊢ e : τ. [TODO: Luo ECC Thm. 3.2.7]

Lemma (wellformedness of environments):
  (1) If Φ ⊢ Γ, then ⊢ Φ is a subderivation.
  (2) If Φ ⊢ Γ₁Γ₂, then Φ ⊢ Γ₁ is a subderivation.
  (3) If Φ; Γ ⊢ e : τ, then Φ ⊢ Γ is a subderivation.
Proof (1): Trivial by induction on the derivation of Φ ⊢ Γ.
Proof (2): Trivial if Γ₂ is empty; otherwise,
  by straightforward induction on the derivation of Φ ⊢ Γ₁Γ₂.
Proof (3): By straightforward induction on the derivation of Φ; Γ ⊢ e : τ.

# Convertibility Lemmas (target)

Lemma (symmetry): If Γ ⊢ e₁ ≈ e₂ then Γ ⊢ e₂ ≈ e₁.
Proof: By induction on the derivation of Γ ⊢ e₁ ≈ e₂.
  Case ≈-red: Trivial by ≈-red.
  Case ≈-trans: By symmetry of the convertibility premises and ≈-trans.
  Case ≈-cong: By symmetry of the convertibility premises and ≈-cong.
  Case ≈-lam-ηL: By symmetry of the convertibility premise and ≈-lam-ηR.
  Case ≈-lam-ηR: By symmetry of the convertibility premise and ≈-lam-ηL.
  Case ≈-reflect: Trivial by ≈-reflect.

Lemma (function extensionality): If Γ ⊢ h: (x: τ) → f x == g x then Γ ⊢ f ≈ g.
Proof: Using ≈-cong and ≈-trans,
  f ≈ λx: τ. f x (by ≈-lam-ηR)
    ≈ λx: τ. let h' := h x in f x (by ζ-reduction)
    ≈ λx: τ. let h' := h x in g x (by ≈-reflect)
    ≈ λx: τ. g x (by ζ-reduction)
    ≈ g (by ≈-lam-ηL).
Corollary: If Γ ⊢ h: (x: τ) → f x == g x then Γ ⊢ refl f: f == g,
  by function extensionality, ≈-cong, ≼-conv and the conv rule.

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
  Case right: Φ; Γ ⊢ e : Σy: σ. τ  Φ; Γ(y: σ) ⊢ τ : U
              ---------------------------------------.
              Φ; Γ ⊢ πR e : τ[y ↦ πL e]
    IHs: ⟦e⟧[x ↦ ⟦e'⟧] = ⟦e[x ↦ e']⟧ and
         ⟦τ⟧[y ↦ ⟦e'⟧] = ⟦τ[y ↦ e']⟧.
    Then we have
      ⟦πR e⟧[x ↦ ⟦e'⟧]
      = match ⟦e⟧[x ↦ ⟦e'⟧] return λ().w.
            (match w return λ().U with
              (pair y _ ⇒ ⟦τ⟧[x ↦ ⟦e'⟧])) with
          (pair _ z ⇒ z)
        where w, z are fresh
      = match ⟦e[x ↦ e']⟧ return λ().w.
            (match w return λ().U with
              (pair y _ ⇒ ⟦τ[x ↦ e']⟧))
          (pair _ z ⇒ z)
        by the IHs
      = ⟦(πR e)[x ↦ e']⟧ by term cut.
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
      = ⟦e[x ↦ e'] [s]⟧ by term cut
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
    By size cut, we have Φ₁(Φ₂[α ↦ s]); Γ[α ↦ s] ⊢ e[α ↦ s] : ∀β < r'[α ↦ s]. τ[α ↦ s].
    Then let Φ₁(α < r)Φ₂ ⊢ ŝ' ⩽ r' ⇝ e≤' and Φ₁(Φ₂[α ↦ s]) ⊢ ŝ'[α ↦ s] ⩽ r'[α ↦ s] ⇝ e≤'[α ↦ s, α* ↦ e≤]
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
    By size cut, we have Φ₁(Φ₂[α ↦ s]); Γ[α ↦ s] ⊢ e[α ↦ s] : N [r'[α ↦ s]].
    Then let Φ₁(α < r)Φ₂ ⊢ r̂' ⩽ s' ⇝ e≤' and Φ₁(Φ₂[α ↦ s]) ⊢ r̂'[α ↦ s] ⩽ s'[α ↦ s] ⇝ e≤'[α ↦ ⟦s⟧, α* ↦ e≤]
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

# Preservation of Environment Membership

Lemma: (1) If (x: τ) ∈ Γ then (x: ⟦τ⟧) ∈ ⟦Γ⟧;
       (2) If (x := e) ∈ Γ then (x := ⟦e⟧) ∈ ⟦Γ⟧;
       (3) If (α) ∈ Φ then (α: Size) ∈ ⟦Φ⟧;
       (4) If (α < s) ∈ Φ then (α: Size) ∈ ⟦Φ⟧ and (α*: suc α ≤ ⟦s⟧) ∈ ⟦Φ⟧, and
       (5) dom(Γ) = dom(⟦Γ⟧) and dom(Φ) ⊆ dom(⟦Φ⟧).
Proof: Straightforward induction on the structures of Γ and Φ.

# Convertibility of Reduction

Lemma: If Φ; Γ ⊢ e ⊳ e', then ∃e* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⊳* e* and ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e'⟧.

Proof: By cases on the derivation of Φ; Γ ⊢ e ⊳ e'.
  Case ⊳δ: Φ; Γ ⊢ x ⊳ e where (x := e) ∈ Γ.
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ x ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ x hold.
    Let e* ≝ ⟦e⟧.
    By preservation of membership in environments, (x := ⟦e⟧) ∈ ⟦Γ⟧.
    Then ⟦Φ⟧⟦Γ⟧ ⊢ x ⊳* ⟦e⟧ (1) holds by ⊳δ and ⊳*-refl.
    Finally, ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ x (2) holds by ≈-red via ⊳*-refl and (1).
  Case ⊳β: Φ; Γ ⊢ (λx: τ. e) e' ⊳ e[x ↦ e'].
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦τ⟧. ⟦e⟧) ⟦e'⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[x ↦ e']⟧ hold.
    Let e* ≝ ⟦e⟧[x ↦ ⟦e'⟧].
    By ⊳β and ⊳*-refl, ⟦Φ⟧⟦Γ⟧ ⊢ (λx: ⟦τ⟧. ⟦e⟧) ⟦e'⟧ ⊳* ⟦e⟧[x ↦ ⟦e'⟧] (1) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[x ↦ ⟦e'⟧] ≈ ⟦e[x ↦ e']⟧ (2) holds.
  Case ⊳ζ: Φ; Γ ⊢ let x : σ := e₁ in e₂ ⊳ e₂[x ↦ e₁].
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e₂[x ↦ e₁]⟧ hold.
    Let e* ≝ ⟦e₂⟧[x ↦ ⟦e₁⟧].
    By ⊳ζ and ⊳*-refl, ⟦Φ⟧⟦Γ⟧ ⊢ let x : ⟦σ⟧ := ⟦e₁⟧ in ⟦e₂⟧ ⊳* ⟦e₂⟧[x ↦ ⟦e₁⟧] (2) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧[x ↦ ⟦e₁⟧] ≈ ⟦e₂[x ↦ e₁]⟧ (2) holds.
  Case ⊳πL: Φ; Γ ⊢ πL 〈e₁, e₂〉_Σx:σ.τ ⊳ e₁.
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦πL 〈e₁, e₂〉_Σx:σ.τ⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e₁⟧ hold, i.e.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match (pair ⟦σ⟧ ⟦λx:σ.τ⟧ ⟦e₁⟧ ⟦e₂⟧) return λ().y.⟦σ⟧ with (pair z _ ⇒ z) ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e₁⟧ hold.
    Let e* ≝ ⟦e₁⟧.
    By ⊳ι, ⟦Φ⟧⟦Γ⟧ ⊢ match (pair ⟦σ⟧ ⟦λx:σ.τ⟧ ⟦e₁⟧ ⟦e₂⟧) return λ().y.⟦σ⟧ with (pair z _ ⇒ z) ⊳ ⟦e₁⟧, so (1) holds by ⊳*-refl.
    Finally, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ ⟦e₁⟧ holds by ≈-red via ⊳*-refl.
  Case ⊳πR: Φ; Γ ⊢ πR 〈e₁, e₂〉_Σx:σ.τ ⊳ e₂.
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦πR 〈e1, e2〉_Σx:σ.τ⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e₂⟧ hold, i.e.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match (pair ⟦σ⟧ ⟦λx:σ.τ⟧ ⟦e₁⟧ ⟦e₂⟧) return λ().y.⟦τ[x ↦ πL y]⟧ with (pair _ z ⇒ z) ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e₂⟧ hold.
    Let e* ≝ ⟦e₂⟧.
    By ⊳ι, ⟦Φ⟧⟦Γ⟧ ⊢ match (pair ⟦σ⟧ ⟦λx:σ.τ⟧ ⟦e₁⟧ ⟦e₂⟧) return λ().y.⟦τ[x ↦ πL y]⟧ with (pair _ z ⇒ z) ⊳ ⟦e₂⟧, so (1) holds by ⊳*-refl.
    Finally, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ ⟦e₂⟧ holds by ≈-red via ⊳*refl.
  Case ⊳ϛ: Φ; Γ ⊢ (Λα.e) [s] ⊳ e[α ↦ s].
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. ⟦e⟧) ⟦s⟧ ⊳* e* and ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[α ↦ s]⟧.
    Let e* ≝ ⟦e⟧[α ↦ ⟦s⟧].
    By ⊳β and ⊳*-refl, ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. ⟦e⟧) ⟦s⟧ ⊳* ⟦e⟧[α ↦ ⟦s⟧] (1) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[α ↦ ⟦s⟧] ≈ ⟦e[α ↦ s]⟧ (2) holds.
  Case ⊳ϛ<: Φ; Γ ⊢ (Λα < r. e) [s] ⊳ e[α ↦ s].
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. λα*: suc α ≤ ⟦r⟧. ⟦e⟧) ⟦s⟧ e≤ ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[α ↦ s]⟧ hold,
      where Φ ⊢ ŝ ⩽ r ⇝ e≤.
    Let e* ≝ ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤].
    By ⊳β twice, ⊳*-refl, and ⊳*-trans, ⟦Φ⟧⟦Γ⟧ ⊢ (λα: Size. λα*: suc α ≤ ⟦r⟧. ⟦e⟧) ⟦s⟧ e≤ ⊳* ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] (1) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[α ↦ ⟦s⟧, α* ↦ e≤] ≈ ⟦e[α ↦ s]⟧ (2) holds.
  Case ⊳ι (zero): Φ; Γ ⊢ match (zero {ℕ [s]} [r]) return λx.P with (zero [α] ⇒ ez) (succ [β] z ⇒ es) ⊳ ez[α ↦ s].
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match (zero ⟦s⟧ ⟦r⟧ e≤) return λ().x.⟦P⟧ with (zero α α* ⇒ ⟦ez⟧) (succ β β* z ⇒ ⟦es⟧) ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦ez[α ↦ r]⟧ hold,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    Let e* ≝ ⟦ez⟧[α ↦ ⟦r⟧, α* ↦ e≤].
    By ⊳ι and ⊳*-refl, (1) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦ez⟧[α ↦ ⟦r⟧, α* ↦ e≤] ≈ ⟦ez[α ↦ r]⟧ holds.
  Case ⊳ι (succ): Φ; Γ ⊢ match (succ {ℕ [s]} [r] e) return λx.P with (zero [α] ⇒ ez) (succ [β] z ⇒ es) ⊳ ez[α ↦ s, z ↦ e].
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match (succ ⟦s⟧ ⟦r⟧ e≤ ⟦e⟧) return λ().x.⟦P⟧ with (zero α α* ⇒ ⟦ez⟧) (succ β β* z ⇒ ⟦es⟧) ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦ez[β ↦ r, z ↦ e]⟧ hold,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    Let e* ≝ ⟦es⟧[β ↦ ⟦r⟧, β* ↦ e≤, z ↦ ⟦e⟧].
    By ⊳ι and ⊳*-refl, (1) holds.
    By compositionality,
      ⟦Φ⟧⟦Γ⟧ ⊢ ⟦es⟧[β ↦ ⟦r⟧, β* ↦ e≤, z ↦ ⟦e⟧] ≈ ⟦es[β ↦ r, β* ↦ e≤, z ↦ e]⟧ (2) holds.
  Case ⊳ι (sup): Φ; Γ ⊢ match (sup {𝕎x: σ. τ [s]} [r] e₁ e₂) return λx.P with (sup [α] z₁ z₂ ⇒ e) ⊳ e[α ↦ r, z₁ ↦ e₁, z₂ ↦ e₂].
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match (sup ⟦s⟧ ⟦σ⟧ ⟦λx: σ. τ⟧ ⟦r⟧ e≤ ⟦e₁⟧ ⟦e₂⟧) return λx.⟦P⟧ with (sup α α* z₁ z₂ ⇒ ⟦e⟧) ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[α ↦ r, z₁ ↦ e₁, z₂ ↦ e₂]⟧ hold,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    Let e* ≝ ⟦e⟧[α ↦ ⟦r⟧, α* ↦ e≤, z₁ ↦ ⟦e₁⟧, z₂ ↦ ⟦e₂⟧].
    By ⊳ι and ⊳*-refl, (1) holds.
    By compositionality,
      ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[α ↦ ⟦r⟧, α* ↦ e≤, z₁ ↦ ⟦e₁⟧, z₂ ↦ ⟦e₂⟧] ≈ ⟦e[α ↦ r, z₁ ↦ e₁, z₂ ↦ e₂]⟧] (2) holds.
  Case ⊳ι: Φ; Γ ⊢ match c [s] p... [r] e... return _ with ...(c [β] z... ⇒ ec)... ⊳ ec[β, z... ↦ r, e...].
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ match c ⟦s⟧ ⟦p⟧... ⟦r⟧ e≤ ⟦e⟧... return _ with ...(c β β* z... ⇒ ⟦ec⟧)... ⊳ e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦ec[β, z... ↦ r, e...]⟧,
      where Φ ⊢ r̂ ⩽ s ⇝ e≤.
      Let e* ≝ ⟦ec⟧[β, β*, z... ↦ ⟦r⟧ e≤ ⟦e⟧...].
      By ⊳ι and ⊳*-refl, (1) holds.
      By compositionality, we have
        ⟦ec⟧[β, β*, z... ↦ ⟦r⟧ e≤ ⟦e⟧...]
        = ⟦ec[β ↦ r]⟧[z... ↦ ⟦e⟧...]
        = ⟦ec[β ↦ r][z... ↦ e...]⟧,
      so we have (2) by ⊳*-refl and ≈-red.
  Case ⊳μ: Φ; Γ ⊢ (fix f [α]: σ := e) [s] t₁ ... tₙ (c e₁ ... eₘ) ⊳ e[α ↦ s, f ↦ Λβ < s. (fix f [α]: σ := e) [β]] t₁ ... tₙ (c e₁ ... eₘ).
    Goal: Find e* s.t.
      (1) ⟦Φ⟧⟦Γ⟧ ⊢ elim (λα: Size. ⟦σ⟧) (λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧) ⟦s⟧ ⟦t₁⟧ ... ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧ ⊳* e* and
      (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[α ↦ s, f ↦ Λβ < s. (fix f [α]: σ := e) [β]]⟧ ⟦t₁⟧ ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧ hold.
    Let e* ≝ ⟦e⟧[α ↦ ⟦s⟧, f ↦ ⟦Λβ < s. (fix f [α]: σ := e) [β]⟧] ⟦t₁⟧ ... ⟦tₙ⟧ ⟦c e₁ ... eₘ⟧.
    For notational convenience, let P ≝ λα: Size. ⟦σ⟧ and g ≝ λα: Size. λf: (β: Size) → suc β ≤ α → ⟦σ⟧[α ↦ β]. ⟦e⟧,
    and recall that elim P g s = elimAcc s (accessible s) where
      acc< ≝ λ β: Size. λ β*: suc β ≤ ⟦s⟧. λ access: Acc ⟦s⟧.
        match access return λ()._.Acc β with (acc p ⇒ p β β*),
      elimAcc ≝ fix₁ elimAccRec: (α: Size) → Acc α → P α :=
          λα: Size. λaccess: Acc α.
            g α (λβ: Size. λβ*: suc β ≤ ⟦s⟧.
              elimAccRec β (acc< β β* access)).
    By ≈-cong and ≈-trans, the function part of the RHS of (1) is
      ⟦e⟧[α ↦ ⟦s⟧, f ↦ ⟦Λβ < s. (fix f [α]: σ := e) [β]⟧]
      = ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elim P g β]
      ≈ ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (accessible β)]
        by reduction of elim.
    On the other hand, by ≈-cong and ≈-trans, the corresponding part of the LHS of (1) is
      elim P g ⟦s⟧
      ≈ elimAcc ⟦s⟧ (accessible ⟦s⟧)
        by reduction of elim
      ≈ g ⟦s⟧ (λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (acc< β β* (accessible ⟦s⟧)))
        by reduction of elimAcc
      = ⟦e⟧[α ↦ ⟦s⟧, f ↦ λβ: Size. λβ*: suc β ≤ ⟦s⟧. elimAcc β (acc< β β* (accessible ⟦s⟧))]
        by definition of g.
    Using accIsProp and equality reflection,
    we can convert between (accessible β) and (acc< β β* (accessible ⟦s⟧)):
      accessible β
      ≈ let p := accIsProp β (accessible β) (acc< β β* (accessible ⟦s⟧))
        in accessible β
        by ζ-reduction
      ≈ let p := accIsProp β (accessible β) (acc< β β* (accessible ⟦s⟧))
        in acc< β β* (accessible ⟦s⟧)
        by ≈-reflect on p and ≈-cong
      ≈ acc< β β* (accessible ⟦s⟧)
        by ζ-reduction.
    Then by ≈-cong, the RHS and LHS are convertible, and (1) holds.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[α ↦ ⟦s⟧, f ↦ ⟦Λβ < s. (fix f [α]: σ := e) [β]⟧] ≈ ⟦e[α ↦ s, f ↦ Λβ < s. (fix f [α]: σ := e) [β]]⟧ holds.
    Then again by ≈-cong, (2) holds.

# Convertibility of (reflexive, transitive, congruent) Closure of Reduction

Lemma: If Φ; Γ ⊢ e ⊳* e', then ∃e* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⊳* e* and ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e'⟧.

Proof: By induction on the derivation of Γ ⊢ e ⊳* e'.
  Case ⊳*-refl: Φ; Γ ⊢ e ⊳* e. Trivial.
  Case ⊳*-trans: Φ; Γ ⊢ e ⊳ e'  Γ ⊢ e' ⊳* e''
                 ----------------------------.
                 Φ; Γ ⊢ e ⊳* e''
    IH: ∃e** s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e'⟧ ⊳* e** and ⟦Φ⟧⟦Γ⟧ ⊢ e** ≈ ⟦e''⟧.
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e''⟧.
    Let e* be the one from convertibility of reduction, where ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⊳* e* (1) and ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e'⟧ hold.
    By ⊳*-refl, ≈-red, ≈-trans, and the IH, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e'⟧ ≈ ⟦e''⟧ holds.
    Then again by ≈-trans, ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e''⟧ (2) holds.
  Case ⊳*-cong: For every i, Φ; Γ ⊢ eᵢ ⊳* eᵢ'
                -----------------------------.
                Φ; Γ ⊢ e[x ↦ eᵢ] ≈ e[x ↦ eᵢ']
    IH: For every i, ∃eᵢ* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦eᵢ⟧ ⊳* eᵢ* and ⟦Φ⟧⟦Γ⟧ ⊢ eᵢ* ≈ ⟦eᵢ'⟧.
    Goal: Find e* s.t. (1) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e[x ↦ eᵢ]⟧ ⊳* e* and (2) ⟦Φ⟧⟦Γ⟧ ⊢ e* ≈ ⟦e[x ↦ eᵢ']⟧.
    Let e* ≝ ⟦e[x ↦ eᵢ]⟧ so that (1) holds by ⊳*-refl.
    By compositionality, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[x ↦ ⟦eᵢ⟧] ≈ ⟦e[x ↦ eᵢ]⟧.
    By ⊳*-refl, ≈-red, ≈-trans, and the IH, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦eᵢ⟧ ≈ ⟦eᵢ'⟧.
    Then by ≈-cong, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[x ↦ ⟦eᵢ⟧] ≈ ⟦e⟧[x ↦ ⟦eᵢ'⟧].
    By compositionality again, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧[x ↦ ⟦eᵢ'⟧] ≈ ⟦e[x ↦ eᵢ']⟧.
    Finally, by ≈-trans and symmetry of convertibility, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e[x ↦ eᵢ]⟧ ≈ ⟦e[x ↦ eᵢ']⟧ (2) holds.

# Preservation of Convertibility

Lemma: If Φ; Γ ⊢ e₁ ≈ e₂, then ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ ⟦e₂⟧.

Proof: By induction on the derivation of Φ; Γ ⊢ e₁ ≈ e₂.
  We implicitly use structural exchange and uniqueness of binding variables throughout.
  Case ≈-red: Φ; Γ ⊢ e₁ ⊳* e
              Φ; Γ ⊢ e₂ ⊳* e
              --------------.
              Φ; Γ ⊢ e₁ ≈ e₂
    By convertibility of closure of reduction,
      ∃e₁* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ⊳* e₁* and ⟦Φ⟧⟦Γ⟧ ⊢ e₁* ≈ ⟦e⟧ holds, and
      ∃e₂* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ⊳* e₂* and ⟦Φ⟧⟦Γ⟧ ⊢ e₂* ≈ ⟦e⟧ holds.
    By ⊳*-refl and ≈-red, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ e₁* and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ e₂* hold.
    Then by ≈-trans and symmetry of convertibility, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ ⟦e₂⟧ holds.
  Case ≈-trans: Φ; Γ ⊢ e₁ ≈ e₂
                Φ; Γ ⊢ e₂ ≈ e₃
                --------------.
                Φ; Γ ⊢ e₁ ≈ e₃
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ ⟦e₂⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ ⟦e₃⟧.
    ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ ⟦e₃⟧ holds by ≈-trans.
  Case ≈-cong: For every i, Φ; Γ ⊢ eᵢ ≈ e'ᵢ
               -----------------------------.
               Φ; Γ ⊢ e[x ↦ eᵢ] ≈ e[x ↦ e'ᵢ]
    IH: For every i, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦eᵢ⟧ ≈ ⟦e'ᵢ⟧.
    We have that
      ⟦e[x ↦ eᵢ]⟧
      ≈ ⟦e⟧[x ↦ ⟦eᵢ⟧] by compositionality
      ≈ ⟦e⟧[x ↦ ⟦e'ᵢ⟧] by ≈-cong using the IH
      ≈ ⟦e[x ↦ e'ᵢ]⟧ by compositionality
    as desired.
  Case ≈-lam-ηL: Φ; Γ ⊢ e₁ ⊳* λx: τ. e
                 Φ; Γ ⊢ e₂ ⊳* e'₂
                 Φ; Γ(x: τ) ⊢ e ≈ e'₂ x
                 ----------------------.
                 Φ; Γ ⊢ e₁ ≈ e₂
    IH: ⟦Φ⟧⟦Γ⟧(x: ⟦τ⟧) ⊢ ⟦e⟧ ≈ ⟦e'₂⟧ x.
    By convertibility of closure of reduction,
      ∃e₁* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ⊳* e₁* and ⟦Φ⟧⟦Γ⟧ ⊢ e₁* ≈ λx: ⟦τ⟧. ⟦e⟧ hold, and
      ∃e₂* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ⊳* e₂* and ⟦Φ⟧⟦Γ⟧ ⊢ e₂* ≈ ⟦e'₂⟧ hold.
    By ⊳*-refl and ≈-red, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ λx: ⟦τ⟧. ⟦e⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ ⟦e'₂⟧ hold.
    By ≈-trans and symmetry of convertibility,
      it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦τ⟧. ⟦e⟧ ≈ ⟦e'₂⟧ holds.
    By ⊳*-refl and the IH, this holds by ≈-lam-ηL.
  Case ≈-lam-ηR: By symmetry of proof of case ≈-lam-ηL.
  Case ≈-slam-ηL: Φ; Γ ⊢ e₁ ⊳* Λα. e
                  Φ; Γ ⊢ e₂ ⊳* e'₂
                  Φ(α); Γ ⊢ e ≈ e'₂ [α]
                  ---------------------.
                  Φ; Γ ⊢ e₁ ≈ e₂
    IH: ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ ⟦e⟧ ≈ ⟦e'₂⟧ α.
    By convertibility of closure of reduction,
      ∃e₁* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ⊳* e₁* and ⟦Φ⟧⟦Γ⟧ ⊢ e₁* ≈ λα: Size. ⟦e⟧ hold, and
      ∃e₂* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ⊳* e₂* and ⟦Φ⟧⟦Γ⟧ ⊢ e₂* ≈ ⟦e'₂⟧ hold.
    By ⊳*-refl and ≈-red, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ λα: Size. ⟦e⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ ⟦e'₂⟧ hold.
    By ≈-trans and symmetry of convertibility,
      it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. ⟦e⟧ ≈ ⟦e'₂⟧ holds.
    By ⊳*-refl and the IH, this holds by ≈-lam-ηL.
  Case ≈-slam-ηR: By symmetry of proof of case ≈-slam-ηL.
  Case ≈-slam<-ηL: Φ; Γ ⊢ e₁ ⊳* Λα < s. e
                   Φ; Γ ⊢ e₂ ⊳* e'₂
                   Φ(α < s); Γ ⊢ e ≈ e'₂ [α]
                   -------------------------.
                   Φ; Γ ⊢ e₁ ≈ e₂
    IH: ⟦Φ⟧(α: Size)(α*: suc α ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦e⟧ ≈ ⟦e'₂⟧ α α*.
    By convertibility of closure of reduction,
      ∃e₁* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ⊳* e₁* and ⟦Φ⟧⟦Γ⟧ ⊢ e₁* ≈ λα: Size. λα*: suc α ≤ ⟦s⟧. ⟦e⟧ hold, and
      ∃e₂* s.t. ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ⊳* e₂* and ⟦Φ⟧⟦Γ⟧ ⊢ e₂* ≈ ⟦e'₂⟧ hold.
    By ⊳*-refl and ≈-red,
      ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₁⟧ ≈ λα: Size. λα*: suc α ≤ ⟦s⟧. ⟦e⟧ and
      ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ ≈ ⟦e'₂⟧ hold.
    By ≈-trans and symmetry of convertibility, it suffices to show that
      (†) ⟦Φ⟧⟦Γ⟧ ⊢ λα: Size. λα*: suc α ≤ ⟦s⟧. ⟦e⟧ ≈ ⟦e'₂⟧ holds.
    By the IH, ⊳*-refl, and ≈-lam-ηL, we have that
      ⟦Φ⟧(α: Size)⟦Γ⟧ ⊢ λα*: suc α ≤ ⟦s⟧. ⟦e⟧ ≈ ⟦e'₂⟧ α holds.
    Then by ⊳*-refl and ≈-lam-ηL again, (†) holds.
  Case ≈-slam<-ηR: By symmetry of proof of case ≈-slam<-ηR.

# Preservation of Subtyping

Lemma: If Φ; Γ ⊢ τ₁ ≼ τ₂, then ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≼ ⟦τ₂⟧.

Proof: By induction on the derivation of Γ ⊢ τ₁ ≼ τ₂.
  We implicitly use structural exchange and uniqueness of binding variables throughout.
  Case ≼-conv: Φ; Γ ⊢ τ₁ ≈ τ₂
               --------------.
               Φ; Γ ⊢ τ₁ ≼ τ₂
    By preservation of convertibility, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≈ ⟦τ₂⟧, so it follows via ≼-conv.
  Case ≼-trans: Φ; Γ ⊢ τ₁ ≼ τ₂  Φ; Γ ⊢ τ₂ ≼ τ₃
                ------------------------------.
                Φ; Γ ⊢ τ₁ ≼ τ₂
    By preservation of convertibility, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₁⟧ ≈ ⟦τ₂⟧ and ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ₂⟧ ≈ ⟦τ₃⟧,
      so it follows via ≼-trans.
  Cases ≼-univ: Φ; Γ ⊢ U₁ ≼ U₂. Trivial.
  Case ≼-pi: Φ; Γ ⊢ σ₂ ≈ σ₁  Φ; Γ(x₂: σ₂) ⊢ τ₁[x₁ ↦ x₂] ≼ τ₂
             -----------------------------------------.
             Φ; Γ ⊢ Πx₁: σ₁. τ₁ ≼ Πx₂: σ₂. τ₂
    IH: ⟦Φ⟧⟦Γ⟧(x₂: ⟦σ₂⟧) ⊢ ⟦τ₁[x₁ ↦ x₂]⟧ ≼ ⟦τ₂⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Πx₁: ⟦σ₁⟧. ⟦τ₁⟧ ≼ Πx₂: ⟦σ₂⟧. ⟦τ₂⟧.
    By preservation of convertibility, ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ₂⟧ ≈ ⟦σ₁⟧.
    By compositionality, we have that ⟦Φ⟧⟦Γ⟧(x₂: ⟦σ₂⟧) ⊢ ⟦τ₁⟧[x₁ ↦ x₂] ≈ ⟦τ₁[x₁ ↦ x₂]⟧.
    Then by ≼-conv, ≼-trans, and the IH, ⟦Φ⟧⟦Γ⟧(x₂: ⟦σ₂⟧) ⊢ ⟦τ₁⟧[x₁ ↦ x₂] ≼ ⟦τ₂⟧.
    Finally, by ≼-pi, we have ⟦Φ⟧⟦Γ⟧ ⊢ Πx₁: ⟦σ₁⟧. ⟦τ₁⟧ ≼ Πx₂: ⟦σ₂⟧. ⟦τ₂⟧.
  Case ≼-forall: Φ(α₂); Γ ⊢ τ₁[α₁ ↦ α₂] ≼ τ₂
                 ---------------------------.
                 Φ; Γ ⊢ ∀α₁. τ₁ ≼ ∀α₂. τ₂
    IH: ⟦Φ⟧(α₂: Size)⟦Γ⟧ ⊢ ⟦τ₁[α₁ ↦ α₂]⟧ ≼ ⟦τ₂⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Πα₁: Size. ⟦τ₁⟧ ≼ Πα₂: Size. ⟦τ₂⟧.
    By ⊳*-refl and ≈-red, we have ⟦Φ⟧⟦Γ⟧ ⊢ Size ≈ Size.
    By compositionality, we have that ⟦Φ⟧(α₂: Size)⟦Γ⟧ ⊢ ⟦τ₁⟧[α₁ ↦ α₂] ≈ ⟦τ₁[α₁ ↦ α₂]⟧.
    Then by ≼-conv, ≼-trans, and the IH, ⟦Φ⟧(α₂: Size)⟦Γ⟧ ⊢ ⟦τ₁⟧[α₁ ↦ α₂] ≼ ⟦τ₂⟧.
    Finally, by ≼-pi, we have ⟦Φ⟧⟦Γ⟧ ⊢ Πα₁: Size. ⟦τ₁⟧ ≼ Πα₂: Size. ⟦τ₂⟧.
  Case ≼-forall<: Φ(α₂ < s); Γ ⊢ τ₁[α₁ ↦ α₂] ≼ τ₂
                  ------------------------------------------
                  Φ; Γ ⊢ ∀α₁ < s. τ₁ ≼ ∀α₂ < s. τ₂
    IH: ⟦Φ⟧(α₂: Size)(α*₂: suc α₂ ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦τ₁[α₁ ↦ α₂]⟧ ≼ ⟦τ₂⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ Πα₁: Size. Πα*₁: suc α₁ ≤ ⟦s⟧. ⟦τ₁⟧ ≼ Πα₂: Size. Πα*₂: suc α₂ ≤ ⟦s⟧. ⟦τ₂⟧.
    By ⊳*-refl and ≈-red, we have ⟦Φ⟧⟦Γ⟧ ⊢ Size ≈ Size.
    Then through ≼-pi, it suffices to show that
      (†) ⟦Φ⟧⟦Γ⟧(α₂: Size)(α*₂: suc α₂ ≤ ⟦s⟧) ⊢ ⟦τ₁⟧[α₁ ↦ α₂, α*₁ ↦ α*₂] ≼ ⟦τ₂⟧.
    By compositionality, we have that
      ⟦Φ⟧(α₂: Size)(α*₂: suc α₂ ≤ ⟦s⟧)⟦Γ⟧ ⊢ ⟦τ₁⟧[α₁ ↦ α₂, α*₁ ↦ α*₂] ≈ ⟦τ₁[α₁ ↦ α₂]⟧].
    Then by ≼-conv, ≼-trans, and the IH, we have (†).

# Type Preservation

Lemma (preservation of sizes):
  (1) If ⊢ Φ then ⊢ ⟦Φ⟧, and
  (2) If Φ ⊢ s then ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
Proof: By simultaneous induction on the derivations of ⊢ Φ and Φ ⊢ s.

  SIZE ENVIRONMENT WELLFORMEDNESS CASES
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

  SIZE WELLFORMEDNESS CASES
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
    Goal: ⟦Γ⟧ ⊢ β* : suc β ≤ ⟦s⟧.
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
    By size wellformedness in subsizing and preservation of sizes we also have
      (†) ⟦Φ⟧ ⊢ s₁ : Size, ⟦Φ⟧ ⊢ s₂ : Size, and ⟦Φ⟧ ⊢ s₃ : Size.
    Goal: ⟦Φ⟧ ⊢ trans≤ ⟦s₁⟧ ⟦s₂⟧ ⟦s₃⟧ e₁ e₂ : ⟦s₁⟧ ≤ ⟦s₃⟧
    Holds by inspection of the definition of trans≤, using the IHs and (†).
    (Definition of trans≤ can be found in the Agda proof.)

Theorem: (1) If Φ ⊢ Γ then ⊢ ⟦Φ⟧⟦Γ⟧, and
         (2) If Φ; Γ ⊢ e : τ then ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ⟧.
Proof: By simultaneous induction on the derivations of Φ ⊢ Γ and Φ; Γ ⊢ e : τ.
  We implicitly use uniqueness of binding variables and structural exchange and weakening throughout.

  ENVIRONMENT WELLFORMEDNESS CASES
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
  Case conv: Φ; Γ ⊢ τ : U
             Φ; Γ ⊢ e : τ'
             Φ; Γ ⊢ τ' ≼ τ
             ---------------.
             Φ; Γ ⊢ e : τ
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : U and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : ⟦τ'⟧.
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
    By wellformedness of environments, Φ ⊢ Γ is a subderivation, so we have ⊢ ⟦Φ⟧⟦Γ⟧.
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
    By wellformedness of environments, Φ ⊢ Γ is a subderivation, so we have (†) ⊢ ⟦Φ⟧⟦Γ⟧.
    By rule lam, from (1) and (2) we have
      (5) ⟦Φ⟧⟦Γ⟧ ⊢ λx: ⟦σ⟧. ⟦τ⟧ : Πx: ⟦σ⟧. U.
    By compositionality, (4) becomes
      (6) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : ⟦τ⟧[x ↦ ⟦e₁⟧].
    By β-reduction and ≈-red, we have that (λx: ⟦σ⟧. ⟦τ⟧) ⟦e₁⟧ ≈ ⟦τ⟧[x ↦ ⟦e₁⟧], so by rule conv, we have
      (7) ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e₂⟧ : (λx: ⟦σ⟧. ⟦τ⟧) ⟦e₁⟧.
    Finally, using (†), (1), (3), (5), and (7), by rule constr and app four times, we have the goal.
  Case left: Φ; Γ ⊢ e : Σx: σ. τ  Φ; Γ ⊢ σ : U
             ---------------------------------.
             Φ; Γ ⊢ πL e : σ
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ()._.⟦σ⟧ with (pair z _ ⇒ z) : ⟦σ⟧.
    By rule var, we have that
      ⟦Φ⟧⟦Γ⟧(z: ⟦σ⟧) ⊢ z : ⟦σ⟧.
    Then the goal holds by the IHs and rule match.
  Case right: Φ; Γ ⊢ e : Σx: σ. τ  Φ; Γ(x: σ) ⊢ τ : U
              ---------------------------------------.
              Φ; Γ ⊢ πR e : τ[x ↦ πL e]
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Pair ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) and
         ⟦Φ⟧⟦Γ⟧(x : ⟦σ⟧) ⊢ τ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ match ⟦e⟧ return λ().y.⟦τ⟧[x ↦ match y return λ()._.⟦σ⟧ with (pair z _ ⇒ z)] with (pair _ z ⇒ z) : ⟦τ[x ↦ πL e]⟧.
    By rule var, we have that
      ⟦Φ⟧⟦Γ⟧(z: ⟦σ⟧)(y: (λx: ⟦σ⟧. ⟦τ⟧) z) ⊢ y : (λx: ⟦σ⟧. ⟦τ⟧) z.
    By compositionality, we have
      ⟦τ[x ↦ πL e]⟧
      = ⟦τ⟧[x ↦ ⟦πL e⟧]
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
    By well-typedness of types, we have Φ; Γ ⊢ ∀α. τ : U, and therefore Φ(α); Γ ⊢ τ : U.
    Then by compositionality, it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ : ⟦τ⟧[α ↦ ⟦s⟧].
    By preservation of sizes, we have ⟦Φ⟧⟦Γ⟧ ⊢ ⟦s⟧ : Size.
    Then the goal follows by rule app.
  Case sapp<: Φ ⊢ ŝ ⩽ r  Φ; Γ ⊢ e : ∀α < r. τ
              -------------------------------.
              Φ; Γ ⊢ e [s] : τ[α ↦ s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Πα: Size. Πα*: suc α ≤ ⟦s⟧. ⟦τ⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ e≤ : ⟦τ[α ↦ s]⟧, where Φ ⊢ ŝ ⩽ r ⇝ e≤.
    By well-typedness of types, we have Φ; Γ ⊢ ∀α < r. τ : U, and therefore Φ(α < r); Γ ⊢ τ : U.
    Then by compositionality, it suffices to show that ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ ⟦s⟧ e≤ : ⟦τ⟧[α ↦ ⟦s⟧, α* ↦ e≤].
    By size wellformedness in subsizing and preservation of sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
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
    By size wellformedness in subsizing and preservation of sizes,
      we have ⟦Φ⟧ ⊢ suc ⟦r⟧ : Size and ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    By preservation of subsizing, we have ⟦Φ⟧ ⊢ e≤ : suc ⟦r⟧ ≤ ⟦s⟧.
    Then the goal holds by rules constr and app thrice.
  Case succ: Φ ⊢ r̂ ⩽ s  Φ; Γ ⊢ e : ℕ [r]
             ---------------------------------.
             Φ; Γ ⊢ succ {ℕ [s]} [r] e : ℕ [s]
    IH: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦e⟧ : Nat ⟦r⟧.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ succ ⟦s⟧ ⟦r⟧ e≤ ⟦e⟧ : Nat ⟦s⟧, where Φ ⊢ r̂ ⩽ s ⇝ e≤.
    By size wellformedness in subsizing and preservation fo sizes, we have ⟦Φ⟧ ⊢ ⟦s⟧ and ⟦Φ⟧ ⊢ ⟦s⟧.
    By preservation of subsizing, we have ⟦Φ⟧ ⊢ e≤ : suc ⟦r⟧ ≤ ⟦s⟧.
    By wellformedness of environments, Φ ⊢ Γ is a subderivation, so we have ⊢ ⟦Φ⟧⟦Γ⟧.
    Then the goal holds by rules constr and app four times.
  Case W: Φ ⊢ s  Φ; Γ ⊢ σ : U  Φ; Γ(x: σ) ⊢ τ : U
          ------------------------------------------.
          Φ; Γ ⊢ 𝕎x: σ. τ [s] : max{⊑}(U, Set)
    IHs: ⟦Φ⟧⟦Γ⟧ ⊢ ⟦σ⟧ : U and
         ⟦Φ⟧⟦Γ⟧ ⊢ ⟦τ⟧ : U.
    Goal: ⟦Φ⟧⟦Γ⟧ ⊢ W ⟦s⟧ ⟦σ⟧ (λx: ⟦σ⟧. ⟦τ⟧) : max{⊑}(U, Set)
    By preservation of sizes, we have (1) ⟦Φ⟧ ⊢ ⟦s⟧ : Size.
    By wellformedness of environments, Φ ⊢ Γ is a subderivation, so we have (2) ⊢ ⟦Φ⟧⟦Γ⟧.
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
    By size wellformedness in subsizing and preservation of sizes, we have
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
    By wellformedness of environments, Φ ⊢ Γ is a subderivation.
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
    By wellformedness of environments, Φ ⊢ Γ is a subderivation.
    Furthermore, by well-typedness of types, Φ; Γ ⊢ 𝕎y: σ. τ [s] : max{⊑}(U, Set), so we have
      (4) Φ; Γ ⊢ σ : U,
      (5) Φ; Γ(y: σ) ⊢ τ : U, and
      (6) Φ ⊢ s.
    Then we can construct
      (7) Φ(α < s); Γ(z₁: σ)(z₂: τ[y ↦ z₁] → 𝕎y: σ. τ [α]) ⊢ sup {𝕎y: σ. τ [s]} [α] z₁ z₂ and
      (8) Φ; Γ(z₁: σ) ⊢ τ[y ↦ z₁] : U by term cut,
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
    By term cut, we have ⟦Φ⟧(β: Size)⟦Γ⟧ ⊢ ⟦σ⟧[α ↦ β] : U, so by compositionality, ⟦σ[α ↦ β]⟧ = ⟦σ⟧[α ↦ β].
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
