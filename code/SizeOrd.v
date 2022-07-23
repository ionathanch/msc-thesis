From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8_core.

Reserved Notation "r ≤ s" (at level 70, no associativity).

Inductive Size : Type :=
| suc : Size → Size
| lim : ∀ {A : Type}, (A → Size) → Size.

Inductive Leq : Size → Size → Type :=
| mono : ∀ {r s}, r ≤ s → suc r ≤ suc s
| cocone : ∀ {s A f} (a : A), s ≤ f a → s ≤ lim f
| limiting : ∀ {s A f}, (∀ (a : A), f a ≤ s) → lim f ≤ s
where "r ≤ s" := (Leq r s).

Definition Lt r s : Type := suc r ≤ s.
Notation "r < s" := (Lt r s).

Definition base : Size := lim (False_rect Size).

Definition baseLeq s : base ≤ s :=
  limiting (λ a, (False_rect (_ ≤ s) a)).

Fixpoint reflLeq {s} : s ≤ s :=
  match s with
  | suc s => mono reflLeq
  | lim f => limiting (λ a, cocone a reflLeq)
  end.

Property transLeq {r s t} (rs : r ≤ s) (st : s ≤ t) : r ≤ t.
Admitted.

(*
Derive NoConfusion for Size.
Equations transLeq {r s t : Size} (rs : r ≤ s) (st : s ≤ t) : r ≤ t :=
  transLeq (mono rs) (mono st) := mono (transLeq rs st);
  transLeq rs (cocone a sfa) := cocone a (transLeq rs sfa);
  transLeq (limiting fas) st := limiting (λ a, transLeq (fas a) st);
  transLeq (cocone a rfa) (limiting fat) := transLeq rfa (fat a).
*)

Fixpoint sucLeq s : s ≤ suc s :=
  match s with
  | suc s => mono (sucLeq s)
  | lim f => limiting (λ a, transLeq (sucLeq (f a)) (mono (cocone a reflLeq)))
  end.

Inductive Acc (s : Size) : Prop :=
acc { accLt : ∀ r, r < s → Acc r }.
Arguments accLt {_}.

Axiom funext : ∀ {A} {B : A → Type} {p q : ∀ x, B x},
  (∀ x, p x = q x) → p = q.

Equations accIsProp {s} (acc1 acc2 : Acc s) : acc1 = acc2 :=
| acc _ p, acc _ q =>
  f_equal _ (funext (λ r, funext (λ rs, accIsProp (p r rs) (q r rs)))).

Lemma accLeq : ∀ r s, r ≤ s → Acc s → Acc r.
Proof.
  intros r s rs acc.
  induction acc as [s p IH].
  exact (acc r (λ t tr, p t (transLeq tr rs))).
Qed.

Theorem wf : ∀ s, Acc s.
Proof.
  intros s.
  induction s as [s IH | A f IH].
  - refine (acc (suc s) (λ r rsucs, accLeq r s _ IH)).
    inversion rsucs as [r' s' rs | |].
    exact rs.
  - refine (acc (lim f) (λ r rlimf, _)).
    inversion rlimf as [| r' A' f' a rfa eqr eqA |].
    dependent destruction H.
    destruct (IH a) as [p].
    exact (p r rfa).
Qed.

Definition wfInd P IH s : P s :=
  let wfInd := fix wfAcc s acc {struct acc} :=
    IH s (λ r rs, wfAcc r (acc.(accLt) r rs))
  in wfInd s (wf s).

Import SigTNotations.

Inductive W (A : Type) (B : A → Type) (s : Size) : Type :=
| sup : ∀ r, r < s → ∀ a, (B a → W A B r) → W A B s.
Arguments sup {_ _ _}.

Definition ac {A B} a (f : B a → {s & W A B s}) : {s & B a → W A B s} :=
  let f' b :=
    match (f b).2 with
    | sup r rs a f => sup r (transLeq rs (cocone b reflLeq)) a f
    end
  in (lim (λ b, (f b).1) ; f').

Equations limN (n : nat) : Size :=
| O => base
| S n => suc (limN n).

Definition infN : Size := lim limN.

Inductive WInf (A : Type) (B : A → Type) : Type :=
| sup' : ∀ a, (B a → WInf A B) → WInf A B.

Equations limW {A} {B} (w : WInf A B) : Size :=
| sup' a f => lim (λ b, limW (f b)).

Definition infW {A} {B} : Size := lim (@limW A B).