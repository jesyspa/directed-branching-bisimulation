From bisimulations Require Import prelude.
From bisimulations Require Import system.

(* Hennessy-Milner Logic with Until*)
Inductive HmluFormula : Set :=
  | Top
  | Neg (φ : HmluFormula)
  | Conj (φ ψ : HmluFormula)
  | Diamond (l : label) (δ φ : HmluFormula).

Notation Bot := (Neg Top).
Notation Disj φ ψ := (Neg (Conj (Neg φ) (Neg ψ))).

Notation "⊤ₕ" := Top.
Notation "⊥ₕ" := Bot.
Notation "¬ₕ φ" := (Neg φ) (at level 40).
Notation "φ ∧ₕ ψ" := (Conj φ ψ) (at level 50).
Notation "φ ∨ₕ ψ" := (Disj φ ψ) (at level 50).
Notation "◇ₕ" := Diamond.

(* Positive Hennessy-Milner Logic with Until*)
Inductive PhmluFormula : Set :=
  | PTop | PBot
  | PConj (φ ψ : PhmluFormula) | PDisj (φ ψ : PhmluFormula)
  | PDiamond (l : label) (δ φ ψ : PhmluFormula).

Notation "⊤ₚ" := PTop.
Notation "⊥ₚ" := PBot.
Notation "φ ∧ₚ ψ" := (PConj φ ψ) (at level 50).
Notation "φ ∨ₚ ψ" := (PDisj φ ψ) (at level 50).
Notation "◇ₚ" := PDiamond.

Fixpoint embed_phmlu (φ : PhmluFormula) : HmluFormula :=
  match φ with
  | ⊤ₚ => ⊤ₕ
  | ⊥ₚ => ⊥ₕ
  | φ ∧ₚ ψ => embed_phmlu φ ∧ₕ embed_phmlu ψ
  | φ ∨ₚ ψ => embed_phmlu φ ∨ₕ embed_phmlu ψ
  | ◇ₚ l δ φ ψ => ◇ₕ l (embed_phmlu δ) (embed_phmlu φ ∧ₕ ¬ₕ embed_phmlu ψ)
  end.

Inductive HmluPos : HmluFormula → Prop :=
  | Top_Pos : HmluPos Top
  | Neg_Pos φ : HmluNeg φ → HmluPos (Neg φ)
  | Conj_Pos φ ψ : HmluPos φ → HmluPos ψ → HmluPos (Conj φ ψ)
  | Diamond_Pos l δ φ: HmluPos δ → HmluPos (Diamond l δ φ)
with HmluNeg : HmluFormula → Prop :=
  | Top_Neg : HmluNeg Top
  | Neg_Neg φ : HmluPos φ → HmluNeg (Neg φ)
  | Conj_Neg φ ψ : HmluNeg φ → HmluNeg ψ → HmluNeg (Conj φ ψ).

Inductive HmluGood : HmluFormula → Prop :=
  | Top_Good : HmluGood Top
  | Neg_Good φ : HmluGood φ → HmluGood (Neg φ)
  | Conj_Good φ ψ : HmluGood φ → HmluGood ψ → HmluGood (Conj φ ψ)
  | DiamondGood l δ φ : HmluPos δ → HmluGood δ → HmluGood φ → HmluGood (Diamond l δ φ).

Global Hint Constructors HmluPos : hints.
Global Hint Constructors HmluNeg : hints.
Global Hint Constructors HmluGood : hints.

Ltac inv_polarity :=
  repeat match goal with
  | H : HmluPos ⊤ₕ |- _ => inv H
  | H : HmluPos (¬ₕ _) |- _ => inv H
  | H : HmluPos (_ ∧ₕ _) |- _ => inv H
  | H : HmluPos (◇ₕ _ _ _) |- _ => inv H
  | H : HmluNeg ⊤ₕ |- _ => inv H
  | H : HmluNeg (¬ₕ _) |- _ => inv H
  | H : HmluNeg (_ ∧ₕ _) |- _ => inv H
  | H : HmluNeg (◇ₕ _ _ _) |- _ => inv H
  | H : HmluGood ⊤ₕ |- _ => inv H
  | H : HmluGood (¬ₕ _) |- _ => inv H
  | H : HmluGood (_ ∧ₕ _) |- _ => inv H
  | H : HmluGood (◇ₕ _ _ _) |- _ => inv H
  end.

Lemma hmlu_pos_neg_rewrite φ : HmluPos (¬ₕ φ) ↔ HmluNeg φ.
Proof. split; intros; inv_polarity; [done|by constructor]. Qed.
Lemma hmlu_neg_neg_rewrite φ : HmluNeg (¬ₕ φ) ↔ HmluPos φ.
Proof. split; intros; inv_polarity; [done|by constructor]. Qed.
Lemma hmlu_pos_conj_rewrite φ ψ : HmluPos (φ ∧ₕ ψ) ↔ HmluPos φ ∧ HmluPos ψ.
Proof. split; intros; inv_polarity; [done|destruct H; by constructor]. Qed.
Lemma hmlu_neg_conj_rewrite φ ψ : HmluNeg (φ ∧ₕ ψ) ↔ HmluNeg φ ∧ HmluNeg ψ.
Proof. split; intros; inv_polarity; [done|destruct H; by constructor]. Qed.
Hint Rewrite hmlu_pos_neg_rewrite : hints.
Hint Rewrite hmlu_neg_neg_rewrite : hints.
Hint Rewrite hmlu_pos_conj_rewrite : hints.
Hint Rewrite hmlu_neg_conj_rewrite : hints.

Lemma phmlu_embedding_positive {φ} : HmluPos (embed_phmlu φ).
Proof. induction φ; unfold embed_phmlu; eauto with hints. Qed.
Global Hint Resolve phmlu_embedding_positive : hints.
Lemma phmlu_embedding_good {φ} : HmluGood (embed_phmlu φ).
Proof. induction φ; unfold embed_phmlu; eauto with hints. Qed.
Global Hint Resolve phmlu_embedding_good : hints.
