From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import formulas.

Section HmluValuationDef.
Context `{ReflSystem : @refl_system X System}.

(* We can't do this via an Inductive because the path_via uses HmluTrue in a non-positive position. *)
Fixpoint HmluTrue (φ : HmluFormula) (p : X) : Prop :=
  match φ with
  | ⊤ₕ => True
  | ¬ₕ φ => HmluFalse φ p
  | φ ∧ₕ ψ => HmluTrue φ p ∧ HmluTrue ψ p
  | ◇ₕ l δ ψ => ∃ q r, path_via (can_step silent) (HmluTrue δ) p q ∧ can_step l q r ∧ HmluTrue ψ r
  end
with HmluFalse (φ : HmluFormula) (p : X) : Prop :=
  match φ with
  | ⊤ₕ => False
  | ¬ₕ φ => HmluTrue φ p
  | φ ∧ₕ ψ => HmluFalse φ p ∨ HmluFalse ψ p
  | ◇ₕ l δ ψ => ∀ q r, path_via (can_step silent) (HmluTrue δ) p q → can_step l q r → HmluFalse ψ r
  end.

Lemma hmlu_not_true_and_false φ p : HmluTrue φ p → HmluFalse φ p → False.
Proof. revert p. simpl. induction φ; intros p HT HF; eauto.
  - destruct HT, HF; eauto.
  - destruct HT as (q & r & Hpq & Hqr & Hr). eauto.
Qed.

End HmluValuationDef.

Notation "x ⊨ₕ φ" := (HmluTrue φ x) (at level 60).
Notation "x ⊭ₕ φ" := (HmluFalse φ x) (at level 60).

Section HmluFacts.
Context `{ReflSystem : @refl_system X System}.

Lemma hmlu_Top_True p : p ⊨ₕ ⊤ₕ.
Proof. done. Qed.
Lemma hmlu_Neg_True p φ : p ⊭ₕ φ → p ⊨ₕ ¬ₕ φ.
Proof. done. Qed.
Lemma hmlu_Neg_True_inv p φ : p ⊨ₕ ¬ₕ φ → p ⊭ₕ φ.
Proof. done. Qed.
Lemma hmlu_Conj_True p φ ψ : p ⊨ₕ φ → p ⊨ₕ ψ → p ⊨ₕ φ ∧ₕ ψ.
Proof. done. Qed.
Lemma hmlu_Diamond_True {l δ ψ p q r} :
  path_via (can_step silent) (HmluTrue δ) p q → can_step l q r → HmluTrue ψ r → HmluTrue (◇ₕ l δ ψ) p.
Proof. unfold HmluTrue. eauto. Qed.
Lemma hmlu_Diamond_True_inv {l δ ψ p} :
  HmluTrue (◇ₕ l δ ψ) p → ∃ q r, path_via (can_step silent) (HmluTrue δ) p q ∧ can_step l q r ∧ HmluTrue ψ r.
Proof. unfold HmluTrue. eauto. Qed.
Lemma hmlu_Neg_False p φ : p ⊨ₕ φ → p ⊭ₕ ¬ₕ φ.
Proof. done. Qed.
Lemma hmlu_Neg_False_inv p φ : p ⊭ₕ ¬ₕ φ → p ⊨ₕ φ.
Proof. done. Qed.
Lemma hmlu_ConjL_False p φ ψ : p ⊭ₕ φ → p ⊭ₕ φ ∧ₕ ψ.
Proof. by left. Qed.
Lemma hmlu_ConjR_False p φ ψ : p ⊭ₕ ψ → p ⊭ₕ φ ∧ₕ ψ.
Proof. by right. Qed.
Lemma hmlu_Diamond_False {l δ ψ p} :
  (∀ q r, path_via (can_step silent) (HmluTrue δ) p q → can_step l q r → r ⊭ₕ ψ) → p ⊭ₕ (◇ₕ l δ ψ).
Proof. unfold HmluFalse. tauto. Qed.
Lemma hmlu_Diamond_False_inv {l δ ψ p q r} :
  p ⊭ₕ (◇ₕ l δ ψ) → path_via (can_step silent) (HmluTrue δ) p q → can_step l q r → r ⊭ₕ ψ.
Proof. unfold HmluFalse. intros. fold HmluFalse HmluTrue in *. eauto. Qed.
Lemma hmlu_Diamond_False_iff {l δ ψ p} :
  p ⊭ₕ (◇ₕ l δ ψ) ↔ ∀ q r, path_via (can_step silent) (HmluTrue δ) p q → can_step l q r → r ⊭ₕ ψ.
Proof. split; intros; [eapply hmlu_Diamond_False_inv|eapply hmlu_Diamond_False]; eauto. Qed.
End HmluFacts.

Create HintDb hmlu_constructors.
Global Hint Resolve hmlu_Top_True : hints hmlu_constructors.
Global Hint Resolve hmlu_Neg_True : hints hmlu_constructors.
Global Hint Resolve hmlu_Conj_True : hints hmlu_constructors.
Global Hint Resolve hmlu_Diamond_True : hints hmlu_constructors.
Global Hint Resolve hmlu_Neg_False : hints hmlu_constructors.
Global Hint Resolve hmlu_ConjL_False : hints hmlu_constructors.
Global Hint Resolve hmlu_ConjR_False : hints hmlu_constructors.
Global Hint Resolve hmlu_Diamond_False : hints hmlu_constructors.

Ltac inv_hmlu :=
  progress repeat match goal with
  | H : _ ⊨ₕ ⊤ₕ |- _ => clear H
  | H : _ ⊨ₕ ¬ₕ _ |- _ => apply hmlu_Neg_True_inv in H
  | H : _ ⊨ₕ _ ∧ₕ _ |- _ => destruct H
  | H : _ ⊨ₕ ◇ₕ _ _ _ |- _ => destruct (hmlu_Diamond_True_inv H) as (? & ? & ? & ? & ?); clear H
  | H : _ ⊭ₕ ⊤ₕ |- _ => exfalso; exact H
  | H : _ ⊭ₕ ¬ₕ _ |- _ => apply hmlu_Neg_False_inv in H
  | H : _ ⊭ₕ _ ∧ₕ _ |- _ => destruct H
  | H : _ ⊭ₕ ◇ₕ _ _ _ |- _ => rewrite hmlu_Diamond_False_iff in H
  end; try fold HmluFalse HmluTrue in *.

Section HmluFacts.
Context `{System : system X}.

Lemma hmlu_true_or_false φ p : HmluTrue φ p ∨ HmluFalse φ p.
Proof. revert p; induction φ; intros p.
  - by left. 
  - destruct (IHφ p); eauto with hints.
  - destruct (IHφ1 p), (IHφ2 p); eauto with hints.
  - destruct (LEM (∃ q r, path_via (can_step silent) (HmluTrue φ1) p q ∧ can_step l q r ∧ r ⊨ₕ φ2));
      [left; eauto with hints|right].
    apply hmlu_Diamond_False. intros q r Hpq Hqr.
    destruct (IHφ2 r); [exfalso|done].
    apply H. eauto.
Qed.

Lemma hmlu_good_ind (P : HmluFormula → Prop) :
  P ⊤ₕ →
  (∀ φ, P φ → P (¬ₕ φ)) →
  (∀ φ ψ, P φ → P ψ → P (φ ∧ₕ ψ)) →
  (∀ l δ φ, HmluPos δ → P δ → P φ → P (◇ₕ l δ φ)) →
  ∀ φ, HmluGood φ → P φ.
Proof.
  intros Htop Hneg Hconj Hdiam φ. induction φ; intros; inv_polarity; eauto.
Qed.

Lemma pos_true_extend_backwards p q φ : HmluPos φ → can_step silent p q → q ⊨ₕ φ → p ⊨ₕ φ
with neg_true_extends_forwards p q φ : HmluNeg φ → can_step silent p q → p ⊨ₕ φ → q ⊨ₕ φ
with pos_false_extends_forwards p q φ : HmluPos φ → can_step silent p q → p ⊭ₕ φ → q ⊭ₕ φ
with neg_false_extends_backwards p q φ : HmluNeg φ → can_step silent p q → q ⊭ₕ φ → p ⊭ₕ φ.
Proof.
  all: intros Hpos Hstep HT; destruct φ; inv_hmlu; inv_polarity; eauto with hmlu_constructors.
  - assert (q ⊨ₕ φ1) by by eapply path_source_satisfies.
    eapply hmlu_Diamond_True; try done.
    eapply path_via_l; eauto with hints steps.
  - eapply hmlu_Diamond_False.
    intros q' r Hq Hqr. eapply HT; try done. 
    eapply path_via_l; eauto with hints steps.
    eapply pos_true_extend_backwards; try done.
    by eapply path_source_satisfies.
Qed.

Lemma rtc_to_path_via_by_pos {δ p q} :
  HmluPos δ → rtc (can_step silent) p q → q ⊨ₕ δ → path_via (can_step silent) (HmluTrue δ) p q.
Proof. intros Hδ. eapply rtc_to_path_via. intros. by eapply pos_true_extend_backwards. Qed.

End HmluFacts.
