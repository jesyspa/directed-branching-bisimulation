
From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import formulas.
From bisimulations Require Import reflexive.hmlu.

Section PhmluSemantics.
Context `{ReflSystem : @refl_system X System}.

Inductive PhmluTrue : PhmluFormula → X → Prop :=
  | PhmluTrue_Top p : PhmluTrue ⊤ₚ p
  | PhmluTrue_Conj φ ψ p : PhmluTrue φ p → PhmluTrue ψ p → PhmluTrue (φ ∧ₚ ψ) p
  | PhmluTrue_DisjL φ ψ p : PhmluTrue φ p → PhmluTrue (φ ∨ₚ ψ) p
  | PhmluTrue_DisjR φ ψ p : PhmluTrue ψ p → PhmluTrue (φ ∨ₚ ψ) p
  | PhmluTrue_Diamond l δ ψ χ p q r :
    rtc (can_step silent) p q → can_step l q r →
    PhmluTrue δ q → PhmluTrue ψ r → PhmluFalse χ r →
    PhmluTrue (◇ₚ l δ ψ χ) p
with PhmluFalse : PhmluFormula → X → Prop :=
  | PhmluFalse_Bot p : PhmluFalse ⊥ₚ p
  | PhmluFalse_ConjL φ ψ p : PhmluFalse φ p → PhmluFalse (φ ∧ₚ ψ) p
  | PhmluFalse_ConjR φ ψ p : PhmluFalse ψ p → PhmluFalse (φ ∧ₚ ψ) p
  | PhmluFalse_Disj φ ψ p : PhmluFalse φ p → PhmluFalse ψ p → PhmluFalse (φ ∨ₚ ψ) p
  | PhmluFalse_Diamond l δ ψ χ p :
    (∀ q r, rtc (can_step silent) p q → can_step l q r → PhmluFalse δ q ∨ PhmluFalse ψ r ∨ PhmluTrue χ r) →
    PhmluFalse (◇ₚ l δ ψ χ) p.
End PhmluSemantics.

Global Hint Constructors PhmluTrue : hints hmlu_constructors.
Global Hint Constructors PhmluFalse : hints hmlu_constructors.

Notation "x ⊨ₚ φ" := (PhmluTrue φ x) (at level 60).
Notation "x ⊭ₚ φ" := (PhmluFalse φ x) (at level 60).

Ltac inv_phmlu :=
  progress repeat match goal with
  | H : _ ⊨ₚ ⊤ₚ |- _ => inv H
  | H : _ ⊨ₚ ⊥ₚ |- _ => inv H
  | H : _ ⊨ₚ _ ∧ₚ _ |- _ => inv H
  | H : _ ⊨ₚ _ ∨ₚ _ |- _ => inv H
  | H : _ ⊨ₚ ◇ₚ _ _ _ _ |- _ => inv H
  | H : _ ⊭ₚ ⊤ₚ |- _ => inv H
  | H : _ ⊭ₚ ⊥ₚ |- _ => inv H
  | H : _ ⊭ₚ _ ∧ₚ _ |- _ => inv H
  | H : _ ⊭ₚ _ ∨ₚ _ |- _ => inv H
  | H : _ ⊭ₚ ◇ₚ _ _ _ _ |- _ => inv H
  end.

Section PhmluFacts.
Context `{ReflSystem : @refl_system X System}.

Lemma phmlu_pos_true_extend_backwards p q φ : can_step silent p q → q ⊨ₚ φ → p ⊨ₚ φ.
Proof. induction 2; eauto using rtc_l with hints. Qed.
Lemma phmlu_pos_false_extends_forwards p q φ : can_step silent p q → p ⊭ₚ φ → q ⊭ₚ φ.
Proof. induction 2; eauto using rtc_l with hints. Qed.

Lemma PhmluTrue_to_embed_HmluTrue p φ : p ⊨ₚ φ → p ⊨ₕ embed_phmlu φ
with PhmluFalse_to_embed_HmluFalse p φ : p ⊭ₚ φ → p ⊭ₕ embed_phmlu φ.
Proof. all: destruct φ; simpl; intros H; inv_phmlu; eauto with hints.
  - eapply hmlu_Diamond_True; eauto using rtc_to_path_via_by_pos with hints.
  - eapply PhmluFalse_to_embed_HmluFalse, hmlu_Neg_True in H2.
    eapply PhmluFalse_to_embed_HmluFalse, hmlu_Neg_True in H4.
    eauto with hints.
  - eapply hmlu_Diamond_False. intros q r Hpq Hqr.
    assert (q ⊭ₚ φ1 ∨ r ⊭ₚ φ2 ∨ r ⊨ₚ φ3) as [|[|]] by eauto using path_via_to_rtc;
      eauto with hints.
    exfalso. eapply PhmluFalse_to_embed_HmluFalse in H.
    eapply hmlu_not_true_and_false; [|exact H].
    by eapply path_target_satisfies.
Qed.

Lemma embed_HmluTrue_to_PhmluTrue p φ : p ⊨ₕ embed_phmlu φ → p ⊨ₚ φ
with embed_HmluFalse_PhmluFalse p φ : p ⊭ₕ embed_phmlu φ → p ⊭ₚ φ.
Proof. all: destruct φ; simpl; intros H; inv_hmlu.
  - constructor. 
  - constructor; eauto with hints.
  - eapply PhmluTrue_DisjL; eauto with hints. 
  - eapply PhmluTrue_DisjR; eauto with hints. 
  - eapply (PhmluTrue_Diamond l _ _ _ p x x0); eauto.
    + by eapply path_via_to_rtc. 
    + by eapply embed_HmluTrue_to_PhmluTrue, path_target_satisfies. 
  - constructor. 
  - eapply PhmluFalse_ConjL; eauto with hints. 
  - eapply PhmluFalse_ConjR; eauto with hints. 
  - constructor; eauto with hints. 
  - eapply PhmluFalse_Diamond. intros q r Hpq Hqr.
    destruct (hmlu_true_or_false (embed_phmlu φ1) q); [right|eauto].
    cut (r ⊭ₕ embed_phmlu φ2 ∧ₕ ¬ₕ embed_phmlu φ3).
    { intros. inv_hmlu; eauto with hints. }
    eapply H; try done.
    eapply rtc_to_path_via_by_pos; eauto with hints.
Qed.

End PhmluFacts.