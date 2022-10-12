From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import formulas.
From bisimulations Require Import reflexive.directed_branching.
From bisimulations Require Import reflexive.hmlu.
From bisimulations Require Import reflexive.phmlu.

Section Distinguish.
Context `{ReflSystem : @refl_system X System}.

Record DADist φ (p q : X) : Prop := mkDADist
{ NoPolarity : sc db_dapart p q
; PosPolarity : HmluPos φ → db_dapart p q
; NegPolarity : HmluNeg φ → db_dapart q p
}.

Lemma neg_da_dist {φ p q} : DADist φ p q → DADist (¬ₕ φ) q p.
Proof. intros [HNP HPos HNeg]. constructor; [by symmetry|..]; by autorewrite with hints. Qed.
Lemma conj_left_da_dist {φ ψ p q} : DADist φ p q → DADist (φ ∧ₕ ψ) p q.
Proof. intros [HNP HPos HNeg]. constructor; [by symmetry|..]; autorewrite with hints; intros []; eauto. Qed.
Lemma conj_right_da_dist {φ ψ p q} : DADist ψ p q → DADist (φ ∧ₕ ψ) p q.
Proof. intros [HNP HPos HNeg]. constructor; [by symmetry|..]; autorewrite with hints; intros []; eauto. Qed.
Lemma diam_simple_da_dist {l δ φ p q} : db_dapart p q → DADist (◇ₕ l δ φ) p q.
Proof. intros Hpq. constructor; [by left|by intros|]. intros. inv_polarity. Qed.
Lemma diam_left_da_dist {l δ φ p q} : DADist δ p q → DADist (◇ₕ l δ φ) p q.
Proof. intros [HNP HPos HNeg]. constructor; [done|..]; intros; inv_polarity; eauto. Qed.

Hint Resolve neg_da_dist : hints.
Hint Resolve conj_left_da_dist : hints.
Hint Resolve conj_right_da_dist : hints.
Hint Resolve diam_simple_da_dist : hints.
Hint Resolve diam_left_da_dist : hints.

Lemma good_distinguish_gives_apartness_impl {p q φ} : HmluGood φ → p ⊨ₕ φ → q ⊭ₕ φ → DADist φ p q.
Proof.
  intros Hgood. revert φ Hgood p q.
  eapply (hmlu_good_ind (λ φ, ∀ p q, p ⊨ₕ φ → q ⊭ₕ φ → DADist φ p q)); simpl.
  - by intros.
  - eauto with hints.
  - intros φ ψ IHφ IHψ p q [Hpφ Hpψ] [Hqφ|Hqψ]; eauto with hints.
  - intros l δ φ Hδ IHδ IHφ p q Hp Hq. inv_hmlu; fold HmluTrue HmluFalse in *.
    rename p into p1, x into p2, x0 into p3, H into Hp12, H0 into Hp23, H1 into Hp3.
    eapply diam_simple_da_dist. induction Hp12; [|by eapply db_dapart_extend_backwards_one; eauto].
    eapply Fwd; try done. intros q2 Hq12 q3 Hq23.
    destruct (hmlu_true_or_false δ q2); [right|left; by eapply IHδ].
    eapply NoPolarity, IHφ; try done.
    eapply Hq; try done.
    by eapply rtc_to_path_via_by_pos.
Qed.

Theorem good_distinguish_gives_apartness {p q φ} : HmluGood φ → p ⊨ₕ φ → q ⊭ₕ φ → sc db_dapart p q.
Proof. intros. eauto using NoPolarity, good_distinguish_gives_apartness_impl. Qed.
Theorem good_distinguish_gives_apartness_pos {p q φ} : HmluGood φ → HmluPos φ → p ⊨ₕ φ → q ⊭ₕ φ → db_dapart p q.
Proof. intros. eauto using PosPolarity, good_distinguish_gives_apartness_impl. Qed.
Theorem good_distinguish_gives_apartness_neg {p q φ} : HmluGood φ → HmluNeg φ → p ⊨ₕ φ → q ⊭ₕ φ → db_dapart q p.
Proof. intros. eauto using NegPolarity, good_distinguish_gives_apartness_impl. Qed.

End Distinguish.