From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.

Section Branching.
Context `{System : system X}.

Notation Silent_property R p1 p2 := (Downstream_property silent (LL_RR_relation p1 p2) R).
Notation Loud_property R p1 p2 := (Downstream_property loud (LL_RR_relation p1 p2) R).

Inductive b_apart : X -> X -> Prop :=
  | b_apart_sym p q : b_apart p q -> b_apart q p
  | b_apart_silent p1 p2 q :
    can_step silent p1 p2 →
    b_apart p2 q →
    Silent_property b_apart p1 p2 q →
    b_apart p1 q
  | b_apart_loud p1 p2 q :
    can_step loud p1 p2 →
    Loud_property b_apart p1 p2 q →
    b_apart p1 q.
Hint Constructors b_apart : hints.

Theorem b_apart_strong_ind :
  ∀ (P : X → X → Prop),
    (∀ p q, b_apart p q → P p q → P q p) →
    (∀ p1 p2 q,
      can_step silent p1 p2 →
      b_apart p2 q →
      P p2 q →
      Silent_property (rel_join b_apart P) p1 p2 q →
      P p1 q) → 
    (∀ p1 p2 q,
      can_step loud p1 p2 →
      Loud_property (rel_join b_apart P) p1 p2 q →
      P p1 q) → 
    ∀ p q, b_apart p q → P p q.
Proof.
  intros P CaseSym CaseSilent CaseLoud.
  fix IH 3.
  intros p1 q1 H.
  inv H as [p' q' Hqp|p1' p2 q' Hs_p1_p2 Ha_p2_q HQ|p1' p2 q' s HQ].
  - eapply CaseSym; [done|by eapply IH]. 
  - eapply CaseSilent; try done; [by eapply IH|].
    intros q2 Hs_q1_q2 q3 Hs_q2_q3.
    destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [H|H]; [left|right];
    (split; [done| by eapply IH]).
  - eapply CaseLoud; try done.
    intros q2 Hs_q1_q2 q3 Hs_q2_q3.
    destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [H|H]; [left|right];
    (split; [done| by eapply IH]).
Qed.

Theorem b_apart_strong_ind' :
  ∀ (P : X → X → Prop),
    (∀ p q, P p q → P q p) →
    (∀ p1 p2 q,
      can_step silent p1 p2 →
      P p2 q →
      Silent_property P p1 p2 q →
      P p1 q) → 
    (∀ p1 p2 q,
      can_step loud p1 p2 →
      Loud_property P p1 p2 q →
      P p1 q) → 
    ∀ p q, b_apart p q → P p q.
Proof.
  intros P CaseSym CaseSilent CaseLoud.
  eapply b_apart_strong_ind; eauto with hints; intros; [eapply CaseSilent|eapply CaseLoud]; eauto;
    (eapply Downstream_property_closed_implication; [eapply LL_RR_relation_MBRT| |done]);
    unfold rel_join; tauto.
Qed.

End Branching.

Global Hint Constructors b_apart : hints.