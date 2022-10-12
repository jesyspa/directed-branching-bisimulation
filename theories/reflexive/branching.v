From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.

Section Branching.
Context `{ReflSystem : @refl_system X System}.

Inductive b_apart : X -> X -> Prop :=
  | b_apart_sym p q : b_apart p q -> b_apart q p
  | b_apart_step l p1 p2 q :
    can_step l p1 p2 →
    Downstream_property l (LL_RR_relation p1 p2) b_apart q →
    b_apart p1 q.
Hint Constructors b_apart : hints.

Theorem b_apart_strong_ind :
  ∀ (P : X → X → Prop),
    (∀ p q, b_apart p q → P p q → P q p) →
    (∀ l p1 p2 q,
      can_step l p1 p2 →
      Downstream_property l (LL_RR_relation p1 p2) (rel_join b_apart P) q →
      P p1 q) → 
    ∀ p q, b_apart p q → P p q.
Proof.
  intros P CaseSym CaseStep.
  fix IH 3.
  intros p1 q1 H.
  inv H as [p' q' Hqp|l' p1' p2 q' Hs_p1_p2 HQ].
  - eapply CaseSym; [done|by eapply IH]. 
  - eapply CaseStep; try done.
    intros q2 Hs_q1_q2 q3 Hs_q2_q3.
    destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [H|H]; [left|right];
      (split; [done| by eapply IH]).
Qed.

Theorem b_apart_strong_ind' :
  ∀ (P : X → X → Prop),
    (∀ p q, P p q → P q p) →
    (∀ l p1 p2 q,
      can_step l p1 p2 →
      Downstream_property l (LL_RR_relation p1 p2) P q →
      P p1 q) → 
    ∀ p q, b_apart p q → P p q.
Proof.
  intros P CaseSym CaseStep.
  eapply b_apart_strong_ind; eauto with hints; intros; eapply CaseStep; eauto;
    eapply Downstream_property_closed_implication; [eapply LL_RR_relation_MBRT| |done];
    unfold rel_join; tauto.
Qed.

End Branching.

Global Hint Constructors b_apart : hints.