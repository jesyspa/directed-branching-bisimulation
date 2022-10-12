From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import nonreflexive.branching.
From bisimulations Require Import nonreflexive.semibranching.

(* We show that the *nonreflexive* definitions of branching and semibranching
   are trivially equivalent in the reflexive setting. *)
Section BranchingVsSemibranching.
Context `{ReflSystem : @refl_system X System}.

Theorem branching_to_semibranching : ∀ p q, b_apart p q → sb_apart p q.
Proof. eapply b_apart_strong_ind'; eauto using sb_apart_sym, sb_apart_loud.
  intros p1 p2 q1 Hp12 Ha_p2_q1 HQ. eapply sb_apart_silent; eauto with hints.
  unfold Downstream_property in *.
  intros q2 Hq12 q3 Hq23. unfold LLR_RR_relation.
  destruct (HQ q2 Hq12 q3 Hq23) as [HL|HR]; [|tauto].
  assert (rtc (can_step silent) q1 q3) as Hq13 by eauto with steps.
  assert (can_step silent q3 q3) as Hq33 by eapply refl_can_step.
  destruct (HQ q3 Hq13 q3 Hq33) as [HL'|HR]; tauto.
Qed.

Theorem semibranching_to_branching : ∀ p q, sb_apart p q → b_apart p q.
Proof. eapply sb_apart_strong_ind'; eauto using b_apart_sym, b_apart_loud.
  intros p1 p2 q1 Hp12 Ha_p2_q1 HQ. eapply b_apart_silent; eauto with hints.
  unfold Downstream_property in *.
  eapply persistently_for_all_steps_closed_implication_weak; [|done].
  unfold LLR_RR_relation, LL_RR_relation. tauto.
Qed.

End BranchingVsSemibranching.
