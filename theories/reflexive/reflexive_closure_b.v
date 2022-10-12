From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import nonreflexive.semibranching.
From bisimulations Require Import reflexive.branching.

Section NonreflVsRefl.
Context `{System : system X}.

Notation nr_sb_apart := (@nonreflexive.semibranching.sb_apart X System).
Notation r_b_apart := (@reflexive.branching.b_apart X WithRefl).

Theorem nonrefl_to_refl : ∀ p q, nr_sb_apart p q → r_b_apart p q.
Proof. eapply nonreflexive.semibranching.sb_apart_strong_ind'; [eauto with hints|..].
  - intros p1 p2 q1 Hp12 Ha_p2_q1 HQ.
    eapply reflexive.branching.b_apart_step; [by eapply WithRefl_can_step|].
    intros q2 Hq12 q3 Hq23.
    rewrite <- WithRefl_rtc_can_step in Hq12.
    destruct Hq23 as [Hq23|[_ <-]].
    { by destruct (HQ q2 Hq12 q3 Hq23) as [[]|]; [left|right]. }
    eapply rtc_inv_r in Hq12 as [<-|(qm & Hq1m & Hqm2)].
    { by right. }
    by destruct (HQ qm Hq1m q2 Hqm2) as [[]|]; [left|right].
  - intros p1 p2 q1 Hp12 HQ. 
    eapply reflexive.branching.b_apart_step; [by eapply WithRefl_can_step|].
    intros q2 Hq12 q3 Hq23.
    rewrite <- WithRefl_rtc_can_step in Hq12.
    rewrite <- WithRefl_can_step_loud in Hq23.
    by destruct (HQ q2 Hq12 q3 Hq23); [left|right].
Qed.

Theorem refl_to_nonrefl : ∀ p q, r_b_apart p q → nr_sb_apart p q.
Proof. eapply reflexive.branching.b_apart_strong_ind'; [eauto with hints|intros [] p1 p2 q1 Hp12 HQ].
  - assert (rtc (@can_step X WithRefl silent) q1 q1) as Hq11 by eauto with steps.
    assert (@can_step X WithRefl silent q1 q1) as Hq11' by by right.
    destruct (HQ q1 Hq11 q1 Hq11'); try done.
    destruct Hp12 as [Hp12|[_ <-]]; [|done].
    eapply sb_apart_silent; try done. 
    intros q2 Hq12 q3 Hq23.
    rewrite WithRefl_rtc_can_step in Hq12.
    eapply WithRefl_can_step in Hq23. 
    assert (rtc (@can_step X WithRefl silent) q1 q3) as Hq13 by eauto with steps.
    assert (@can_step X WithRefl silent q3 q3) as Hq33' by by right.
    destruct (HQ q3 Hq13 q3 Hq33') as [|]; [|by right].
    destruct (HQ q2 Hq12 q3 Hq23) as [|]; [left|right]; eauto with hints.
  - eapply WithRefl_can_step_loud in Hp12.
    eapply sb_apart_loud; try done. 
    intros q2 Hq12 q3 Hq23.
    rewrite WithRefl_rtc_can_step in Hq12.
    eapply WithRefl_can_step_loud in Hq23.
    by destruct (HQ q2 Hq12 q3 Hq23) as [|]; [left|right].
Qed.

End NonreflVsRefl.