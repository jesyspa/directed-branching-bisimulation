From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import nonreflexive.directed_branching.
From bisimulations Require Import reflexive.directed_branching.

Section NonreflVsRefl.
Context `{System : system X}.

Notation nr_db_dapart := (@nonreflexive.directed_branching.db_dapart X System).
Notation r_db_dapart := (@reflexive.directed_branching.db_dapart X WithRefl).

Theorem nonrefl_to_refl : ∀ p q, nr_db_dapart p q → r_db_dapart p q.
Proof. eapply nonreflexive.directed_branching.db_dapart_strong_ind'.
  - intros p1 p2 q Hp12 Hr_p2q. eapply db_dapart_extend_backwards_one; try done.
    by eapply WithRefl_can_step.
  - intros p q1 HQ. 
    eapply Fwd; [by right|].
    intros q2 Hq12 q3 Hq23. right.
    eapply HQ. rewrite WithRefl_rtc_can_step. eauto with steps.
  - intros p1 p2 q1 Hp12 Ha_q1_p2 HQ.
    assert (Hp12' : WithRefl silent p1 p2) by by eapply WithRefl_can_step.
    eapply Fwd; [done|].
    intros q2 Hq12. rewrite <- WithRefl_rtc_can_step in Hq12.
    intros q3 [Hq23|[_ <-]]; unfold directed_branching.Downstream_relation.
    { specialize (HQ q2 Hq12 q3 Hq23) as [|]; [by left|by right]. }
    eapply rtc_inv_r in Hq12 as [<-|(qm & Hq1m & Hqm2)].
    { right. by right. }
    specialize (HQ qm Hq1m q2 Hqm2) as [|]; [left|by right].
    eapply WithRefl_can_step in Hqm2.
    by eapply db_dapart_extend_forward_one.
  - intros p1 p2 q1 Hp12 HQ.
    assert (Hp12' : @can_step X WithRefl loud p1 p2) by by rewrite <- WithRefl_can_step_loud.
    eapply Fwd; [done|].
    intros q2 Hq12 q3 Hq23.
    rewrite <- WithRefl_rtc_can_step in Hq12.
    rewrite <- WithRefl_can_step_loud in Hq23.
    specialize (HQ q2 Hq12 q3 Hq23) as [|]; [by left|by right].
Qed.

Theorem refl_to_nonrefl : ∀ p q, r_db_dapart p q → nr_db_dapart p q.
Proof. eapply reflexive.directed_branching.db_dapart_strong_ind'.
  intros l p1 p2 q1 [Hp12|[-> <-]] HQ.
  - destruct l. 
    + assert (Hq11 : rtc (@can_step X WithRefl silent) q1 q1) by eapply rtc_refl.
      assert (Hq11' : @can_step X WithRefl silent q1 q1) by by right.
      destruct (HQ q1 Hq11 q1 Hq11') as [|]; [done|]. clear Hq11 Hq11'.
      destruct H; [by eapply nonreflexive.directed_branching.db_dapart_extend_backwards_one|].
      eapply Silent; try done. clear H Hp12.
      intros q2 Hq12 q3 Hq23.
      rewrite WithRefl_rtc_can_step in Hq12.
      eapply WithRefl_can_step in Hq23.
      specialize (HQ q2 Hq12 q3 Hq23) as [|]; [left|right]; done.
    + eapply Loud; try done. clear Hp12.
      intros q2 Hq12 q3 Hq23.
      rewrite WithRefl_rtc_can_step in Hq12.
      rewrite WithRefl_can_step_loud in Hq23.
      specialize (HQ q2 Hq12 q3 Hq23) as [|]; [left|right]; done.
  - eapply SilentRefl.
    intros q2 Hq12.
    rewrite WithRefl_rtc_can_step in Hq12.
    assert (Hq22 : @can_step X WithRefl silent q2 q2) by by right.
    specialize (HQ q2 Hq12 q2 Hq22) as [|]; [by left|done].
Qed.

End NonreflVsRefl.