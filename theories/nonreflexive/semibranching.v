From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.

Section SemibranchingDef.
Context `{System : system X}.

Notation Silent_property R p1 p2 := (Downstream_property silent (LLR_RR_relation p1 p2) R).
Notation Loud_property R p1 p2 := (Downstream_property loud (LL_RR_relation p1 p2) R).

Inductive sb_apart : X -> X -> Prop :=
  | sb_apart_sym p q : sb_apart p q -> sb_apart q p
  | sb_apart_silent p1 p2 q :
    can_step silent p1 p2 →
    sb_apart p2 q →
    Silent_property sb_apart p1 p2 q →
    sb_apart p1 q
  | sb_apart_loud p1 p2 q :
    can_step loud p1 p2 →
    Loud_property sb_apart p1 p2 q →
    sb_apart p1 q.
Hint Constructors sb_apart : hints.

Theorem sb_apart_strong_ind :
  ∀ (P : X → X → Prop),
    (∀ p q, sb_apart p q → P p q → P q p) →
    (∀ p1 p2 q,
      can_step silent p1 p2 →
      sb_apart p2 q →
      P p2 q →
      Silent_property (rel_join sb_apart P) p1 p2 q →
      P p1 q) → 
    (∀ p1 p2 q,
      can_step loud p1 p2 →
      Loud_property (rel_join sb_apart P) p1 p2 q →
      P p1 q) → 
    ∀ p q, sb_apart p q → P p q.
Proof.
  intros P CaseSym CaseSilent CaseLoud.
  fix IH 3.
  intros p1 q1 H.
  inv H as [p' q' Hqp|p1' p2 q' Hs_p1_p2 Ha_p2_q HQ|p1' p2 q' s HQ].
  - eapply CaseSym; [done|by eapply IH]. 
  - eapply CaseSilent; try done; [by eapply IH|].
    intros q2 Hs_q1_q2 q3 Hs_q2_q3.
    destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [[HA HB]|H]; [left; split|right];
    (split; [done| by eapply IH]).
  - eapply CaseLoud; try done.
    intros q2 Hs_q1_q2 q3 Hs_q2_q3.
    destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [H|H]; [left|right];
    (split; [done| by eapply IH]).
Qed.

Theorem sb_apart_strong_ind' :
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
    ∀ p q, sb_apart p q → P p q.
Proof.
  intros P CaseSym CaseSilent CaseLoud.
  eapply sb_apart_strong_ind; eauto; intros; [eapply CaseSilent|eapply CaseLoud]; eauto.
  - eapply Downstream_property_closed_implication; [eapply LLR_RR_relation_MBRT| |done].
    unfold rel_join; tauto.
  - eapply Downstream_property_closed_implication; [eapply LL_RR_relation_MBRT| |done].
    unfold rel_join; tauto.
Qed.

Lemma sb_apart_nsteps_silent_gen n {p1 p2 p3 q1} :
  nsteps (can_step silent) n p1 p2 →
  can_step silent p2 p3 →
  sb_apart p3 q1 →
  Silent_property sb_apart p2 p3 q1 →
  ∀ {qf}, rtc (can_step silent) q1 qf -> sb_apart p1 qf.
Proof.
  intros Hp12 Hp23 Ha_p3_q1 HQ. revert p1 Hp12.
  induction n as [n IH] using lt_wf_ind.
  intros p1 Hs_p1_p2.
  (* Induction on number of steps from q1 to qf *)
  eapply (rtc_ind_r (λ qf, sb_apart p1 qf)).
  (* Base case: zero steps, we are essentially proving sb_apart_nsteps_silent *)
  - (* The case when n = 0 is the usual rule. *)
    destruct n as [|k];
    inv Hs_p1_p2 as [|z1 z2 p1b z3 Hs_p1_p1b Hs_p1b_p2].
    { eauto with hints. }
    assert (k < S k) as H_k_Sk by lia.
    eauto 8 with hints steps.
  (* Inductive case: We know this for q2, and are proving it for a silent-successor q3. *)
  - intros q2 q3 Hs_q1_q2 Hs_q2_q3 Ha_p1_q2.
    assert (rtc (can_step silent) q1 q3) as Hs_q1_q3 by eauto with steps.
    destruct n as [|k]; inv Hs_p1_p2 as [|z1 z2 p1b z3 Hs_p1_p1b Hs_p1b_p2].
    (* Base case: no silent steps, this is just the usual rule. *)
    + destruct (HQ q2 Hs_q1_q2 q3 Hs_q2_q3) as [[Ha_p2_q2 Ha_p2_q3]|Ha_p3_q3]; [done|].
      (* Left case is trivial since our goal is p2 # p3, we show right case by taking a step. *)
      eauto 7 with hints steps.
    (* Inductive case: we need to show that taking a step is safe, but this is easy
       since we've generalised the IH so we know p1b is apart from every successor of q1. *)
    + assert (k < S k) as H_k_Sk by lia.
      assert (∀ qf, rtc (can_step silent) q1 qf → sb_apart p1b qf) as Ha_p1b_qf by eauto with hints.
      eapply sb_apart_silent; eauto with hints steps.
      intros q4 Hs_q3_q4 q5 Hs_q4_q5.
      right.
      eapply Ha_p1b_qf. eauto using rtc_transitive with steps.
Qed.

Lemma sb_apart_nsteps_silent n {p1 p2 p3 q1} :
  nsteps (can_step silent) n p1 p2 →
  can_step silent p2 p3 →
  sb_apart p3 q1 →
  Silent_property sb_apart p2 p3 q1 →
  sb_apart p1 q1.
Proof. intros. by eapply sb_apart_nsteps_silent_gen. Qed.

Lemma sb_apart_nsteps_loud n {p1 p2 p3 q1} :
  nsteps (can_step silent) n p1 p2 →
  can_step loud p2 p3 →
  Loud_property sb_apart p2 p3 q1 →
  sb_apart p1 q1.
Proof.
  intros Hsteps Hl_p2_p3. revert q1.
  induction Hsteps as [pf|n p1 p2 pf IH Hs_p1_p2 Hs_p2_pf]
    using nsteps_ind_strong_l; intros q1 HQ.
  { by eapply sb_apart_loud. }
  eapply sb_apart_silent; eauto with steps hints.
  intros q2 Hs_q1_q2 q3 Hs_q2_q3.
  right.
  eauto with steps hints.
Qed.

Lemma sb_apart_silent_gen {p1 p2 p3 q1 q2} :
  rtc (can_step silent) p1 p2 →
  can_step silent p2 p3 →
  rtc (can_step silent) q1 q2 →
  sb_apart p3 q1 →
  Silent_property sb_apart p2 p3 q1 →
  sb_apart p1 q2.
Proof.
  intros Hs_p1_p2 Hs_p2_p3 Hs_q1_q2 Ha HQ1.
  eapply rtc_nsteps_1 in Hs_p1_p2 as [n Hs_p1_p2].
  eapply sb_apart_nsteps_silent_gen; try done.
Qed.

Lemma sb_apart_loud_gen {p1 p2 p3 q1 q2} :
  rtc (can_step silent) p1 p2 →
  can_step loud p2 p3 →
  rtc (can_step silent) q1 q2 →
  Loud_property sb_apart p2 p3 q1 →
  sb_apart p1 q2.
Proof.
  intros Hs_p1_p2 Hl_p2_p3 Hs_q1_q2 HQ1.
  eapply rtc_nsteps_1 in Hs_p1_p2 as [n Hs_p1_p2].
  eapply sb_apart_nsteps_loud; eauto with hints.
Qed.

Lemma sb_apart_silent_rtc_before {p1 p2 p3 q1}  :
  rtc (can_step silent) p1 p2 →
  can_step silent p2 p3 →
  sb_apart p3 q1 →
  Silent_property sb_apart p2 p3 q1 →
  sb_apart p1 q1.
Proof.
  intros Hsteps.
  eapply rtc_nsteps_1 in Hsteps as [n Hsteps].
  by eapply sb_apart_nsteps_silent.
Qed.

Lemma sb_apart_loud_rtc_before {p1 p2 p3 q1} :
  rtc (can_step silent) p1 p2 →
  can_step loud p2 p3 →
  Loud_property sb_apart p2 p3 q1 →
  sb_apart p1 q1.
Proof.
  intros Hsteps.
  eapply rtc_nsteps_1 in Hsteps as [n Hsteps].
  by eapply sb_apart_nsteps_loud.
Qed.

Inductive Sufficient : X → X → Prop :=
  | SilentSufficient p1 p2 q :
      can_step silent p1 p2 →
      sb_apart p2 q →
      Silent_property sb_apart p1 p2 q →
      Sufficient p1 q
  | SilentReflSufficient p q :
      persistently (sb_apart p) q →
      Sufficient p q
  | LoudSufficient p1 p2 q :
      can_step loud p1 p2 →
      Loud_property sb_apart p1 p2 q →
      Sufficient p1 q.

Local Definition EvSufficient p q := eventually (λ p', Sufficient p' q) p.

Lemma sb_apart_from_sufficient_rtc_after {p1 q1 q2} :
  rtc (can_step silent) q1 q2 →
  EvSufficient p1 q1 →
  sb_apart p1 q2.
Proof.
  intros Hs_q1_q2 (p2 & Hs_p1_p2 & Hsuff).
  inv Hsuff; try eauto using sb_apart_silent_gen, sb_apart_loud_gen.
  eapply rtc_inv_r in Hs_p1_p2 as [<-|(pm & Hs_p1_pm & Hs_pm_p2)].
  { by eapply H. }
  eapply sb_apart_silent_gen; eauto with hints steps.
  eapply persistently_closed_implication; [|done].
  intros q3 Hs_q1_q3 H_p2_q3 q4 Hs_q3_q4.
  right. eauto with steps.
Qed.

Lemma sb_apart_from_sufficient {p1 q1} :
  EvSufficient p1 q1 → sb_apart p1 q1.
Proof.
  intros Hsuff.
  eapply sb_apart_from_sufficient_rtc_after; [eapply rtc_refl|done].
Qed.

End SemibranchingDef.

Global Hint Constructors sb_apart : hints.
Global Hint Extern 1 (EvSufficient _ _) => unfold EvSufficient : hints steps.