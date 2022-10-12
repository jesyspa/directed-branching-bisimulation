From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import nonreflexive.directed_branching.
From bisimulations Require Import nonreflexive.semibranching.

Section Equivalence.
Context `{System : system X}.

Notation db_apart := (sc db_dapart).

Theorem semibranching_implies_directed_semibranching :
  ∀ p q, sb_apart p q → db_apart p q.
Proof.
  eapply sb_apart_strong_ind.
  { intros p q Ha_pq [Hda_pq|Hda_qp]; [right|left]; done. }
  all: intros p1 p2 q1;
    destruct (LEM (db_apart p1 q1)) as [|Hcont]; [done|].
  - intros Hs_p1_p2 Ha_p2_q1 [Hda_p2_q1|Hda_q1_p2] HQ; left;
      [by eapply db_dapart_extend_backwards_one|].
    eapply Silent; try done.
    eapply (Downstream_property_closed_implication _ _ _ db_apart) in HQ; [|unfold rel_join; tauto].
    eapply persistently_closed_implication; [|exact HQ].
    clear HQ. intros q2 Hp_q1_q2.
    eapply for_all_steps_closed_implication.
    intros q3 Hs_q2_q3.
    intros [[Hl _]|Hr]; [left|right].
    * destruct Hl; [done|].
      exfalso. eapply Hcont. right.
      by eapply db_dapart_extend_backwards.
    * destruct Hr; [left|right]; done.
  - intros Hs_p1_p2 HQ; left.
    eapply Loud; try done.
    eapply (Downstream_property_closed_implication _ _ _ db_apart) in HQ; [|unfold rel_join; tauto].
    eapply persistently_closed_implication; [|exact HQ].
    clear HQ. intros q2 Hp_q1_q2.
    eapply for_all_steps_closed_implication.
    intros q3 Hs_q2_q3.
    intros [Hl|Hr]; [left|right].
    * destruct Hl; [done|].
      exfalso. eapply Hcont. right.
      by eapply db_dapart_extend_backwards.
    * destruct Hr; [left|right]; done.
Qed.

Lemma db_dapart_implies_semibranching_lemma :
  ∀ p1 q1, db_dapart p1 q1 → semibranching.EvSufficient p1 q1.
Proof.
  eapply db_dapart_strong_ind.
  - intros p1 p2 q1 Hs_p1_p2 Ha_p2_q1 (p3 & Hs_p2_p3 & H).
    exists p3. eauto with steps.
  - intros p1 q1 HQ.
    exists p1. split; [eauto with steps|].
    eapply SilentReflSufficient, persistently_closed_implication; [|done].
    intros q2 Hs_q1_q2 [[]|[]].
    + by eapply sb_apart_from_sufficient.
    + by eapply sb_apart_sym, sb_apart_from_sufficient. 
  - intros p1 p2 q1 Hs_p1_p2 Ha_q1_p2 IH_q1_p2 HQ. 
    exists p1. split; [eauto with steps|].
    eapply (SilentSufficient _ _ _ Hs_p1_p2).
    { by eapply sb_apart_sym, sb_apart_from_sufficient. }
    eapply persistently_closed_implication; [|exact HQ].
    intros q2 Hs_q1_q2 IH q3 Hs_q2_q3.
    destruct (IH q3 Hs_q2_q3) as [[_ IHa_p1_q2]|[[_ IHa_p2_q3]|[_ IHa_q3_p2]]].
    + left. split.
      * by eapply sb_apart_from_sufficient.
      * eapply sb_apart_from_sufficient_rtc_after; [by eapply rtc_once|done].
    + right. by eapply sb_apart_from_sufficient. 
    + right. by eapply sb_apart_sym, sb_apart_from_sufficient. 
  - intros p1 p2 q1 Hs_p1_p2 HQ. 
    exists p1. split; [eauto with steps|].
    eapply (LoudSufficient _ _ _ Hs_p1_p2).
    eapply persistently_closed_implication; [|exact HQ].
    intros q2 Hs_q1_q2 IH q3 Hs_q2_q3.
    destruct (IH q3 Hs_q2_q3) as [[_ IHa_p1_q2]|[[_ IHa_p2_q3]|[_ IHa_q3_p2]]].
    + left. by eapply sb_apart_from_sufficient. 
    + right. by eapply sb_apart_from_sufficient. 
    + right. by eapply sb_apart_sym, sb_apart_from_sufficient. 
Qed.

Lemma db_dapart_implies_semibranching {p1 q1} :
  db_dapart p1 q1 → sb_apart p1 q1.
Proof.
  intros H. by eapply sb_apart_from_sufficient, db_dapart_implies_semibranching_lemma.
Qed.

Theorem db_apart_iff_sb_apart {p q} : db_apart p q ↔ sb_apart p q.
Proof. split.
  - intros [|]; eauto using db_dapart_implies_semibranching with hints.
  - by eapply semibranching_implies_directed_semibranching.
Qed.

End Equivalence.

