(* Branching directed apartness *)

From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.

Section DirectedBranchingApart.
Context `{System : system X}.

Notation Downstream_property l R p1 p2 := ((Downstream_property l (LL_RR_coRR_relation p1 p2) R)).
Notation Silent_property R p1 p2 := (Downstream_property silent R p1 p2).
Notation Loud_property R p1 p2 := (Downstream_property loud R p1 p2).

Local Definition SilentRefl_relation (R : relation X) (p q : X) : Prop := sc R p q.
Lemma SilentRefl_relation_closed_implication (R1 R2 : relation X) p q :
  (∀ p q, R1 p q → R2 p q) → SilentRefl_relation R1 p q → SilentRefl_relation R2 p q.
Proof. intros H [|]; [left|right]; eauto. Qed.

Local Definition SilentRefl_property (R : relation X) (p : X) : X → Prop :=
  persistently (SilentRefl_relation R p).
Lemma SilentRefl_property_closed_down (R : relation X) p q1 q2 :
  rtc (can_step silent) q1 q2 → SilentRefl_property R p q1 → SilentRefl_property R p q2.
Proof. eapply persistently_closed_down. Qed.
Lemma SilentRefl_property_closed_implication (R1 R2 : relation X) p q :
  (∀ p q, R1 p q → R2 p q) → SilentRefl_property R1 p q → SilentRefl_property R2 p q.
Proof. intros H. eapply persistently_closed_implication_weak.
  intros q2. by eapply SilentRefl_relation_closed_implication.
Qed.

(* db_dapart a b := a can do something b can't do *)
Inductive db_dapart : X → X → Prop :=
  | SilentBkwd p1 p2 q :
    can_step silent p1 p2 →
    db_dapart p2 q →
    db_dapart p1 q
  | SilentRefl p q :
    SilentRefl_property db_dapart p q →
    db_dapart p q
  | Silent p1 p2 q :
    can_step silent p1 p2 →
    db_dapart q p2 →
    Silent_property db_dapart p1 p2 q →
    db_dapart p1 q
  | Loud p1 p2 q :
    can_step loud p1 p2 →
    Loud_property db_dapart p1 p2 q →
    db_dapart p1 q.
Hint Constructors db_dapart : hints.

Notation sb_a := (sc db_dapart).

Theorem db_dapart_strong_ind :
  ∀ P : X → X → Prop,
    (∀ (p1 p2 q : X),
      can_step silent p1 p2 →
      db_dapart p2 q →
      P p2 q →
      P p1 q) →
    (∀ (p q : X),
      SilentRefl_property (rel_join db_dapart P) p q →
      P p q) →
    (∀ (p1 p2 q : X),
      can_step silent p1 p2 →
      db_dapart q p2 →
      P q p2 →
      Silent_property (rel_join db_dapart P) p1 p2 q →
      P p1 q) →
    (∀ (p1 p2 q : X),
      can_step loud p1 p2 →
      Loud_property (rel_join db_dapart P) p1 p2 q →
      P p1 q) →
    ∀ p1 q1 : X, db_dapart p1 q1 → P p1 q1.
Proof.
  intros P Case1 Case2 Case3 Case4.
  fix IH 3.
  intros p1 q1 H.
  inv H as [p1' p2 q1' Hs_p1_p2 Ha_p2_q1|p1' q1' HQ|p1' p2 q1' Hs_p1_p2 Ha_q1_p2 HQ|p1' p2 q1' Hs_p1_p2 HQ];
    [eapply Case1|eapply Case2|eapply Case3|eapply Case4]; eauto with hints;
    intros q2 Hs_q1_q2; specialize (HQ q2 Hs_q1_q2);
    [destruct HQ; [left|right]; split; eauto|..];
    intros q3 Hs_q2_q3; specialize (HQ q3 Hs_q2_q3);
    (destruct HQ; [left|right]; unfold rel_join, sc in *); eauto;
    (destruct H; [left|right]); eauto.
Qed.

Theorem db_dapart_strong_ind' :
  ∀ P : relation X,
    (∀ (p1 p2 q : X),
      can_step silent p1 p2 →
      P p2 q →
      P p1 q) →
    (∀ (p q : X), SilentRefl_property P p q → P p q) →
    (∀ (p1 p2 q : X),
      can_step silent p1 p2 →
      P q p2 →
      Silent_property P p1 p2 q →
      P p1 q) →
    (∀ (p1 p2 q : X),
      can_step loud p1 p2 →
      Loud_property P p1 p2 q →
      P p1 q) →
    ∀ p1 q1 : X, db_dapart p1 q1 → P p1 q1.
Proof. intros P Case1 Case2 Case3 Case4.
  assert (∀ p q, rel_join db_dapart P p q → P p q) by (unfold rel_join; tauto).
  eapply db_dapart_strong_ind; eauto using SilentRefl_property_closed_implication.
  - intros. eapply Case3; eauto using Downstream_property_closed_implication, LL_RR_coRR_relation_MBRT with hints.
  - intros. eapply Case4; eauto using Downstream_property_closed_implication, LL_RR_coRR_relation_MBRT with hints.
Qed.

Lemma Downstream_property_closed_rel_join {R1 R2 : relation X} {l p1 p2 q1} :
  Downstream_property l (rel_join R1 R2) p1 p2 q1 →
  Downstream_property l R1 p1 p2 q1.
Proof. eapply Downstream_property_closed_implication.
  - eapply LL_RR_coRR_relation_MBRT. 
  - unfold rel_join. tauto. 
Qed.

Instance db_dapart_extend_backwards_one :
  Proper (can_step silent ==> eq ==> flip impl) db_dapart.
Proof.
  intros p1 p2 Hs_p1_p2 q1 q1' <- Ha_p2_q1.
  eauto with hints.
Qed.

Instance db_dapart_extend_backwards :
  Proper (rtc (can_step silent) ==> eq ==> flip impl) db_dapart.
Proof.
  intros p1 p2 Hs_p1_p2 q1 q2 <-.
  revert Hs_p1_p2. revert p1.
  eapply rtc_ind_l; [done|].
  simpl. unfold impl.
  eauto using db_dapart_extend_backwards_one with hints.
Qed.

Instance db_dapart_extend_forward_one {p1} :
  Proper (can_step silent ==> impl) (db_dapart p1).
Proof.
  intros q1 q2 Hs_q1_q2 H.
  induction H as
    [p1 p2 q1 Hs_p1_p2 Ha_p2_q IHa_q|p1 q1 HQ|p1 p2 q1 Hs_p1_p2 Ha_q_p2 IHa_q1_q2 HQ|p1 p2 q1 Hs_p1_p2 HQ]
    using db_dapart_strong_ind.
  - eauto with hints.
  - eapply SilentRefl. eapply SilentRefl_property_closed_down.
    { by eapply rtc_once. }
    revert HQ. eapply SilentRefl_property_closed_implication.
    clear p1 q1 Hs_q1_q2. by intros p1 q1 [].
  - destruct (HQ _ (rtc_refl _ q1) q2 Hs_q1_q2)
      as [[Ha_p1_q1 IHa_p1_q2]|[[Ha_p2_q2 IHA]|[Ha_q2_p2 IHA]]]; simpl in *.
    + by apply IHa_p1_q2.
    + by eapply db_dapart_extend_backwards_one.
    + eapply Downstream_property_closed_rel_join in HQ.
      eapply Silent; try done.
      eapply Downstream_property_closed_down; eauto using rtc_once.
  - eapply Downstream_property_closed_rel_join in HQ.
    eapply Loud; try done.
    eapply Downstream_property_closed_down; eauto using rtc_once.
Qed.

Instance db_dapart_extend_forward {p1} :
  Proper (rtc (can_step silent) ==> impl) (db_dapart p1).
Proof.
  intros q1. 
  eapply rtc_ind_r; [done|].
  intros q2 q3 _ Hs_q2_q3 IH H.
  specialize (IH H).
  by eapply db_dapart_extend_forward_one.
Qed.

End DirectedBranchingApart.