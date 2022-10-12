(* Semi-branching directed apartness *)

From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.

Section DirectedBranchingApart.
Context `{ReflSystem : @refl_system X System}.

Local Definition Downstream_relation (R : relation X) p1 p2 q1 q2 : Prop := R p1 q1 ∨ sc R p2 q2.
Lemma Downstream_relation_weaken_minimal (R1 R2 : relation X) p1 p2 q1 q2 :
  (R1 p1 q1 → R2 p1 q1) → (R1 p2 q2 → R2 p2 q2) → (R1 q2 p2 → R2 q2 p2) →
  Downstream_relation R1 p1 p2 q1 q2 → Downstream_relation R2 p1 p2 q1 q2.
Proof. intros H1 H2 H3 [|[]]; [left|right;left|right;right]; eauto. Qed.
Lemma Downstream_relation_closed_implication (R1 R2 : relation X) :
  (∀ p q, R1 p q → R2 p q) → ∀ p1 p2 q1 q2, Downstream_relation R1 p1 p2 q1 q2 → Downstream_relation R2 p1 p2 q1 q2.
Proof. intros ?????. eauto using Downstream_relation_weaken_minimal. Qed.

Local Definition Downstream_property l (R : relation X) p1 p2 : X → Prop :=
  persistently_for_all_steps l (Downstream_relation R p1 p2).

Lemma Downstream_property_closed_implication l (R1 R2 : relation X) :
  (∀ p q, R1 p q → R2 p q) → ∀ p1 p2 q1, Downstream_property l R1 p1 p2 q1 → Downstream_property l R2 p1 p2 q1.
Proof. intros ????. by eapply persistently_for_all_steps_closed_implication_weak, Downstream_relation_closed_implication. Qed.

Instance Downstream_property_closed_down {R : relation X} {l p1 p2} :
  Proper (rtc (can_step silent) ==> impl) (Downstream_property l R p1 p2).
Proof. eapply persistently_closed_down. Qed.

Notation Silent_property := (Downstream_property silent).
Notation Loud_property := (Downstream_property loud).

(* db_dapart a b := a can do something b can't do *)
Inductive db_dapart : X → X → Prop :=
  | Fwd l p1 p2 q : can_step l p1 p2 → Downstream_property l db_dapart p1 p2 q → db_dapart p1 q.
Hint Constructors db_dapart : hints.

Theorem db_dapart_strong_ind :
  ∀ P : X → X → Prop,
    (∀ l (p1 p2 q : X),
      can_step l p1 p2 →
      Downstream_property l (rel_join db_dapart P) p1 p2 q →
      P p1 q) →
    ∀ p1 q1 : X, db_dapart p1 q1 → P p1 q1.
Proof.
  intros P CaseFwd.
  fix IH 3.
  intros p1 q1 H.
  inv H as [l p1' p2 q1' Hs_p1_p2 HQ].
  eapply CaseFwd; try done.
  intros q2 Hq12 q3 Hq23.
  destruct (HQ q2 Hq12 q3 Hq23) as [Ha_p1_q2|[Ha_p2_q3|Ha_q3_p2]];
    [left|right;left|right;right]; split; eauto.
Qed.

Theorem db_dapart_strong_ind' :
  ∀ P : X → X → Prop,
    (∀ l (p1 p2 q : X), can_step l p1 p2 → Downstream_property l P p1 p2 q → P p1 q) →
    ∀ p1 q1 : X, db_dapart p1 q1 → P p1 q1.
Proof.
  intros P CaseFwd.
  eapply db_dapart_strong_ind; eauto.
  intros; eapply CaseFwd; try done.
  eapply Downstream_property_closed_implication; [|exact H0].
  unfold rel_join. tauto.
Qed.

Lemma Downstream_property_closed_rel_join {R1 R2 : relation X} {l p1 p2 q1} :
  Downstream_property l (rel_join R1 R2) p1 p2 q1 →
  Downstream_property l R1 p1 p2 q1.
Proof. eapply Downstream_property_closed_implication. by intros p q []. Qed.

Instance db_dapart_extend_forward_one {p1} :
  Proper (can_step silent ==> impl) (db_dapart p1).
Proof.
  intros q1 q2 Hs_q1_q2 H.
  inv H.
  eapply Fwd; try done.
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

Instance db_dapart_extend_backwards_one :
  Proper (can_step silent ==> eq ==> flip impl) db_dapart.
Proof.
  intros p1 p2 Hs_p1_p2 q1 q1' <- Ha_p2_q1.
  eapply Fwd; try done.
  intros q2 Hq12 q3 Hq23.
  right. left.
  by eapply db_dapart_extend_forward; [eapply rtc_r|].
Qed.

Instance db_dapart_extend_backwards :
  Proper (rtc (can_step silent) ==> eq ==> flip impl) db_dapart.
Proof.
  intros p2 p3 Hs_p2_p3 q1 q2 <- Ha.
  revert p2 Hs_p2_p3.
  eapply rtc_ind_l; [done|].
  intros p1 p2 Hp12 Hp23.
  by eapply db_dapart_extend_backwards_one.
Qed.

End DirectedBranchingApart.
