From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.

Global Hint Resolve rtc_refl : steps.
Global Hint Resolve rtc_l : steps.
Global Hint Resolve rtc_r : steps.

Theorem nsteps_ind_strong_l :
  ∀ X R (P : nat → X → X → Prop),
    (∀ x, P 0 x x) →
    (∀ n x y z,
      (∀ a b (s : nsteps R n a b), P n a b) →
      R x y →
      nsteps R n y z →
      P (Datatypes.S n) x z) →
    ∀ n x y, nsteps R n x y → P n x y.
Proof.
  intros X R P Base Ind n.
  induction n as [|n IH]; intros x y Hsteps;
  inv Hsteps; [by eapply Base|by eapply Ind].
Qed.

Section PathVia.
Context {X} (R : relation X) (P : X → Prop).

Inductive path_via : relation X :=
  | path_via_refl p : P p → path_via p p
  | path_via_l p q r : P p → R p q → path_via q r → path_via p r.

Lemma path_source_satisfies p q : path_via p q → P p.
Proof. intros H. by inv H. Qed.
Lemma path_target_satisfies p q : path_via p q → P q.
Proof. by induction 1. Qed.

Lemma rtc_to_path_via {p q} (Hpos : ∀ p1 p2, R p1 p2 → P p2 → P p1) :
  rtc R p q → P q → path_via p q.
Proof.
  intros Hpq Hq. revert p Hpq. eapply rtc_ind_l; 
  eauto using path_via_refl, path_via_l, path_source_satisfies.
Qed.

Lemma path_via_to_rtc {p q} : path_via p q → rtc R p q.
Proof. induction 1; eauto using rtc_refl, rtc_l. Qed.

End PathVia.

Global Hint Constructors path_via : steps.

Section SuccessorFunc.
Context {X} (R : relation X).

Definition sucessor_func (f : X → list X) := ∀ p q, q ∈ f p ↔ R p q.
End SuccessorFunc.

Section FilteredPathVia.
Context {X : Set} (R : relation X) (f : X → list X).
Context (P : X → Prop) (dec : ∀ x, Decision (P x)).

Definition filtered_successors : X → list X := list_filter P dec ∘ f.
End FilteredPathVia.

Section Defs.
Context `{System : system X}.

Section Persistently.
Context (P : X → Prop).

Definition persistently q1 : Prop :=
  ∀ q2, rtc (can_step silent) q1 q2 → P q2.

Instance persistently_closed_down :
  Proper (rtc (can_step silent) ==> impl) persistently.
Proof.
  intros q1 q2 Hq12 HQ q3 Hq23.
  eapply HQ. eauto using rtc_transitive with steps.
Qed.
End Persistently.

Lemma persistently_closed_implication {R1 R2 : X → Prop} {q1} :
  (∀ q2, rtc (can_step silent) q1 q2 → R1 q2 → R2 q2) →
  persistently R1 q1 → persistently R2 q1.
Proof. unfold persistently. eauto. Qed.

Lemma persistently_closed_implication_weak {R1 R2 : X → Prop} :
  (∀ q2, R1 q2 → R2 q2) → ∀ q1, persistently R1 q1 → persistently R2 q1.
Proof. unfold persistently. eauto. Qed.

Section Eventually.
Context (P : X → Prop).

Definition eventually q1 : Prop :=
  ∃ q2, rtc (can_step silent) q1 q2 ∧ P q2.

Instance eventually_closed_up :
  Proper (rtc (can_step silent) ==> flip impl) eventually.
Proof.
  intros q1 q2 Hq12 (q3 & Hq23 & HQ).
  exists q3. split; [eauto using rtc_transitive with steps|done].
Qed.
End Eventually.

Definition for_all_steps l (P : relation X) (q1 : X) : Prop :=
  ∀ q2, can_step l q1 q2 → P q1 q2.

Lemma for_all_steps_closed_implication {l} {R1 R2 : relation X} {q1} :
  (∀ q2, can_step l q1 q2 → R1 q1 q2 → R2 q1 q2) →
  for_all_steps l R1 q1 → for_all_steps l R2 q1.
Proof. unfold for_all_steps. eauto. Qed.

Definition persistently_for_all_steps l (P : relation X) : X → Prop := persistently (for_all_steps l P).

Lemma persistently_for_all_steps_closed_implication {l} {R1 R2 : relation X} {q1} :
  (∀ q2 q3, rtc (can_step silent) q1 q2 → can_step l q2 q3 → R1 q2 q3 → R2 q2 q3) →
  persistently_for_all_steps l R1 q1 → persistently_for_all_steps l R2 q1.
Proof. unfold persistently_for_all_steps, persistently, for_all_steps. eauto. Qed.

Lemma persistently_for_all_steps_closed_implication_weak {l} {R1 R2 : relation X} :
  (∀ q2 q3, R1 q2 q3 → R2 q2 q3) → ∀ q1, persistently_for_all_steps l R1 q1 → persistently_for_all_steps l R2 q1.
Proof. unfold persistently_for_all_steps, persistently, for_all_steps. eauto. Qed.

Lemma persistently_for_all_steps_manual {l q1} {R : relation X} :
  (∀ q2 q3, rtc (can_step silent) q1 q2 → can_step l q2 q3 → R q2 q3) → persistently_for_all_steps l R q1.
Proof. intros H. intros q2 Hq12 q3 Hq23. eauto. Qed.

End Defs.

Global Hint Resolve persistently_for_all_steps_manual : steps.

Section DownstreamProperty.
Context `{System : system X}.
Context (l : label) (T : relation X → relation X).
Definition Downstream_property (R : relation X) : X → Prop :=
  persistently_for_all_steps l (T R).

Lemma Downstream_property_closed_down (R : relation X) q1 q2 :
  rtc (can_step silent) q1 q2 → Downstream_property R q1 → Downstream_property R q2.
Proof. eapply persistently_closed_down. Qed.
Lemma Downstream_property_closed_implication `{MBRT : MonoBinRelTrans X T} (R1 R2 : relation X) :
  (∀ x1 x2, R1 x1 x2 → R2 x1 x2) → ∀ q1, Downstream_property R1 q1 → Downstream_property R2 q1.
Proof.
  intros H.
  by eapply persistently_for_all_steps_closed_implication_weak, binreltrans_is_mono.
Qed.
Lemma Downstream_property_manual {q1} {R : relation X} :
  (∀ q2 q3, rtc (can_step silent) q1 q2 → can_step l q2 q3 → T R q2 q3) → Downstream_property R q1.
Proof. intros H. intros q2 Hq12 q3 Hq23. eauto. Qed.

End DownstreamProperty.

Global Hint Resolve Downstream_property_manual : hints.
Global Hint Resolve Downstream_property_closed_down : hints.
