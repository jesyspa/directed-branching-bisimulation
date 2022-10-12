From bisimulations Require Import prelude.
From stdpp Require Export relations.

Inductive label : Set := silent | loud.

Class system (X : Set) := can_step : label → X → X → Prop.
Class refl_system (X : Set) `{system X} := refl_can_step : ∀ x, can_step silent x x.

Definition WithRefl `{system X} : system X.
Proof. intros l x1 x2. exact (can_step l x1 x2 ∨ (l = silent ∧ x1 = x2)). Defined.
Global Instance WithReflReflSystem `{System : system X} : @refl_system X WithRefl.
Proof. intros x. by right. Qed.

Lemma WithRefl_can_step `{System : system X} {l p q} : can_step l p q → @can_step X WithRefl l p q.
Proof. unfold can_step, WithRefl, can_step. tauto. Qed.
Global Hint Resolve WithRefl_can_step : hints steps.

Lemma WithRefl_can_step_loud `{System : system X} {p q} : can_step loud p q ↔ @can_step X WithRefl loud p q.
Proof. split; [left|intros [|[[=] _]]]; done. Qed.

Lemma WithRefl_rtc_can_step `{System : system X} {p q} : rtc (can_step silent) p q ↔ rtc (@can_step X WithRefl silent) p q.
Proof. split; revert q; eapply rtc_ind_r; eauto using rtc_refl; unfold can_step; intros q r Hpq Hqr Hpq'.
  - eapply rtc_r; [done|]. by left. 
  - destruct Hqr as [|[? ->]]; [by eapply rtc_r|done].
Qed.
