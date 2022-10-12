From bisimulations Require Import prelude.
From stdpp Require Export relations.
From Coq Require Export Relations.Relation_Definitions.
From Coq Require Export Classes.RelationClasses.

Definition rel_join {A} (R1 R2 : relation A) : relation A :=
  λ a1 a2, R1 a1 a2 ∧ R2 a1 a2.

Class MonoBinRelTrans X (T : relation X → relation X) :=
  binreltrans_is_mono : ∀ (R1 R2 : relation X), (∀ x y, R1 x y → R2 x y) → ∀ x y, T R1 x y → T R2 x y.

Definition LLR_RR_relation {X} p1 p2 (R : relation X) q1 q2 : Prop :=
  (R p1 q1 ∧ R p1 q2) ∨ R p2 q2.
Global Instance LLR_RR_relation_MBRT {X} p1 p2 : MonoBinRelTrans X (LLR_RR_relation p1 p2).
Proof. intros R1 R2 H x y. unfold LLR_RR_relation. intuition. Qed.
Global Hint Extern 0 (LLR_RR_relation _ _ _ _ _) => unfold LLR_RR_relation : hints.

Definition LL_RR_relation {X} p1 p2 (R : relation X) q1 q2 : Prop :=
  R p1 q1 ∨ R p2 q2.
Global Instance LL_RR_relation_MBRT {X} p1 p2 : MonoBinRelTrans X (LL_RR_relation p1 p2).
Proof. intros R1 R2 H x y. unfold LL_RR_relation. intuition. Qed.
Global Hint Extern 0 (LL_RR_relation _ _ _ _ _) => unfold LL_RR_relation : hints.

Definition LL_RR_coRR_relation {X} p1 p2 (R : relation X) q1 q2 : Prop := R p1 q1 ∨ sc R p2 q2.
Global Instance LL_RR_coRR_relation_MBRT {X} p1 p2 : MonoBinRelTrans X (LL_RR_coRR_relation p1 p2).
Proof. intros R1 R2 H x y. unfold LL_RR_coRR_relation, sc. intuition. Qed.
Global Hint Extern 0 (LL_RR_coRR_relation _ _ _ _ _) => unfold LL_RR_coRR_relation : hints.
