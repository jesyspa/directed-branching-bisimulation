From bisimulations Require Import prelude.
From bisimulations Require Import system.
From bisimulations Require Import relations.
From bisimulations Require Import paths.
From bisimulations Require Import reflexive.directed_branching.
From bisimulations Require Import reflexive.branching.

Section Equivalence.
Context `{ReflSystem : @refl_system X System}.

Notation db_apart := (sc db_dapart).

Theorem branching_implies_directed_branching :
  ∀ p q, b_apart p q → db_apart p q.
Proof.
  eapply b_apart_strong_ind'.
  { by intros p q [|]; [right|left]. }
  intros l p1 p2 q1 Hp12 HQ.
  destruct (LEM (db_apart p1 q1)) as [|Hcont]; [done|].
  left. eapply Fwd; try done.
  intros q2 Hq12 q3 Hq23.
  destruct (HQ q2 Hq12 q3 Hq23) as [[|]|[|]].
  - by left.
  - exfalso. eapply Hcont. right. by eapply db_dapart_extend_backwards. 
  - right. by left.
  - right. by right.
Qed.

Lemma directed_branching_implies_branching :
  ∀ p q, db_dapart p q → b_apart p q.
Proof.
  eapply db_dapart_strong_ind'.
  intros l p1 p2 q1 Hp12 HQ.
  eapply b_apart_step; try done.
  intros q2 Hq12 q3 Hq23.
  destruct (HQ q2 Hq12 q3 Hq23) as [|[|]]; [by left|by right|right].
  by eapply b_apart_sym.
Qed.

Theorem db_apart_iff_b_apart {p q} : db_apart p q ↔ b_apart p q.
Proof. split.
  - intros [|]; eauto using directed_branching_implies_branching with hints.
  - by eapply branching_implies_directed_branching.
Qed.

End Equivalence.

