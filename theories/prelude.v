From Coq Require Export Logic.Decidable.
From stdpp Require Export base.
From stdpp Require Export tactics.

Tactic Notation "inv" ident(H) "as" simple_intropattern(ipat) :=
  inversion H as ipat; clear H; simplify_eq.

Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

Axiom LEM : ∀ (A : Prop), A ∨ ¬ A.

Create HintDb hints.
Create HintDb steps.