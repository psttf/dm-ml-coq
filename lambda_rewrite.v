Module Foo.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Generalizable All Variables.

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.

Goal (fun n => n + 0) = (fun n => n).
  setoid_rewrite <- plus_n_O.
  reflexivity.
Qed.

End Foo.