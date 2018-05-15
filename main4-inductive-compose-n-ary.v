Require Import Vector.

Definition BoolFun := Prop -> Prop.

Inductive Bool: Prop :=
  True: Bool | False: Bool.

Fixpoint t_n (A: Type) (n: nat) (x: A): t A n := 
  match n with
    | O => nil A
    | S m => cons A x m (t_n A m x)
  end.

Inductive preserves_false (n: nat) (f: t Bool n -> Bool) := 
  preserves: (f(t_n Bool n False) = False) -> preserves_false n f.

Lemma preserves_false_from_false: forall (n: nat) (f: t Bool n -> Bool) (f_preserves: preserves_false n f),
  f(t_n Bool n False) = False.
Proof.
intros.
induction f_preserves.
exact e.
Qed.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

Lemma comp_rewrite:
  forall 
    {m: nat} {n: nat} 
    (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) 
    (xs: t Bool n),
    (compose f gs xs) = f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).
Proof.
intros.
unfold compose.
exact eq_refl.
Qed.

Lemma comp_false_rewrite:
  forall 
    {m: nat} {n: nat} 
    (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
    (compose f gs (t_n Bool n False)) = f (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n False) ) gs).
Proof.
intros.
apply comp_rewrite.
Qed.


Lemma preserves_false_vector: forall {n: nat} {m: nat} (gs: t (t Bool n -> Bool) m),
  Forall (fun (g: t Bool n -> Bool) => preserves_false n g) gs -> 
    (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n False) ) gs) = (t_n Bool m False).
Proof.
intros.
induction H.
auto.
simpl.
induction H.
rewrite e.
induction map.
auto.
rewrite IHForall.
auto.
Qed.

Inductive compose_closed (c: forall k, (t Bool k -> Bool) -> Prop) :=
  compose_is_c:
    (forall
      {m: nat} {n: nat}
      (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
      (c m f) -> Forall (fun (g: t Bool n -> Bool) => c n g) gs -> (c n (compose f gs))) ->
        compose_closed c.

Definition preserves_false_is_composed_closed: compose_closed preserves_false.
Proof.
apply compose_is_c.
intros.
induction H.
apply preserves.
unfold compose.
rewrite preserves_false_vector.
exact e.
exact H0.
Qed.

Inductive preserves_true (n: nat) (f: t Bool n -> Bool) := 
  preserve_true: (f(t_n Bool n True) = True) -> preserves_true n f.

Lemma preserves_true_vector: forall {n: nat} {m: nat} (gs: t (t Bool n -> Bool) m),
  Forall (fun (g: t Bool n -> Bool) => preserves_true n g) gs -> 
    (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n True) ) gs) = (t_n Bool m True).
Proof.
intros.
induction H.
auto.
simpl.
induction H.
rewrite e.
induction map.
auto.
rewrite IHForall.
auto.
Qed.


Definition preserves_true_is_composed_closed: compose_closed preserves_true.
Proof.
apply compose_is_c.
intros.
induction H.
apply preserve_true.
unfold compose.
rewrite preserves_true_vector.
exact e.
exact H0.
Qed.
