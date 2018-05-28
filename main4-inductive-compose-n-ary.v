Require Import Vector.
Require Import Arith.

Definition BoolFun := Prop -> Prop.

Inductive Bool: Prop :=
  True: Bool | False: Bool.

Fixpoint t_n (A: Type) (n: nat) (x: A): t A n := 
  match n with
    | O => nil A
    | S m => cons A x m (t_n A m x)
  end.

Check t_n Bool 3 False.
Eval compute in t_n Bool 3 False.

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

Import VectorNotations.

Definition is_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => True
    | (False, False) => True
    | (True, False) => False
    | (False, True) => False
  end.

Fixpoint is_comparable_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p) (diff: nat): Bool :=
    match x with
    | [] => 
        match diff with 
          | S O => True
          | _ => False
        end
    | xh :: xt =>
        match y with
          | yh :: yt => 
              match is_same_bool xh yh with
                | True => is_comparable_set xt yt (S diff)
                | False => is_comparable_set xt yt diff
              end
          | _ => False
        end
    end.

Fixpoint is_same_set  {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => True
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | True => is_same_set xt yt
          | False => False
        end
    | _, _ => False
    end.

Definition is_revert_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => True
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | False => is_same_set xt yt
          | True => False
        end
    | _, _ => False
    end.

Definition set_bool_vector (n: nat): t ( t Bool n) (2^n) .
admit.

Inductive preserves_false1 (n: nat) (f: t Bool n -> Bool) := 
  preserves1: (f(t_n Bool n False) = False) -> preserves_false1 n f.

Inductive revert_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p)
  revert: (is_revert_set x y = True) -> revert_set x y.

Inductive self_duality (n: nat) (f: t Bool n -> Bool):=
  self_dual: Forall2 (is_revert_set (set_bool_vector n) (set_bool_vector n)).

Inductive compose_closed (c: forall k, (t Bool k -> Bool) -> Prop) :=
  compose_is_c:
    (forall
      {m: nat} {n: nat}
      (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
      (c m f) -> Forall (fun (g: t Bool n -> Bool) => c n g) gs -> (c n (compose f gs))) ->
        compose_closed c.



Fixpoint get_next_rev_vect {n: nat} (curr: t Bool n) : t Bool n :=
    match curr with 
      | [] => []
      | True :: xs => False :: (get_next_rev_vect xs)
      | False :: xs => True :: xs
  end.

(*Fixpoint get_next_rev_vect {n: nat} (curr: t Bool n) : t Bool n :=
    match curr with 
      | [] => []
      | x :: xs => 
        match is_same_bool x True with
          | True => append (t_n Bool 1 False) (get_next_rev_vect xs)
          | False => append (t_n Bool 1 True) xs
        end
  end.*)

cons A x m (t_n A m x)

  
Fixpoint comparable_pairs {p: nat} (n: nat)(curr: t Bool n) (delt: nat)  (l :t (prod (t Bool n) (t Bool n)) p) :=
  match is_same_set curr (t_n Bool n True) with
    | True => l
    | False => if (delt >= n) then   else
        match is_same_bool False (nth curr delt 
  end.




    




