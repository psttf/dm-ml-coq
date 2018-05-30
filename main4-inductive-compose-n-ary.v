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

(* Check t_n Bool 3 False.
Eval compute in t_n Bool 3 False.*)

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

(*for self-duality*)

Definition is_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => True
    | (False, False) => True
    | (True, False) => False
    | (False, True) => False
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

Definition is_not_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => False
    | (False, False) => False
    | (True, False) => True
    | (False, True) => True
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

Inductive revert_sets {n: nat} (x y: t Bool n):=
  revert: (is_revert_set x y = True) -> revert_sets x y.

Inductive self_duality (n: nat) (f: t Bool n -> Bool): Prop:=
  self_dual: 
    forall (x y: t ( t Bool n) (2^n)) (xs ys : t Bool n),
    Forall2 revert_sets x y -> (is_not_same_bool (f xs) (f ys)) = True-> self_duality n f .

Definition self_duality_is_composed_closed: compose_closed self_duality.
Proof.


(* for monotonous*)
Definition is_less_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => False
    | (False, False) => False
    | (True, False) => False
    | (False, True) => True
  end.

Definition is_less_or_equal_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => True
    | (False, False) => True
    | (True, False) => False
    | (False, True) => True
  end.

Fixpoint is_first_less_and_comparable_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p) (diff: nat): Bool :=
    match x, y with
    | [], [] => 
        match diff with 
          | S O => True
          | _ => False
        end
    | xh :: xt, yh :: yt =>
         match is_less_bool xh yh with
            | True => is_first_less_and_comparable_set xt yt (S diff)
            | False => is_first_less_and_comparable_set xt yt diff
         end
     | _, _ => False
    end.

Inductive first_less_and_comparable_sets {n: nat} (x y: t Bool n):=
  less_comparable: (is_first_less_and_comparable_set x y 0 = True) -> first_less_and_comparable_sets x y.

Inductive monotonous (n: nat) (f: t Bool n -> Bool): Prop :=
  monotony: forall (x y: t ( t Bool n) (2^n)) (xs ys : t Bool n),
    Forall2 first_less_and_comparable_sets x y -> (is_less_or_equal_bool (f xs) (f ys) = True )-> monotonous n f .

Definition monotonous_is_composed_closed: compose_closed monotonous.
admit.

(* for linear*)
Definition xor (x y: Bool): Bool :=
  match x, y with
    | False, False => False
    | False, True => True
    | True, False => True
    | True, True => False
  end.

Fixpoint is_more_one_true_in_set {n: nat} (x: t Bool n) (diff: nat) : Bool :=
  match x with   
    | [] => 
        match diff with 
          | O => False
          | S O => False
          | _ => True
        end
    | xh :: xt =>
        match is_same_bool xh True with
          | True => is_more_one_true_in_set xt (S diff)
          | False => is_more_one_true_in_set xt diff
        end
   end.



Definition pred_set {n: nat} (x: t Bool n): t Bool n := x.

Fixpoint get_coef_for_set {n: nat} (x: t Bool n) (f: t Bool n -> Bool): Bool :=
(* Some third-party code to use this method *)
  match is_same_set x (t_n Bool n False) with
    | True => f (t_n Bool n False)
    | False => xor (f x) (get_coef_for_set ( pred_set x) f)
  end.

Inductive false_coef_for_set {n: nat} (x: t Bool n) (f: t Bool n -> Bool) :=
  false_coef: (get_coef_for_set x f
 = False) -> false_coef_for_set x.

Inductive more_one_true_in_set {n: nat} (x: t Bool n):=
  mote_one_true: (is_more_one_true_in_set x 0 = True) -> more_one_true_in_set x.

Inductive linearity (n: nat) (f: t Bool n -> Bool) : Prop :=
  linear: forall (x : t (t Bool n) (2^n)) (xs: t Bool n),
    Forall more_one_true_in_set x -> false_coef_for_set xs -> linearity n f.




