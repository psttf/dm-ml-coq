Require Import Vector.
Require Import Arith.

Inductive Bool: Prop :=
  True: Bool | False: Bool.

Fixpoint t_n (A: Type) (n: nat) (x: A): t A n := 
  match n with
    | O => nil A
    | S m => cons A x m (t_n A m x)
  end.

Inductive preserves_false (n: nat) (f: t Bool n -> Bool) := 
  preserves: (f(t_n Bool n False) = False) -> preserves_false n f.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

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

(*Fixpoint is_same_set  {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => True
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | True => is_same_set xt yt
          | False => False
        end
    | _, _ => False
    end.*)

Definition is_not_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (True, True) => False
    | (False, False) => False
    | (True, False) => True
    | (False, True) => True
  end.

Fixpoint is_revert_set_rec {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => True
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | False => is_revert_set_rec xt yt
          | True => False
        end
    | _, _ => False
    end.

Definition is_revert_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
   match x, y with
    |[], [] => False
    | xh :: xt, yh :: yt=> is_revert_set_rec (xh :: xt) (yh :: yt)
    | _, _ => False
   end.


Inductive revert_sets {n: nat} (x y: t Bool n):=
  revert: (is_revert_set x y = True) -> revert_sets x y.

(*
Inductive self_duality (n: nat) (f: t Bool n -> Bool): Prop:=
  self_dual: 
    (forall (x y: t (t Bool n) (2^n)) (*(xs ys : t Bool n)*),
    Forall2 (fun (xs ys: t Bool n) => (revert_sets xs ys -> ((is_not_same_bool (f xs) (f ys)) = True) )) x y) -> self_duality n f .
*)

(*
Definition self_duality_is_composed_closed: compose_closed self_duality.
Proof.
apply compose_is_c.
intros.
unfold compose.
induction H0.
simpl.
admit.
apply self_dual.
intros.
admit.
Qed.
*)

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

Fixpoint is_preced_sets {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
    match x, y with
    | [], [] => True
    | xh :: xt, yh :: yt =>
         match is_less_or_equal_bool xh yh with
            | True => is_preced_sets xt yt
            | False => False
         end
     | _, _ => False
    end.

Inductive preced_sets {n: nat} (x y: t Bool n):=
  preced: (is_preced_sets x y = True) -> preced_sets x y.

Inductive monotonous (n: nat) (f: t Bool n -> Bool): Prop :=
  monotony:
    (forall (x : t ( t Bool n) (2^n)) (* (xs ys : t Bool n)*),
    Forall2 (fun (xs ys: t Bool n) => (preced_sets xs ys -> (is_less_or_equal_bool (f xs) (f ys) = True ))) x x)-> monotonous n f .

(*
Definition monotonous_is_composed_closed: compose_closed monotonous.
Proof.
apply compose_is_c.
intros.
induction H.
apply monotony.
intros.
auto.
simpl.
admit.
Qed.
(* for linear*)
(*
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


Inductive false_coef_for_set {n: nat} (x: t Bool n) (f: t Bool n -> Bool) :=
  false_coef: (get_coef_for_set x f
 = False) -> false_coef_for_set x.

Inductive more_one_true_in_set {n: nat} (x: t Bool n):=
  mote_one_true: (is_more_one_true_in_set x 0 = True) -> more_one_true_in_set x.

Inductive linearity (n: nat) (f: t Bool n -> Bool) : Prop :=
  linear: forall (x : t (t Bool n) (2^n)) (xs: t Bool n),
    Forall more_one_true_in_set x -> false_coef_for_set xs -> linearity n f.
*)
*)

Definition not (x: Bool) := match x with
  | True => False
  | False => True
end.

Fixpoint not_t {n: nat} (xs: t Bool n) :=
  map (fun x => not x) xs.

(*
Inductive dual {n: nat} (f g: t Bool n -> Bool) :=
  is_dual: (forall (xs: t Bool n), f xs = not (g (not_t xs))) -> dual f g.

Inductive self_dual (n: nat) (f: t Bool n -> Bool) :=
  is_self_dual: (dual f f) -> self_dual n f.

(*
Theorem dual_composition: 
  forall {m: nat} {n: nat} 
    (f df: t Bool m -> Bool) (gs dgs: t (t Bool n -> Bool) m),
*)

Theorem self_dual_is_composed_closed: compose_closed self_dual.
Proof.
apply compose_is_c.
intros.
apply is_self_dual.
induction H.
apply is_dual.
unfold compose.
*)

Definition dual {n: nat} (f: t Bool n -> Bool) (x: t Bool n) :=
  not (f (not_t x)).

Fixpoint dual_t {m: nat} {n: nat} (gs: t (t Bool n -> Bool) m) := 
  map (fun g => dual g) gs.

Inductive self_dual (n: nat) (f: t Bool n -> Bool) :=
  is_self_dual: (f = dual f) -> self_dual n f.

Require Import Coq.Logic.FunctionalExtensionality.

Theorem dual_composition:
  forall {m: nat} {n: nat}
    (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
    dual(compose f gs) = compose (dual f)(dual_t gs).
Proof.
intros.
unfold compose.
unfold dual.
apply functional_extensionality.
intros.
apply f_equal.
apply f_equal.
induction not_t.
induction map.
apply case0.
exact eq_refl.
unfold not_t.
unfold dual_t.
induction map.

induction map.
simpl.
unfold dual.
induction not.
.
.
unfold map.


induction n.
.
induction gs.

unfold not_t.
induction map.

induction map.

unfold not.
induction eq.
apply f_equal.
apply refl_f.
intro.