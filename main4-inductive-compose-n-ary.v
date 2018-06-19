Require Import Vector.
Require Import Arith.

Inductive Bool: Prop :=
  BTrue: Bool | BFalse: Bool.

Fixpoint t_n (A: Type) (n: nat) (x: A): t A n := 
  match n with
    | O => nil A
    | S m => cons A x m (t_n A m x)
  end.

Inductive preserves_false (n: nat) (f: t Bool n -> Bool) := 
  preserves: (f(t_n Bool n BFalse) = BFalse) -> preserves_false n f.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

Lemma preserves_false_vector: forall {n: nat} {m: nat} (gs: t (t Bool n -> Bool) m),
  Forall (fun (g: t Bool n -> Bool) => preserves_false n g) gs -> 
    (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n BFalse) ) gs) = (t_n Bool m BFalse).
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
assumption.
assumption.
Qed.


Inductive preserves_true (n: nat) (f: t Bool n -> Bool) := 
  preserve_true: (f(t_n Bool n BTrue) = BTrue) -> preserves_true n f.

Lemma preserves_true_vector: forall {n: nat} {m: nat} (gs: t (t Bool n -> Bool) m),
  Forall (fun (g: t Bool n -> Bool) => preserves_true n g) gs -> 
    (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n BTrue) ) gs) = (t_n Bool m BTrue).
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
assumption.
assumption.
Qed.

Import VectorNotations.

(*for self-duality*)

Definition is_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (BTrue, BTrue) => BTrue
    | (BFalse, BFalse) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
  end.

(*Fixpoint is_same_set  {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => BTrue
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | BTrue => is_same_set xt yt
          | BFalse => BFalse
        end
    | _, _ => BFalse
    end.*)

Definition is_not_same_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (BTrue, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (BTrue, BFalse) => BTrue
    | (BFalse, BTrue) => BTrue
  end.

Fixpoint is_revert_set_rec {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
  match x, y with
    |[], [] => BTrue
    | xh :: xt, yh :: yt=>
        match is_same_bool xh yh with
          | BFalse => is_revert_set_rec xt yt
          | BTrue => BFalse
        end
    | _, _ => BFalse
    end.

Definition is_revert_set {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
   match x, y with
    |[], [] => BFalse
    | xh :: xt, yh :: yt=> is_revert_set_rec (xh :: xt) (yh :: yt)
    | _, _ => BFalse
   end.


Inductive revert_sets {n: nat} (x y: t Bool n):=
  revert: (is_revert_set x y = BTrue) -> revert_sets x y.

(*
Inductive self_duality (n: nat) (f: t Bool n -> Bool): Prop:=
  self_dual: 
    (forall (x y: t (t Bool n) (2^n)) (*(xs ys : t Bool n)*),
    Forall2 (fun (xs ys: t Bool n) => (revert_sets xs ys -> ((is_not_same_bool (f xs) (f ys)) = BTrue) )) x y) -> self_duality n f .
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
    | (BTrue, BTrue) => BFalse
    | (BFalse, BFalse) => BFalse
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BTrue
  end.

Definition is_less_or_equal_bool (x y: Bool) : Bool:=
  match (x, y) with
    | (BTrue, BTrue) => BTrue
    | (BFalse, BFalse) => BTrue
    | (BTrue, BFalse) => BFalse
    | (BFalse, BTrue) => BTrue
  end.

Fixpoint is_preced_sets {n: nat} {p: nat} (x: t Bool n) (y: t Bool p): Bool :=
    match x, y with
    | [], [] => BTrue
    | xh :: xt, yh :: yt =>
         match is_less_or_equal_bool xh yh with
            | BTrue => is_preced_sets xt yt
            | BFalse => BFalse
         end
     | _, _ => BFalse
    end.

Inductive preced_sets {n: nat} (x y: t Bool n):=
  preced: (is_preced_sets x y = BTrue) -> preced_sets x y.

Inductive monotonous (n: nat) (f: t Bool n -> Bool): Prop :=
  monotony:
    (forall (x : t ( t Bool n) (2^n)) (* (xs ys : t Bool n)*),
    Forall2 (fun (xs ys: t Bool n) => (preced_sets xs ys -> (is_less_or_equal_bool (f xs) (f ys) = BTrue ))) x x)-> monotonous n f .

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
    | BFalse, BFalse => BFalse
    | BFalse, BTrue => BTrue
    | BTrue, BFalse => BTrue
    | BTrue, BTrue => BFalse
  end.

Fixpoint is_more_one_true_in_set {n: nat} (x: t Bool n) (diff: nat) : Bool :=
  match x with   
    | [] => 
        match diff with 
          | O => BFalse
          | S O => BFalse
          | _ => BTrue
        end
    | xh :: xt =>
        match is_same_bool xh BTrue with
          | BTrue => is_more_one_true_in_set xt (S diff)
          | BFalse => is_more_one_true_in_set xt diff
        end
   end.


Inductive false_coef_for_set {n: nat} (x: t Bool n) (f: t Bool n -> Bool) :=
  false_coef: (get_coef_for_set x f
 = BFalse) -> false_coef_for_set x.

Inductive more_one_true_in_set {n: nat} (x: t Bool n):=
  mote_one_true: (is_more_one_true_in_set x 0 = BTrue) -> more_one_true_in_set x.

Inductive linearity (n: nat) (f: t Bool n -> Bool) : Prop :=
  linear: forall (x : t (t Bool n) (2^n)) (xs: t Bool n),
    Forall more_one_true_in_set x -> false_coef_for_set xs -> linearity n f.
*)
*)

Definition not (x: Bool) := match x with
  | BTrue => BFalse
  | BFalse => BTrue
end.

Definition not_t {n: nat} (xs: t Bool n) :=
  map (fun x => not x) xs.

Definition dual {n: nat} (f: t Bool n -> Bool) (xs: t Bool n) :=
  not (f (not_t xs)).

Definition dual_t {m: nat} {n: nat} (gs: t (t Bool n -> Bool) m) := 
  map (fun g => dual g) gs.

Inductive self_dual (n: nat) (f: t Bool n -> Bool) :=
  is_self_dual: (f = dual f) -> self_dual n f.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma compose_assoc {m : nat} {n : nat} {h: Bool -> Bool}:
  forall (f : t Bool m -> Bool) (gs : t (t Bool n -> Bool) m),
    (fun xs : t Bool n => h (compose f gs xs)) = compose (fun xs : t Bool m => h (f xs)) gs.
Proof.
intros.
unfold compose.
apply functional_extensionality.
intros.
apply f_equal.
apply f_equal.
apply f_equal.
reflexivity.
Qed.

Lemma involution: forall (x: Bool), not (not x) = x.
Proof.
intros.
unfold not.
destruct x.
reflexivity.
reflexivity.
Qed.

Check involution.

Lemma dual_vector {m: nat} {n: nat}:
  forall (gs : t (t Bool n -> Bool) m) (xs : t Bool n),
    map (fun g : t Bool n -> Bool => g (not_t xs)) gs =
      not_t (map (fun g : t Bool n -> Bool => g xs) (dual_t gs)).
Proof.
intros.
unfold dual_t.
unfold dual.
unfold not_t.
induction gs.
simpl.
reflexivity.
simpl.
rewrite involution.
apply f_equal.
assumption.
Qed.

Theorem dual_composition:
  forall {m: nat} {n: nat}
    (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
    dual (compose f gs) = compose (dual f) (dual_t gs).
Proof.
intros.
unfold dual.
unfold compose.
apply functional_extensionality.
intros.
apply f_equal.
apply f_equal.
apply dual_vector.
Qed.

Theorem self_dual_is_compose_closed: compose_closed self_dual.
Proof.
apply compose_is_c.
intros.
apply is_self_dual.
rewrite dual_composition.
apply f_equal2.
induction H.
assumption.
clear H.
clear f.
induction H0.
simpl.
reflexivity.
simpl.
induction H.
destruct e.
apply f_equal.
apply IHForall.
Qed.

(* curried `and` *)
Definition and (x y: Bool) : Bool :=
  match (x, y) with
    | (BFalse, BFalse) => BFalse
    | (BFalse, BTrue) => BFalse
    | (BTrue, BFalse) => BFalse
    | (BTrue, BTrue) => BTrue
  end.

(* uncurried `and`, i. e. boolean function and *)
Definition and_bf (xs: t Bool 2) := and (hd xs) (hd (tl xs)).

(* curried Zhegalkin plus, i. e. boolean function plus *)
Definition plus (x y: Bool) : Bool:=
  match (x, y) with
    | (BFalse, BFalse) => BFalse
    | (BFalse, BTrue) => BTrue
    | (BTrue, BFalse) => BTrue
    | (BTrue, BTrue) => BTrue
  end.

(* uncurried Zhegalkin plus *)
Definition plus_bf (xs: t Bool 2) := plus (hd xs) (hd (tl xs)).

(* computes Zhegalkin polynomm for the given coefficients:
   c is the free coefficient and cs are variable coefficients *)
Definition compute_polynom {n: nat} (c: Bool) (cs: t Bool n) (xs: t Bool n): Bool :=
  fold_left
    (fun (result value: Bool) => plus result value) 
      c
       (map2 (fun (c x: Bool) => and c x) cs xs).

Inductive linear (n: nat) (f: t Bool n -> Bool): Prop :=
  of_coefficients: 
    forall (c: Bool) (cs: t Bool n),
      (forall (xs: t Bool n), compute_polynom c cs xs = f xs) 
        -> linear n f.

Check of_coefficients.

Check caseS' [BTrue; BTrue].

(*
  Vector_0_is_nil' and Vector_0_is_nil: easier proofs that 0-length vectors are equal to nil
  see http://coq-club.inria.narkive.com/wrDwvaNY/how-to-prove-that-all-vectors-of-0-length-are-equal-to-vector-nil
*)

Lemma Vector_0_is_nil' : forall T n (v : Vector.t T n),
match n return Vector.t T n -> Prop with
| O => fun v => v = Vector.nil T
| _ => fun _ => (True: Prop)
end v.
Proof.
destruct v; auto.
Qed.

Theorem Vector_0_is_nil : forall T (v : Vector.t T 0), v = Vector.nil T.
Proof.
intros; apply (Vector_0_is_nil' _ _ v).
Qed.

(* example proof that Zhegalkin plus has a corresponding polynom *)
Example plus_bf_has_polynom: forall (xs: t Bool 2), compute_polynom BFalse [BTrue; BTrue] xs = plus_bf xs.

Proof.

intros.

(* first introduce all the xs since it has fixed length *)
apply (caseS' xs).
intros.
clear xs.
apply (caseS' t).
clear t.
intros.

(* the rest of xs is [] *)
rewrite (Vector_0_is_nil Bool t).

(* unfold all the definitions *)
unfold compute_polynom.
unfold plus_bf.
unfold plus.

(* now enumerate all the xs by destructing h and h0 *)
destruct h.
destruct h0.
simpl.
reflexivity.
simpl.
reflexivity.
destruct h0.
simpl.
reflexivity.
simpl.
reflexivity.

Qed.

Example plus_bf_is_linear: linear 2 plus_bf.
Proof.
(* propose the polynom that we already know *)
apply (of_coefficients 2 plus_bf BFalse [BTrue; BTrue]).
intros.
apply plus_bf_has_polynom.
Qed.

Theorem linear_is_compose_closed: compose_closed linear.
Proof.
(* Work in Progress *)
Admitted.
