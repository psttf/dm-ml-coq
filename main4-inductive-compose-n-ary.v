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
    (forall (x y: t (t Bool n) (2^n)) (xs ys : t Bool n),
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
    | (BTrue, BTrue) => BFalse
  end.

(* uncurried Zhegalkin plus *)
Definition plus_bf (xs: t Bool 2) := plus (hd xs) (hd (tl xs)).

(* computes Zhegalkin polynomm for the given coefficients:
   c is the free coefficient and cs are variable coefficients *)
Definition compute_polynom {n: nat} (c: Bool) (cs: t Bool n) (xs: t Bool n): Bool :=
  fold_right
    (plus) 
    (map2 (and) cs xs)
    c.

Inductive linear (n: nat) (f: t Bool n -> Bool): Prop :=
  of_coefficients: 
    forall (c: Bool) (cs: t Bool n),
      (forall (xs: t Bool n), compute_polynom c cs xs = f xs) 
        -> linear n f.

Check linear.
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

Check plus_bf.
(*Definition plus_bf (xs: t Bool 2) := plus (hd xs) (hd (tl xs)).*)
(*plus_bf t> t Bool 2 -> Bool*)


Lemma plus_commutativity: forall (x y: Bool),
plus x y = plus y x.
Proof.
intros.
destruct x, y; 
unfold plus; reflexivity.
Qed.

Lemma plus_associativity: forall (x y z: Bool), 
plus (plus x y) z = plus x (plus y z).
Proof.
intros.
destruct x, y, z; 
unfold plus; reflexivity.
Qed.

Lemma op_associativity_false: 
forall (x z: Bool), plus (plus x BFalse) z = plus x (plus BFalse z).
Proof.
  intros.
  apply plus_associativity.
Qed.


Lemma plus_false_c: forall (x: Bool), plus x BFalse = x.
Proof.
  intros.
  destruct x;
  unfold plus;
  reflexivity. 
Qed.

Lemma and_true_c: 
  forall (x: Bool), and BTrue x = x.
  Proof.
    intros.
    destruct x;
    unfold and;
    reflexivity.
  Qed.

Lemma and_false_c:
  forall (x: Bool), and BFalse x = BFalse.
  Proof.
    intros.
    destruct x;
    unfold and;
    reflexivity.
  Qed.


(*Load lambda_rewrite.*)

Lemma and_true_c_lambda:
  forall (x: Bool),
  (fun x : Bool => and x BTrue) = (fun x: Bool => x).
  Proof.
    (*intros.
    setoid_rewrite -> and_true_c.
    reflexivity.
  Qed.*)
  Admitted.

Lemma and_false_c_lambda:
  forall (x: Bool),
  (fun x: Bool => and x BFalse) = (fun x: Bool => BFalse).
  Proof.
    (*intros.
    setoid_rewrite -> and_false_c.
    reflexivity.
  Qed.*)
  Admitted.

Theorem fold_associativity: forall {n: nat} (c: Bool) (xs: t Bool n),
  fold_right plus xs c = plus c (fold_right plus xs BFalse).
Proof.
intros.
induction xs.
simpl.

rewrite -> plus_false_c.
reflexivity. 
simpl.
rewrite -> IHxs.
rewrite plus_commutativity.
rewrite (plus_commutativity c (fold_right plus xs BFalse)).
rewrite plus_associativity.
rewrite (plus_commutativity c (plus h (fold_right plus xs BFalse))). 
rewrite (plus_commutativity h (fold_right plus xs BFalse)). 
rewrite plus_associativity.
rewrite (plus_commutativity c h). 
reflexivity. 
Qed.

Theorem poly_plus_c_is_poly:
forall (n: nat),
forall (cs cx: t Bool n),
forall (c c0: Bool),
plus (compute_polynom c cs cx) c0 = compute_polynom (plus c c0) cs cx.
Proof.
intros.
destruct c. 
destruct c0.
unfold plus at 2.
unfold compute_polynom.
rewrite fold_associativity.
rewrite (plus_commutativity BTrue (fold_right plus (map2 and cs cx) BFalse)).
rewrite plus_associativity.
unfold plus at 3.
rewrite plus_false_c.
reflexivity. 
rewrite -> plus_false_c.
unfold plus.
reflexivity.
destruct c0.
unfold compute_polynom.
rewrite -> fold_associativity. 
rewrite (plus_commutativity BFalse (fold_right plus (map2 and cs cx) BFalse)).
rewrite plus_associativity.  
unfold plus at 3. 
unfold plus at 4. 
rewrite (fold_associativity BTrue (map2 and cs cx)). 
auto.
rewrite -> plus_false_c. 
unfold plus.
reflexivity.
Qed.

Theorem and_commutativity:
forall (x y: Bool), and x y = and y x.
Proof.
  intros.
  destruct x, y;
  unfold and; reflexivity.
Qed.

Lemma and_associativity: forall (x y z: Bool), 
and (and x y) z = and x (and y z).
Proof.
intros.
destruct x, y, z; 
unfold and; reflexivity.
Qed.

(*Lemma and_unmap:
  forall {n: nat} (cs: t Bool n),
  map (fun x : Bool => x) cs = cs.
  Proof.
  intros.
  Admitted.*)

Lemma and_true_unmap:
  forall {n: nat} (cs: t Bool n),
  map (fun x : Bool => and x BTrue) cs = cs.
  Proof.
    intros.

  Admitted.

(*distributivity*)
(*mult c (plus a b) = plus (nult c a) (mult c b)*)
(*mult x zero = zero*)
(*poly plus poly is poly*)
(*composition of poly is poly*)
(*modules - make at least one*)

Lemma and_distributivity:
  forall (x y z: Bool),
  and x (plus y z) = plus (and x y) (and x z).
  Proof.
    intros.
    destruct x, y, z;
    unfold plus; 
    unfold and; 
    reflexivity.
  Qed. 



Lemma polynom_with_falses_reults_false:
  forall {n: nat} (cs cx: t Bool n),
  compute_polynom BFalse (map (fun x : Bool => and x BFalse) cs) cx = BFalse.
  Proof.
    intros.
    unfold compute_polynom.
    unfold plus.
  Admitted.

Theorem poly_and_c_is_poly: 
forall (n: nat),
forall (cs cx: t Bool n),
forall (c c0: Bool),
and (compute_polynom c cs cx) c0 = 
compute_polynom (and c c0) (map (fun x => (and x c0)) cs) cx.
Proof.
  intros.
  destruct c, c0. 
  unfold and at 2.
  unfold compute_polynom. 
  rewrite -> and_commutativity. 
  rewrite -> and_true_c.
  rewrite -> and_true_unmap.
  reflexivity.
  rewrite -> and_commutativity at 1.
  rewrite -> and_false_c.
  unfold and at 1.
  rewrite -> polynom_with_falses_reults_false.
  reflexivity.
  rewrite -> and_commutativity. 
  rewrite -> and_true_c. 
  unfold and at 1.
  rewrite -> and_true_unmap.
  reflexivity.
  rewrite -> and_commutativity at 1. 
  rewrite -> and_false_c. 
  unfold and at 1.
  rewrite -> polynom_with_falses_reults_false. 
  reflexivity. 
Qed.

Theorem poly_plus_poly_is_poly: 
  forall {n: nat},
  forall (csf csg xs: t Bool n),
  forall (cf cg: Bool),
  plus (compute_polynom cf csf xs) (compute_polynom cg csg xs) = 
    compute_polynom (plus cf cg) (map2 plus csf csg) xs.
Proof.
  intros.
  unfold compute_polynom.
  induction n.
  rewrite (Vector_0_is_nil Bool csf).
  rewrite (Vector_0_is_nil Bool csg).
  rewrite (Vector_0_is_nil Bool xs).
  simpl.
  reflexivity.
  apply (caseS' csf).
  apply (caseS' csg).
  apply (caseS' xs).
  intros.
  simpl.
  rewrite -> plus_associativity. 
  rewrite -> plus_commutativity with (fold_right plus (map2 and t1 t) cf) (plus (and h0 h) (fold_right plus (map2 and t0 t) cg)).
  rewrite -> plus_associativity.
  rewrite -> plus_commutativity with (fold_right plus (map2 and t0 t) cg) (fold_right plus (map2 and t1 t) cf).
  rewrite IHn.
  rewrite <- plus_associativity.
  rewrite and_commutativity at 1.
  rewrite and_commutativity with h0 h.
  rewrite <- and_distributivity.
  rewrite and_commutativity.
  reflexivity.
Qed.

Theorem poly_plus_c_is_linear: 
forall (n: nat),
forall (cs: t Bool n),
forall (c c0: Bool),
linear n (compute_polynom (plus c c0) cs).
Proof.
intros.
apply (of_coefficients n (compute_polynom (plus c c0) cs) (plus c c0) cs).
auto.
Qed.

Theorem poly_and_c_is_linear: 
forall (n: nat),
forall (cs: t Bool n),
forall (c c0: Bool),
linear n (compute_polynom (and c c0) ( map (fun x => (and x c0)) cs)).
Proof.
intros.
apply (of_coefficients 
                n 
                (compute_polynom (and c c0) (map (fun x => (and x c0)) cs)) 
                (and c c0) 
                (map (fun x => (and x c0)) cs)
      ).
auto.
Qed.




Theorem poly_plus_poly_is_linear:
forall (n m: nat), 
forall (csf: t Bool n), 
forall (csg: t Bool m), 
forall (cf cg: Bool),
linear (n+m) (compute_polynom (plus cf cg) (csf ++ csg)).
Proof.
intros.
apply (of_coefficients 
                (n+m) 
                (compute_polynom (plus cf cg) (csf ++ csg))
                (plus cf cg)
                (csf ++ csg)
      ).
auto.
Qed.
(*
Lemma composition_of_polynoms_is_polynom: forall {n: nat} {m: nat} (gs: t Bool m -> Bool) (vect: t (t Bool n -> Bool) m),
  Forall (fun (g: t Bool n) => fun (b: Bool) => compute_polynom b g) gs -> 
    (map ( fun (g: t Bool n -> Bool) => g (t_n Bool n BFalse) ) gs) = (t_n Bool m BFalse).
Proof.*)

Theorem composition_of_polynoms_is_polynom:
forall (n m: nat),
forall (csf: t Bool n), 
forall (cf: Bool),
forall (csg : t Bool m), 
forall (cg : Bool),
forall (csx: t Bool m), (*exists / linear*)
forall (cx: Bool),
compose (compute_polynom cf csf) (t_n (t Bool m -> Bool) n (compute_polynom cg csg)) = compute_polynom cx csx.
Proof.
intros.
unfold compose.
Admitted.

Check compute_polynom.

Definition csg_to_cg_application {m: nat} (csg: t Bool m) (cg: Bool) : t Bool m -> Bool := compute_polynom cg csg.

Check composition_of_polynoms_is_polynom.

(*Theorem polynom_and_vector_computation_composition_is_linear: 
forall (n m: nat), 
forall (csg_to_cg: t Bool m -> Bool),
forall (csg_to_vector: t (t Bool n -> Bool) m),
forall (csx: t Bool m), 
forall (cx: Bool),
linear n (compose (csg_to_cg) (csg_to_vector)).
Proof.
intros.
rewrite (composition_of_polynoms_is_polynom n m csf csg cf cg csx cx).
apply (of_coefficients m (compute_polynom cx csx) cx csx).
auto.
Qed.
Admitted.


Check polynom_and_vector_computation_composition_is_linear.*)

Theorem linear_is_compose_closed: compose_closed linear.
Proof.
apply (compose_is_c).
intros.
induction H.
apply functional_extensionality in H.
induction H0.

apply eq_sym in H.
rewrite H.
unfold compose.
simpl.
apply (of_coefficients (n) (fun _ : t Bool (n) => compute_polynom c cs []) c (t_n Bool (n) BFalse)).
intros.
apply eq_sym.
rewrite (Vector_0_is_nil Bool cs).
unfold compute_polynom.
simpl.
induction xs.
simpl.
reflexivity.
unfold and.
simpl.
unfold plus.
simpl.
unfold plus.
simpl.
induction n.
apply (of_coefficients 0 (fun _ : t Bool 0 => compute_polynom c cs []) c []).
apply case0.
rewrite (Vector_0_is_nil Bool cs).
reflexivity.
apply (of_coefficients (S n) (fun _ : t Bool (S n) => compute_polynom c cs []) c (t_n Bool (S n) BFalse)).
simpl.
unfold compute_polynom.
simpl.



induction H0.
simpl.
apply (of_coefficients n (fun _ : t Bool n => compute_polynom c cs []) c (t_n Bool n BTrue)).
induction n.
apply case0.
simpl.
rewrite (Vector_0_is_nil Bool cs).
reflexivity.
simpl.
apply caseS'.
simpl.

unfold compose.

apply (polynom_and_vector_computation_composition_is_linear n m f gs).

Qed.
