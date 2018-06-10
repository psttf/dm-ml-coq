Require Import Vector.
Require Import Arith.
Import VectorNotations.

Inductive Bool: Set :=
  BTrue: Bool | BFalse: Bool.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

Inductive compose_closed (c: forall k, (t Bool k -> Bool) -> Prop) :=
  compose_is_c:
    (forall
      {m: nat} {n: nat}
      (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
      (c m f) -> Forall (fun (g: t Bool n -> Bool) => c n g) gs -> (c n (compose f gs))) ->
        compose_closed c.

Definition leq (x y: Bool): Prop:=
  match (x, y) with
    | (BTrue, BTrue) => True
    | (BFalse, BFalse) => True
    | (BTrue, BFalse) => False
    | (BFalse, BTrue) => True
  end.

Definition leq_t {n: nat} (xs ys: t Bool n) :=
  Forall2 (fun (x y: Bool) => leq x y) xs ys.

Inductive monotonous (n: nat) (f: t Bool n -> Bool): Prop :=
  monotony:
    (forall (xs ys : t Bool n),
        (((leq_t xs ys) = True) -> (leq (f xs) (f ys) = True ))) -> monotonous n f .
Require Import Coq.Logic.FunctionalExtensionality.

Lemma monoton {m: nat} {n: nat}:
  forall (f : t Bool n -> Bool) (xs ys: t Bool n), 
     monotonous n f ->
      leq_t xs ys = True ->  
        (leq (f xs) (f ys) = True ).
Proof.
intros.
induction H.
auto.
Qed.

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

Lemma monoton_vector_0 {n: nat}: 
forall (gs : t (t Bool n -> Bool) 0) (xs ys: t Bool n), 
    Forall (fun (g: t Bool n -> Bool) => monotonous n g) gs ->
      leq_t xs ys = True ->  
        (leq_t (map (fun g : t Bool n -> Bool => g xs) gs) 
          (map (fun g : t Bool n -> Bool => g ys) gs)) = leq_t [] [] .
Proof.
intros.
rewrite (Vector_0_is_nil (t Bool n -> Bool) gs).
simpl.
apply eq_refl.
Qed.

Lemma monoton_vector {m: nat} {n: nat}:
  forall (gs : t (t Bool n -> Bool) m) (xs ys: t Bool n), 
    Forall (fun (g: t Bool n -> Bool) => monotonous n g) gs ->
      leq_t xs ys = True ->  
        (leq_t (map (fun g : t Bool n -> Bool => g xs) gs) 
          (map (fun g : t Bool n -> Bool => g ys) gs)) = True.
Proof.
intros.
(*induction H.
induction xs.
simpl.
elim H0.
rewrite (Vector_0_is_nil Bool ys).
apply eq_refl.*)


induction gs.
simpl.
induction H0.


Qed.

Theorem monotonous_compose_closed: compose_closed monotonous.
Proof.
apply compose_is_c.
intros.
apply monotony.
unfold compose.
intros.
apply monoton_vector.

induction H0.
simpl.
induction H.
unfold leq.
induction f.
exact eq_refl.
exact eq_refl.
simpl.


(*test*)

