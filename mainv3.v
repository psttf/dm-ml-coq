Require Import Lists.List.
Require Import Vector.



Inductive Bool: Prop :=
  True| False.

Inductive ArgSet (n: nat) : Prop:=
      false_set: ArgSet n
    | true_set: ArgSet n
    | other_set: ArgSet n.


Inductive preserves_false {n} (x: ArgSet n -> Bool) := 
 preserve_false: (x (false_set n)= False) -> preserves_false x.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

Inductive compose_closed {m: nat} {n: nat} (c: (t Bool m -> Bool) -> Prop) :=
  compose_is_c: 
    (forall (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) , (c f) -> (c xs) -> (c (map ( fun (g: t Bool n -> Bool) => g xs)) gs) -> (c (compose f gs xs))) ->
      compose_closed c.

Inductive compose_closed (c: (Bool -> Bool) -> Prop) :=
  compose_is_c: 
    (forall (f g: Bool -> Bool), (c f) -> (c g) -> (c (compose f g))) ->
      compose_closed c.



Definition compose (f : Bool -> Bool) (g: Bool -> Bool) :=
  fun x: Bool => g (f x).



(*Fixpoint create_false_list_rec (n: nat) (res: list Bool) :=
  match n with
  | 0 => res
  | S n1 => create_false_list_rec n1 (False :: res)
  end.


Definition create_false_vector (n: nat) : t Bool n := of_list (create_false_list_rec n List.nil).*)

  
 
(*Inductive FalseVector {n} :=
  false_vector: create_false_vector n.*)

(*Lemma comp_rewrite_lem: forall (f g: t Bool n -> Bool) (x: Bool), (compose f g x) = g (f x).
intros.
unfold compose.
exact eq_refl.
Qed.*)

