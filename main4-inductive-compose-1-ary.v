Definition BoolFun := Prop -> Prop.

Inductive Bool: Prop :=
  True: Bool | False: Bool.

Print Bool_ind.

Definition id (x: Bool) := x.
Definition ConstTrue  (_ : Bool) := True.
Definition ConstFalse (_ : Bool) := False.
Definition Not (x : Bool) : Bool := match x with
  | True => False
  | False => True
end.

Definition compose (f : Bool -> Bool) (g: Bool -> Bool) :=
  fun x: Bool => g (f x).

Lemma comp_rewrite_lem: forall (f g: Bool -> Bool) (x: Bool), (compose f g x) = g (f x).
intros.
unfold compose.
exact eq_refl.
Qed.

Inductive preserves_false (x: Bool -> Bool) := 
  preserves: (x(False) = False) -> preserves_false x.

Definition xxx: forall (f g : Bool -> Bool), compose f g False = g (f False).
intros.
apply comp_rewrite_lem.
Qed.

Inductive compose_closed (c: (Bool -> Bool) -> Prop) :=
  compose_is_c: 
    (forall (f g: Bool -> Bool), (c f) -> (c g) -> (c (compose f g))) ->
      compose_closed c.

Lemma ppp: forall (f: Bool -> Bool) (f_preserves: preserves_false f),
  f(False) = False.
Proof.
intros.
induction f_preserves.
exact e.
Qed.

Definition preserves_false_is_composed_closed: compose_closed preserves_false.
apply compose_is_c.
intros.
induction H.
induction H0.
apply preserves.
unfold compose.
rewrite e.
rewrite e0.
exact eq_refl.

Inductive preserves_true (x: Bool -> Bool) := 
  preserve_true: (x(True) = True) -> preserves_true x.

Definition preserves_true_is_composed_closed: compose_closed preserves_true.
apply compose_is_c.
intros.
induction H.
induction H0.
apply preserve_true.
unfold compose.
rewrite e.
rewrite e0.
exact eq_refl.







