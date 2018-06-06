Require Import Vector.
Require Import Arith.
Import VectorNotations.

Inductive Bool: Prop :=
  True: Bool | False: Bool.

Definition compose {m: nat} {n: nat} (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m) (xs: t Bool n) : Bool :=
  f (map ( fun (g: t Bool n -> Bool) => g xs ) gs).

Inductive compose_closed (c: forall k, (t Bool k -> Bool) -> Prop) :=
  compose_is_c:
    (forall
      {m: nat} {n: nat}
      (f: t Bool m -> Bool) (gs: t (t Bool n -> Bool) m),
      (c m f) -> Forall (fun (g: t Bool n -> Bool) => c n g) gs -> (c n (compose f gs))) ->
        compose_closed c.

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
    (forall (xs ys : t Bool n),
        (preced_sets xs ys -> (is_less_or_equal_bool (f xs) (f ys) = True ))) -> monotonous n f .
