Require Import Vector.

Check t.

Check bool.

Check true.

Check t bool 3.

Check cons.

Check cons bool true 1 (cons bool false 0 (nil bool)).

Definition BoolOp := forall (n: nat), t bool n -> bool.

Check BoolOp.

Check map ( fun (x:bool) => x ) (cons bool true 1 (cons bool false 0 (nil bool))).

Definition compose (m: nat) (n: nat) (f: t bool m -> bool) (gs: t (t bool n -> bool) m) (xs: t bool n) : bool :=
  f (map ( fun (g: t bool n -> bool) => g xs ) gs).

Check compose.

Check Prop.

Check True.

(* Definition EqBoolOp (n: nat) (f: t bool n -> bool) (g: t bool n -> bool) : Prop. *)

Definition BoolOpClass := forall (n: nat), (t bool n -> bool) -> Prop.

Check fun (a: Type) (f: a -> a) => f.

Check 1 = 2.

Definition PreserveFalse (f: t bool 2 -> bool) :=
  match (f (cons bool false 1 (cons bool false 0 (nil bool)))) with 
    | true => True
    | false => False
  end.

Check PreserveFalse.

Check orb.

(* ? Definition Clone ... *)

Definition ComposeClosed: (c: BoolOpClass) -> Prop.

(* forall f (c(f) = True), forall gs (all g in gs: c(g) = True) .... => .... c(compose f gs) = True *) 

