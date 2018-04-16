Inductive BoolFun := 
| ConstTrue  (x : Prop)
| ConstFalse (x : Prop)
| Id (x : Prop)
| Not (x : Prop).

Inductive closClass :=
| PreservesFalse (x: BoolFun)
| PreservesTrue (x: BoolFun)
| SelfDual (x: BoolFun)
| Monotonous (x: BoolFun)
| Linear (x: BoolFun) .

Inductive Close: closClass -> Prop :=
| ClPreserveFalse : forall x, Close ( PreservesFalse x)
| ClPreserveTrue : forall x, Close ( PreservesTrue x)
| ClSelfDual : forall x, Close ( SelfDual x)
| ClMonotonous : forall x, Close ( Monotonous x)
| ClLinear : forall x, Close ( Linear x).


Definition сompose {BoolFun} (f : BoolFun -> BoolFun) (g: BoolFun -> BoolFun) :=
  fun x: BoolFun => g (f x).

Definition ConstTrueFun := (ConstTrue True).
Definition ConstFalseFun := (ConstFalse False).
Definition IdFun (x : Prop) := Id x.
Definition NotFun (x: Prop) := Not (not x).