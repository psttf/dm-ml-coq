
Inductive BoolFun := 
| ConstTrue  (x : Prop)
| ConstFalse (x : Prop)
| Id (x : Prop)
| Not (x : Prop)
| And (x y: BoolFun)
| Or (x y: BoolFun).

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

Definition ConstTrueFun (x: Prop) := ConstTrue x.
Definition ConstFalseFun (x: Prop) := ConstFalse x.
Definition IdFun (x : Prop) := Id x.
Definition NotFun (x: Prop) := Not x.
Definition AndFun (x y: BoolFun) := And x y.
Definition OrFun (x y: BoolFun) := Or x y.

Fixpoint interpr (f : BoolFun) : Prop :=
  match f with 
  
  | ConstTrue x => True
  | ConstFalse x => False
  | Id x => x
  | Not x => not x
  | And x y => and (interpr (x : BoolFun)) (interpr (y : BoolFun))
  | Or x y => or (interpr (x : BoolFun)) (interpr (y : BoolFun))
end.