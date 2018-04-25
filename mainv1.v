Require Import Vector.
Require Import Arith.
Require Import Bool.Bvector.
(* Try to represent bool function as list of result, 
for example conj will represent like {0, 0, 0, 1} *)

Definition BoolFunN (n: nat) : Type := t bool (2^n).

Definition BoolFun : Set := forall (n: nat), t bool (2^n).

Definition TwoBoolFun := BoolFunN 2.
(*Definition conj := BoolFun ([false ; false ; false ; true ]).*)



Inductive Close: closClass -> Prop :=
| ClPreserveFalse : forall x, Close ( PreservesFalse x)
| ClPreserveTrue : forall x, Close ( PreservesTrue x)
| ClSelfDual : forall x, Close ( SelfDual x)
| ClMonotonous : forall x, Close ( Monotonous x)
| ClLinear : forall x, Close ( Linear x).


Definition сompose {BoolFun} (f : BoolFun -> BoolFun) (g: BoolFun -> BoolFun) :=
  fun x: BoolFun => g (f x).


(*Systems of bool func*)
(*Definition SystemBoolFun := forall (m: nat), t BoolFun m.*)



Definition IsPreservesFalseFunc (f : BoolFun): Prop :=
  match f with
    | 
    | false => False
end.

(*Inductive BoolFun : Type :=
| One (x : t bool 1)
| Two (x : t bool 2)
| Three (x : t bool 3)
| Four (x : t bool 4) .*)

(*Inductive BoolFun := 
| ConstTrue  (x : Prop)
| ConstFalse (x : Prop)
| Id (x : Prop)
| Not (x : Prop)impl
| And (x y: BoolFun)
| Or (x y: BoolFun).

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
end.*)