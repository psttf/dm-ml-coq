Require Import Vector.
Require Import Arith.
Require Import Bool.Bvector.
(* Try to represent bool function as list of result, 
for example conj will represent like {0, 0, 0, 1} *)

Definition BoolFunN (n: nat) := t bool (2^n).

Inductive closClass (n: nat): Type := 
| PreservesFalse (x: BoolFunN n)
| PreservesTrue (x: BoolFunN n)
| SelfDual (x: BoolFunN n)
| Monotonous (x: BoolFunN n)
| Linear (x: BoolFunN n) .

Definition сompose {BoolFun} (f : BoolFun -> BoolFun) (g: BoolFun -> BoolFun) :=
  fun x: BoolFun => g (f x).

Definition BoolFun2 (x: t bool 4) := BoolFunN 2.

Definition conj := BoolFun2 ([false ; false ; false ; true ]).

Definition IsPreservesFalseFunc (n: nat) (f : (BoolFunN n)): Prop :=
  match f with
    | [] => False (* Strange case*)
    | true :: t => False
    | false :: t => True
end.

Definition IsPreservesTrueFunc (n: nat) (f : (BoolFunN n)): Prop :=
  match f with
    | [] => False (* Strange case*)
    | true :: t => True
    | false :: t => False
end.

Import Lists.List.

Fixpoint IsListSelfDual(v p : list bool): bool :=  
  match v, p with 
  | Lists.List.nil, Lists.List.nil => true
  | h::t, f::g => if eqb h f then false else  IsListSelfDual t g
  | _, _ => false
end.

Definition IsSelfDualFunc (n: nat) (f : (BoolFunN n)) : Prop :=
 let m:= (let x := to_list f in IsListSelfDual x (rev x)) in
  match m with 
  | true => True
  | _ => False
end.

Definition isMonotoniusFunc (n: nat) (f : (BoolFunN n)) : Prop :=
  


