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
    | h::t => if List.last (to_list t) false then True else False
end.

Import Lists.List.

Fixpoint IsListSelfDual(v p : list bool): Prop :=  
  match v, p with 
  | Lists.List.nil, Lists.List.nil => True
  | h::t, f::g => if eqb h f then False else  IsListSelfDual t g
  | _, _ => False
end.

Definition IsSelfDualFunc (n: nat) (f : (BoolFunN n)) : Prop := let x := to_list f in IsListSelfDual x (rev x).


Definition getComparableSet (n: nat) : list (nat * nat) :=
  match n with
  | 1 => (cons (0 , 1) nil)
  | 2 => (cons (0 , 1) (cons (1 , 2)  (cons (2 , 3) nil) ))
  | 3 => (cons (0 , 1) (cons (0 , 2)  (cons (0 , 4) ( cons (1 ,3) ( cons (1,5) 
( cons (2, 3) ( cons (2, 6) ( cons (3, 7)( cons (4 ,5)( cons (4, 6) 
(cons (5,7) ( cons (6, 7) nil))))))) )))))
  | _ => nil
  end.

Check fst.

Definition leBool (a b : bool) : bool :=
  match a, b with
  | true, false => false
  | _, _ => true
  end.


Fixpoint isMonotoniusFuncHelp {n: nat} (f : (BoolFunN n)) ( comparation: list (nat * nat)) : Prop :=
  let fl := to_list f in match comparation with
  | List.nil => True
  | h::t => if  leBool (nth (fst h) fl false) (nth (snd h) fl false)  then isMonotoniusFuncHelp f t  else False
  end.

Definition isMonotoniusFunc (n: nat) (f : (BoolFunN n)) : Prop := isMonotoniusFuncHelp f (getComparableSet n).
  
(* Определит линейность, ввести понятие системы функций, 
написать проверки на на не принадлежность к классам для системы функций,
тогда теорема о полноте: T0 -> T1 -> S -> M -> L -> Full.
А проверка конкретной системы будет ??????*)

