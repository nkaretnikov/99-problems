(** * Problem 1

    Find the last element of a list.
    (Note that the Lisp transcription of this problem is incorrect.)

    Example in Haskell:
<<
Prelude> myLast [1,2,3,4]
4

Prelude> myLast ['x','y','z']
'z'
>>
*)

Require Import List.
Import ListNotations.
Require Import Datatypes.
Require Import Ascii.

(** Since partial functions are not allowed, we need to provide the
    default value or use something like the [option] type. *)

Fixpoint myLast {X:Type} (xs:list X) : option X :=
  match xs with
    | nil    => None
    | x::nil => Some x
    | _::xt  => myLast xt
  end.

Example myLast1:
  myLast [1;2;3;4] = Some 4.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example myLast2:
  myLast ["x";"y";"z"] = Some "z".
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem myLast_nil : forall X:Type,
  @myLast X [] = None.
Proof. reflexivity. Qed.

Theorem myLast_app : forall (X:Type) (xs : list X) (x : X),
  myLast (app xs [x]) = Some x.
Proof.
  intros.
  induction xs as [|y yt].
    reflexivity.
    simpl. destruct (yt ++ [x]).
      (* Contradiction. *)
      inversion IHyt.
      apply IHyt.
Qed.

(** * Problem 2

    Find the last but one element of a list.
    (Note that the Lisp transcription of this problem is incorrect.)

    Example in Haskell:
<<
Prelude> myButLast [1,2,3,4]
3
Prelude> myButLast ['a'..'z']
'y'
>>
*)

Fixpoint myButLast {X:Type} (xs:list X) : option X :=
  match xs with
    | [] | [_] => None
    | [x;_]    => Some x
    | _::xt    => myButLast xt
  end.

Example myButLast1:
  myButLast [1;2;3;4] = Some 3.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example myButLast2:
  myButLast ["a";"b";"c";"d"] = Some "c".
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem myButLast_nil : forall X:Type,
  @myButLast X [] = None.
Proof. reflexivity. Qed.

Theorem myButLast_one : forall (X:Type) (x:X),
  myButLast [x] = None.
Proof. reflexivity. Qed.

Theorem myButLast_app : forall (X:Type) (xs:list X) (x:X) (y:X),
  myButLast (app xs [x;y]) = Some x.
Proof.
  intros.
  induction xs as [|z zt].
    reflexivity.
    simpl. destruct (zt ++ [x;y]).
      inversion IHzt.
      rewrite IHzt.
      destruct l as [|n nt].
        inversion IHzt.
        reflexivity.
Qed.

(** * Problem 3

    Find the K'th element of a list. The first element in the list is
    number 1.

    Example:
<<
* (element-at '(a b c d e) 3)
c
>>

    Example in Haskell:
<<
Prelude> elementAt [1,2,3] 2
2
Prelude> elementAt "haskell" 5
'e'
>>
*)

Fixpoint element_at {X:Type} (xs:list X) (n:nat) : option X :=
  match xs with
    | []    => None
    | x::xt => match n with
                 | 0    => None
                 | 1    => Some x
                 | S n' => element_at xt n'
               end
  end.

Example element_at1:
  element_at [1;2;3] 2 = Some 2.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example element_at2:
  element_at ["h";"a";"s";"k";"e";"l";"l"] 5 = Some "e".
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem element_at_nil : forall (X:Type) (n:nat),
  @element_at X [] n = None.
Proof. reflexivity. Qed.

Theorem element_at_zero : forall (X:Type) (xs:list X),
  element_at xs 0 = None.
Proof.
  intros.
  destruct xs as [|x xt].
    reflexivity.
    reflexivity.
Qed.

Theorem element_at_app : forall (X:Type) (xs:list X) (x:X),
  element_at (app xs [x]) (length xs + 1) = Some x.
Proof.
  intros.
  induction xs as [|y yt].
    reflexivity.
    simpl. destruct (length yt + 1).
      rewrite element_at_zero in IHyt. inversion IHyt.
      apply IHyt.
Qed.
