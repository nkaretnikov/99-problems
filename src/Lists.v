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
