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
Module Import LN := ListNotations.
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
