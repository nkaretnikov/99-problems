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

Fixpoint my_last {X:Type} (xs:list X) : option X :=
  match xs with
    | nil    => None
    | x::nil => Some x
    | _::xt  => my_last xt
  end.

Example my_last1:
  my_last [1;2;3;4] = Some 4.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example my_last2:
  my_last ["x";"y";"z"] = Some "z".
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem my_last_nil : forall X:Type,
  @my_last X [] = None.
Proof. reflexivity. Qed.

Theorem my_last_app : forall (X:Type) (xs : list X) (x : X),
  my_last (app xs [x]) = Some x.
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

Fixpoint my_but_last {X:Type} (xs:list X) : option X :=
  match xs with
    | [] | [_] => None
    | [x;_]    => Some x
    | _::xt    => my_but_last xt
  end.

Example my_but_last1:
  my_but_last [1;2;3;4] = Some 3.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example my_but_last2:
  my_but_last ["a";"b";"c";"d"] = Some "c".
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem my_but_last_nil : forall X:Type,
  @my_but_last X [] = None.
Proof. reflexivity. Qed.

Theorem my_but_last_one : forall (X:Type) (x:X),
  my_but_last [x] = None.
Proof. reflexivity. Qed.

Theorem my_but_last_app : forall (X:Type) (xs:list X) (x:X) (y:X),
  my_but_last (app xs [x;y]) = Some x.
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

(** * Problem 4

    Find the number of elements of a list.

    Example in Haskell:
<<
Prelude> myLength [123, 456, 789]
3
Prelude> myLength "Hello, world!"
13
>>
*)

Fixpoint my_length {X:Type} (xs:list X) : nat :=
  match xs with
    | []    => 0
    | _::xt => 1 + my_length xt
  end.

Example my_length1:
  my_length [123; 456; 789] = 3.
Proof. reflexivity. Qed.
Open Scope char_scope.
Example my_length2:
  my_length ["H";"e";"l";"l";"o";",";" ";"w";"o";"r";"l";"d";"!"] = 13.
Proof. reflexivity. Qed.
Close Scope char_scope.

Theorem my_length_nil : forall (X:Type),
  @my_length X [] = 0.
Proof. reflexivity. Qed.

Theorem my_length_eq_length : forall (X:Type) (xs:list X),
  my_length xs = length xs.
Proof.
  intros.
  induction xs as [|x xt].
    reflexivity.
    simpl. apply f_equal. apply IHxt.
Qed.

Theorem my_length_app : forall (X:Type) (xs ys:list X),
  my_length xs + my_length ys = my_length (xs ++ ys).
Proof.
  intros.
  induction xs as [|x xt].
    reflexivity.
    simpl. apply f_equal. apply IHxt.
Qed.
