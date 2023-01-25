From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat)
.
Check (pair 1 3) : natprod.

Definition extract_first (p : natprod) : nat :=
  match p with
  | pair x y  => x
end.

Compute (extract_first (pair 4 3)).
Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
end.

Compute(swap_pair (3,4)).

Inductive natlist : Type := 
  | nil
  | cons (n : nat) (next : natlist).

Definition mylist := cons 1 (cons 3 nil).
Check mylist : natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist2 := [1;2;3].
Check mylist : natlist.
Definition list3 := 1 :: [].
Compute list3.


Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n::(repeat n count')
end.

Definition mylist3 := repeat 3 4.
Compute (mylist3).

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | n::c => S (length c)
  end.

Compute (length mylist3).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | n::l => n:: (app l l2)
end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default : nat) (l : natlist) :=
  match l with
  | nil => default
  | n::t => n
end.

Definition tl (l : natlist) := 
  match l with
  | nil => nil
  | n::t => t
end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.   