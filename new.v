(* Introduction to Coq *)

(*Datatype for natural numbers*)
(*nat is a datatype *)
(*Inductive nat : Set := 
  |O : nat
  |S : nat -> nat.
The first one gives zero
  Second one gives 1 
  and the third one makes up 3 *)

Eval compute in O.
Eval compute in (S O).
Eval compute in (S(S(S O))).
(*We can write natural number as is in coq *)
Eval compute in 3. (*Returns datatype nat*)
Print nat.
(*Print the defintion of nat and is same as the one defined above*)



(*Defining Addition: For recursive function we use Fixpoint  *)
(*This means that adding a and b where a and b both
are natural numbers and : nat signifies that the returned value
is also a natural number*)
Fixpoint add(a b:nat) : nat :=
  match a with
  | 0 => b
  | S n => S(add n b)
  end.

Theorem add_associ: forall (a b c: nat),
  (add a (add b c)) = (add (add a b) c).
Proof.
intros a b c.
induction a. simpl. reflexivity.
simpl. rewrite -> IHa. reflexivity.
Qed.
(*eq_refl means equality*)
Definition test : 1 = 1:= eq_refl 1.
Theorem test' : 1 = 1.
Proof.
reflexivity.
Qed.
Print test.
Print test'.
(*Pred function *)
Definition pred(n : nat) : nat :=
match n with
|O => O
|S n' => n
end.


Check 0.

Print reflexivity.

(**)


(*This function below gives the associative property
for addition*)

(*Defination of a Predecisor function*)

(**)




