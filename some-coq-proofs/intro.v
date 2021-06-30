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

(*Coq documentation *)
(*Section is used for modelling. 
It will also give a convenient way to reset part of the development.*)
Section Declaration.
(* Variable name_of_the_variable: whatisit*)
Variable n: nat.
(*n is a natural number*)
(*new is a variable that is positive, hence gt accepts
two arguments, which are both nat, we can also use hypothesis
 also gt works like nat->nat-> prop, hence it gives a prop
hence (gt n 0) is same as ((gt n)0) which is a well constructes
proposition.*)
(*A preposition is a theorem of less importance.*)
(*A lemma is a small theorem which will be used to prove a
larger theorem.*)
Variable new : (gt n 0).
(*Definations see top for more context*)
Definition one := (S O).
Definition two := S one.
(*double requires 'm' which is a nat and returns twice of m*)
Definition double (m : nat) := plus m m.

Section logic.
(*Everything we need to prove is a proposition*)
Variables a b c :Prop.
Check(a -> b).
(*To prove ((a->(b->c))-> (a->b)->(a->c) *)
Goal (a -> b ->c) -> (a->b)->(a->c).



(*after defining our goal we are in proof mode, and we have 
to use tatics to get the proof. Local hypotheses are the ones above
the double line. intros is applicable to any judgement who's 
goal is an implication, by moving the propsition to the 
left to local hypotheses *)
intros h.
intros h4.
intros ha.
(*We notice that C, the current goal, may be obtained from hypothesis H,
 provided the truth of A and B are established. 
The tactic apply implements this piece of reasoning*)
apply h.
exact ha.
apply h4.
apply ha.
Qed.
Lemma impl_ca : (a->b->c)->(a->b)->(a->c).
auto.
Qed.


(*Start from 1.3*)
(*https://coq.inria.fr/tutorial/1-basic-predicate-calculus*)

(*Propositional Logic.*)
(*/\ signifies the and symbol in logical operations
\/ signifies or, a/\b implies a and b *)


(**)
Lemma addcom: a/\b -> b/\a.
intros h.
elim h.
split.
apply H0.
apply H.
Qed.
Lemma orcom : a\/b->b\/a.
intros h.
elim h.
intros h1.
right.
apply h1.
intros h2.
left.
apply h2.
Qed.
(*This could also be done by using tauto*)
(*Lemma nw_addcom: a\/b -> b/\a.
tauto.*)

Lemma prooftrial : (a -> b/\c) -> (a->b) /\ (a->c).
Proof.

split.
intros h.
apply H.
apply h.
intros h'.
apply H.
exact h'.
Qed.

(*Peirces lemma*)
Definition p_l := forall (a b:Prop),((a -> b)->a)->a.
Definition len := forall a,a\/ ~a.


Theorem pl : p_l <-> len.
Proof.
unfold p_l ,len.
firstorder.
apply H with (b := ~(a \/ ~a)).
firstorder.
destruct (H a0).
apply H1.
tauto.
Qed.

Inductive IsEven : nat -> Prop :=
  | EvenO : IsEven O
  | EvenS n : IsOdd n -> IsEven (S n)
with IsOdd : nat -> Prop :=
  | OddS n : IsEven n -> IsOdd (S n).



(*unfold : operates on deination and expands them by applying the variable
for you 
  firstorder : *)
  
  
Lemma even_plus_even: forall n m, IsEven n -> IsEven m -> IsEven (n+m)
 with odd_plus_even: forall n m, IsOdd n -> IsEven m -> IsOdd (n+m).
Proof.
  induction 1; simpl; auto using EvenS.
  induction 1; simpl; auto using OddS.
Qed.
Require Export ZArith.
Require Export Znumtheory.
Require Import Classical.

Check Gauss.


Theorem euclids_first_theorem :
  forall p : Z, prime p ->
                forall a b : Z, (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intros p prime_p a b div.

  elim (classic (p | a)).
  intros. left. assumption.
  intros. right.

  specialize (prime_rel_prime p).
  intros.
  apply H0 with (a:=a) in prime_p; [|assumption].

  specialize (Gauss p a b).
  intros.
  auto.
Qed.





























