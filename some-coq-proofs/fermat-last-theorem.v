(*Pre-req*)
Require Import ssreflect.
(*ssreflext provides an extension of Coq for tactics *)
Require Import Coq.omega.Omega.
Require Import BinNums.
Require Coq.Init.Nat.
Require Import Bool Morphisms Setoid.
Require Import ssreflect ssrfun ssrbool.
Require Import BinNat.
Require BinPos Ndec.
Require Import Coq.Classes.Equivalence.
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.

Set Implicit Arguments.


(*Introducing ~ as a new notation for describing binaries and should be left associative
which means that during compilations they are grouped from the left. eg, if '*' is left
associative a*b*c will be interpreted as (a*b)*c

Here ~ is an assignment of a binary. 
For More: https://en.wikipedia.org/wiki/Operator_associativity

positive_scope defines that binary is strictly positive.

 *)
Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope. 

Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Local Open Scope positive_scope.
Module Pos.


(*Fermat's Last Theorem 

    Given the whole numbers a,b,c,n there exists no case of 

              a^n + b^n = c^n st. n > 2
Defn. A Fermat Triplet- A set of (a,b,c) for which the fermat theorem holds true.

Before we go to Fermat's Theorem there's quite an interesting conjecture given by Euler
which states that or all integers n and k greater than 1, if the sum of n kth powers of positive
integers is itself a kth power, then n is greater than or equal to k. Fermat's Last Theorem
comes close to this at n=2 but Fermat's exists only beyond n > 2, but this provides a great
inutition for Fermat's, it's also been proved false by arguably the first supercomputer
CDC 6600, so there is scope for proving Fermat's as well.
*)

(*To prove Fermat's Last Theorem we can start to work with Wiles but the proof is skeched
by proving 4 thoerems(http://www.cs.rug.nl/~wim/fermat/wilesEnglish.html#cite) 


Th1: If there is a Fermat triple for exponent n, there is a Fermat triple (a,b,c) for exponent n with a and b coprime.
Th2: There is no Fermat triple for exponent 4.
Th3: There is no Fermat triple for exponent 3.
Th4:  If there is a Fermat triple for an exponent > 4, then there is a Fermat triple for an exponent which is a prime number > 4. 

There are actually 7 theorems that need to be satisfied, but they're too compicated and I don't know Coq that well but we can make do with 4. *)

(*

To check if ~ works
Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.
*)

(*Numbers are Coprime iff. the common factor is 1*)
(*Fixpoint is used for Recursive Functions and Multiple args*)
(*Th1-Proof: Let (x,y,z) be some Fermat triple for exponent n. 
  Let d be the greatest common divisor of x and y. Since xn + yn = zn, the number dn divides zn; therefore d divides z. 
  Put a = x/d, b = y/d, c = z/d. Then (a,b,c) is a Fermat triple for exponent n with a and b coprime. *)
Fixpoint gcdn (n : nat) (a b : positive) : positive :=
  match n with
    | O => 1 (* when 0 *)
    | S n => (*Natural Number*)
      match a,b with
        | 1, _ => 1
        | _, 1 => 1
        | a~0, b~0 => (gcdn n a b)~0
        | _ , b~0 => gcdn n a b
        | a~0, _ => gcdn n a b
        | a'~1, b'~1 =>
          match a' ?= b' with
            | Eq => a
            | Lt => gcdn n (b'-a') a
            | Gt => gcdn n (a'-b') b
          end
      end
  end.
(*The reduction for gcdn given for all x,y,t if t divides x and for all t' if t' divides x and t' divides y then the gcd of x,y is t  *)
(*Can be reduced using Peirces lemma *)
Lemma gcdn_red: forall t x y, t %| x -> (forall t', t' %| x -> t' %| y -> t' %| t) -> gcdn x y = t.
Lemma gcdwithx x a b : gcdn ((x*a) (x*b)) == x -> gcdn a b == 1.
Proof.
  move.
  intros k.
  apply/eqP/gcdn_red; try by [].
  intros.
Admitted.
(* a%%b remainder of 'a' when divided by 'b'
  a %/b quotient of a when divided by b *)

Lemma coprime_gcd a b : coprime (a %/ (gcdn a b)) (b %/ (gcdn a b)).
Proof.
  unfold coprime.
  apply (gcdwithx (gcdn a b)).  
  apply/eqP.
  apply gcdn_def; try by [].
  admit.
  admit.
  intros d' H H0
admit.

Admitted.

(*Adding every component together*)
Theorem Th1 : forall n, (exists x y z, x^n + y^n = z^n) -> (exists a b c, a^n + b^n = c^n /\ (coprime a b)).
Proof.
  intros n [x [y [z H]]].
  pose (d := gcdn x y).

  (* assert (ddivx : d %| x). *)
  
  exists (x %/ d).
  exists (y %/ d).
  exists (z %/ d).
  split.

unfold d.
Admitted.

(*Proof for these is quite straight forward so not doing this a good resource to understand these is https://www.math.uci.edu/~brusso/vanderPoortenpp1-6.pdf

*)
Theorem Th2 : forall a b c, a^4 + b^4 <> c^4.
Proof.
Admitted.

Theorem Th3 : forall a b c, a^3 + b^3 <> c^3.
Proof.
Admitted.

Theorem Th3 : (exists a b c n, n > 4 /\ a^n + b^n = c^n) ->
                                    (exists a b c n, n > 4 /\ prime n /\ a^n + b^n = c^n).
Proof.
  simpl.
Admitted.


(*Proof By Contradiction*)
Theorem fermats_last_theorem : ~exists a b c n, a^n + b^n = c^n /\ n > 2.
Proof.
  red.
  
  intros [a [b [c [n [eq ngt]]]]].
  assert (nn4 : n <> 4). {
    specialize (Th2 a b c).
    red; intros; rewrite H0 in eq; rewrite eq in H; contradiction.
  }
  assert (nn3 : n <> 3). {
    specialize (Th3 a b c).
    red; intros; rewrite H0 in eq; rewrite eq in H; contradiction.
  }

  assert (ngt4 : n > 4). {
    rewrite ltn_neqAle ltn_neqAle.
    case and3P.
    intros; by [].
    intros.
    destruct n0.
    split.
    apply/eqnP; auto.
    apply/eqnP; auto.
    assumption.
  }
  clear ngt nn4 nn3.

  specialize (Th4).
  intros.
  destruct H.
  exists a, b, c, n.
  split; assumption.
  clear a b c n eq ngt4.
  rename x into a.
  destruct H as [b [c [n [ngt [pn eq]]]]].

  specialize (Th1 n).
  intros.
  destruct H.
  exists a,b,c.
  assumption.
  clear a b c eq.
  rename x into a.
  destruct H as [b [c [eq coab]]].
Admitted.


