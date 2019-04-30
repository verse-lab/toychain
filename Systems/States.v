From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep Relations.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Types Parameters Forests Protocol Address.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NetState (T : Types) (P : ConsensusParams T) (F : Forest T P)
       (A : NetAddr) (Pr : ConsensusProtocol T P F A).
Import T P A Pr.
Definition StateMap := union_map [ordType of Address] State.
Definition initState' s : StateMap := foldr (fun a m => (a \\-> Init a) \+ m) Unit s.
Definition initState := initState' (enum [finType of Address]).

Axiom valid_initState' : forall s,  uniq s -> valid (initState' s).
Axiom dom_initState' : forall s, uniq s -> dom (initState' s) =i s.
End NetState.

Module States (T : Types) (P : ConsensusParams T) (F : Forest T P)
            (A : NetAddr) (Pr : ConsensusProtocol T P F A) <: NetState T P F A Pr.
Import T P A Pr.

Definition StateMap := union_map [ordType of Address] State.

Definition initState' s : StateMap := foldr (fun a m => (a \\-> Init a) \+ m) Unit s.

(* Master-lemma, proving a conjunction of two mutually-necessary facts *)
Lemma initStateValidDom s :
  uniq s -> dom (initState' s) =i s /\ valid (initState' s).
Proof.
elim: s => /=[|a s']; first by rewrite valid_unit dom0.
move => IH.
move/andP => [H_ni H_u].
move/IH: H_u => [H1 H2] {IH}.
split; last first.
- case: validUn; rewrite ?validPt ?H2//.
  move=>k. rewrite domPt inE. move=>/eqP Z. subst k.
  by rewrite H1; move/negP: H_ni.
- move=>z;
  rewrite (domUn (a \\-> Init a) (initState' s')).
  rewrite !inE !domPt !inE.
  rewrite H1.
  case validUn.
  * by move/negP => H_v; case: H_v; rewrite validPt.
  * by move/negP.
  * move => k.
    rewrite H1.
    rewrite domPt inE=>/eqP H_eq.
    rewrite -H_eq => H_in.
    by move/negP: H_ni.
  * move => Hv1 Hv2 H_d.
    by rewrite eq_sym.
Qed.

Lemma valid_initState' s : uniq s -> valid (initState' s).
Proof. by move => H_u; case: (initStateValidDom H_u). Qed.

Lemma dom_initState' s : uniq s -> dom (initState' s) =i s.
Proof. by move => H_u; case: (initStateValidDom H_u). Qed.

Definition initState := initState' (enum [finType of Address]).
End States.