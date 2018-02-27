From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding.
From Toychain
Require Import SeqFacts Chains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record Block {Hash : ordType} {Transaction VProof : eqType} :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Definition eq_block {H : ordType} {T P : eqType} (b b' : @Block H T P) :=
  match b, b' with
  | mkB p t pf, mkB p' t' pf' =>
    [&& p == p', t == t' & pf == pf']
  end.
      
Lemma eq_blockP {H : ordType} {T P : eqType} : Equality.axiom (@eq_block H T P).
Proof.
case=> p t pf; case=> p' t' pf'; rewrite /eq_block/=.
case H2: (p == p'); [move/eqP: H2=>?; subst p'| constructor 2];
  last by case=>?; subst p';rewrite eqxx in H2.
case H3: (t == t'); [move/eqP: H3=>?; subst t'| constructor 2];
  last by case=>?; subst t';rewrite eqxx in H3.
case H4: (pf == pf'); [move/eqP: H4=>?; subst pf'| constructor 2];
  last by case=>?; subst pf';rewrite eqxx in H4.
by constructor 1. 
Qed.

Canonical Block_eqMixin {H : ordType} {T P : eqType} :=
  Eval hnf in EqMixin (@eq_blockP H T P).
Canonical Block_eqType {H : ordType} {T P : eqType} :=
  Eval hnf in EqType (@Block H T P) (@Block_eqMixin H T P).

