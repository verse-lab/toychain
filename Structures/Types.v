From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
From fcsl
Require Import ordtype unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)
Module Type Types.
Parameter Timestamp : Set.
Parameter Hash : Set.
Parameter VProof : Set.
Parameter Transaction : Set.

(* These need to be types that can be coerced into ordType *)
Axiom Hash_eqMixin : Equality.mixin_of Hash.
Canonical Hash_eqType := Eval hnf in EqType Hash Hash_eqMixin.
Axiom Hash_ordMixin : Ordered.mixin_of Hash_eqType.
Canonical Hash_ordType := Eval hnf in OrdType Hash Hash_ordMixin.

Axiom VProof_eqMixin : Equality.mixin_of VProof.
Canonical VProof_eqType := Eval hnf in EqType VProof VProof_eqMixin.
Axiom VProof_ordMixin : Ordered.mixin_of VProof_eqType.
Canonical VProof_ordType := Eval hnf in OrdType VProof VProof_ordMixin.

Axiom Transaction_eqMixin : Equality.mixin_of Transaction.
Canonical Transaction_eqType := Eval hnf in EqType Transaction Transaction_eqMixin.
Axiom Transaction_ordMixin : Ordered.mixin_of Transaction_eqType.
Canonical Transaction_ordType := Eval hnf in OrdType Transaction Transaction_ordMixin.

Record Block  :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Definition eq_block b b':=
  match b, b' with
  | mkB p t pf, mkB p' t' pf' =>
    [&& p == p', t == t' & pf == pf']
  end.

Lemma eq_blockP : Equality.axiom eq_block.
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

Canonical Block_eqMixin := Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.

Definition block := Block.
Definition Blockchain := seq block.

Definition TxPool := seq Transaction.
Definition BlockTree := union_map [ordType of Hash] block.
End Types.
