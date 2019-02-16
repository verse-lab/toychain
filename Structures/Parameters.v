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

Parameter Timestamp : Type.
Parameter Hash : ordType.
Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter Address : finType.

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

Definition block := @Block Hash Transaction VProof.
Definition Blockchain := seq block.
Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition TxPool := seq Transaction.
(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.

Parameter GenesisBlock : block.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.

Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.

Parameter FCR : Blockchain -> Blockchain -> bool.
Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).

Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

Axiom txValid_nil : forall t, txValid t [::].

(** VAF **)
Axiom VAF_init : VAF (proof GenesisBlock) [::] (txs GenesisBlock).

Axiom VAF_GB_first :
  forall bc, VAF (proof GenesisBlock) bc (txs GenesisBlock) -> bc = [::].


(** FCR **)
Axiom FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

(* TODO: strengthen to only valid chains *)
Axiom FCR_ext :
  forall (bc : Blockchain) (b : block) (ext : seq block),
    bc ++ (b :: ext) > bc.

Axiom FCR_rel :
  forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.

Axiom FCR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.

Axiom FCR_trans :
  forall (A B C : Blockchain), A > B -> B > C -> A > C.