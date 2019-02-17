From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
From fcsl
Require Import ordtype unionmap.
From Toychain
Require Import Blocks Parameters.
Require Import BinNat BinNatDef.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Instantiate Toychain with a proof-of-work scheme **)

Module ProofOfWork <: ConsensusParams.

(* Need to do some massaging to get Coq types that extract nicely to
  play well with SSReflect. *)
(* N is ordType *)
Section NOrd.
Lemma irr_ltbN : irreflexive N.ltb.
Proof. by case=>[|n]//; apply N.ltb_irrefl. Qed.

Lemma trans_ltbN : transitive N.ltb.
Proof.
by move=>x y z; move=>/N.ltb_lt A /N.ltb_lt B;
   apply/N.ltb_lt; move: (N.lt_trans _ _ _ A B).
Qed.

Lemma total_ltbN x y : [|| N.ltb x y, x == y | N.ltb y x].
Proof.
apply/or3P; case: (N.compare_spec x y).
by move=>->; constructor 2.
by constructor 1; apply/N.ltb_lt.
by constructor 3; apply/N.ltb_lt.
Qed.

Definition N_ordMixin := OrdMixin irr_ltbN trans_ltbN total_ltbN.
Canonical Structure N_ordType := OrdType N N_ordMixin.
End NOrd.


(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)

Definition Timestamp := N_ordType.
Definition Hash := N_ordType.
Definition VProof := unit_ordType.
Definition Transaction := N_ordType.

Definition block := @Block Hash Transaction VProof.
Definition Blockchain := seq block.
Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Definition TxPool := seq Transaction.
(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.

Definition GenesisBlock : block := mkB (N_of_nat 0) [::] tt.
Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

(* TODO: Implement this in the extraction *)
Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.

Definition WorkAmnt := N_ordType.

(* TODO: don't hardcode the length of the hash *)
Definition work (b : block) : WorkAmnt := (256 - N.log2 (hashB b))%N.
Fixpoint total_work (bc : Blockchain) : N_ordType :=
  match bc with
  | b::bc' => (work b + total_work bc')%N
  | [::] => N_of_nat 0
  end.

Definition FCR bc bc' : bool :=
  let w := total_work bc in
  let w' := total_work bc' in

  if w > w' then true else
  if w < w' then false else
  (* If same amount of work, compare based on length. *)
  if length bc > length bc' then true else
  if length bc' > length bc then false else
  (* TODO: If same amount of work AND same length, compare based on actual value *)
  (* seq block is an ordType if block is ordType *)
  true.

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).

Definition txValid (tx : Transaction) (bc : Blockchain) := true.

(* bt is an argument to allow you to validate transactions before
    adding them to your pool. However, all transactions are valid for us.
 *)
Definition tpExtend (tp : TxPool) (bt : BlockTree) (tx : Transaction) :=
  if tx \in tp then tp else (tx::tp).


(* You'd normally want some difficulty adjustment, but we're just toying around *)
(* TODO: don't hardcode difficulty *)
Definition VAF (b : Block) (bc : Blockchain) (tp : TxPool) : bool :=
  if (16 <? (work b))%N then true else false.

(* For proof-of-work, this would be more aptly called "getNonce" *)
(* TODO: Implement this in the extraction *)
(* We can't (reasonably) implement this in Coq since it required randomness. *)
Parameter genProof : Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

Axiom txValid_nil : forall t, txValid t [::].

(** VAF **)
Axiom VAF_init : VAF GenesisBlock [::] (txs GenesisBlock).

Axiom VAF_GB_first :
  forall bc, VAF GenesisBlock bc (txs GenesisBlock) -> bc = [::].


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

End ProofOfWork.