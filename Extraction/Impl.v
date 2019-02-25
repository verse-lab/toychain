From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
From fcsl
Require Import ordtype unionmap.
From Toychain
Require Import Types TypesImpl Parameters Address.
Require Import BinNat BinNatDef.
Require Import HexString String Ascii.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: find a way to remove this stuff from the extraction! *)
(** Instantiate Toychain with a proof-of-work scheme **)
Module ProofOfWork <: (ConsensusParams TypesImpl).
Import TypesImpl.

Definition GenesisBlock : block :=
  mkB ((of_N 0) <: Hash)
      [::]
      (tt <: VProof).

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.
Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

(* Hash should be HexStrings prefixed with 0x, e.g. '0x1c2139314aab35' *)
Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.

Definition WorkAmnt := N_ordType.

(* TODO: don't hardcode the length of the hash *)
Definition work (b : block) : WorkAmnt :=
  (256 - N.log2 (to_N (hashB b)))%N.
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
  if List.length bc > List.length bc' then true else
  if List.length bc' > List.length bc then false else
  (* TODO: If same amount of work AND same length, compare based on actual value *)
  (* seq block is an ordType if block is ordType *)
  true.

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).

Definition txValid (tx : Transaction) (bc : Blockchain) :=
  tx \notin flatten (map (fun b => txs b) bc).

(* bt is an argument to allow you to validate transactions before
    adding them to your pool. However, all transactions are valid for us.
 *)
Definition tpExtend (tp : TxPool) (bt : BlockTree) (tx : Transaction) :=
  if tx \in tp then tp else (tx::tp).


(* You'd normally want some difficulty adjustment, but we're just toying around *)
(* TODO: don't hardcode difficulty *)
Definition VAF (b : Block) (bc : Blockchain) (tp : TxPool) : bool :=
  (* GenesisBlock doesn't have work requirements *)
  if (b == GenesisBlock) then
    if (bc == [::]) && (tp == [::]) then true else false
  (* All other blocks do *)
  else if (16 <? (work b))%N then true else false.

(* For proof-of-work, this would be more aptly called "getNonce" *)
(* TODO: Implement this in the extraction *)
(* We can't (reasonably) implement this in Coq since it required randomness. *)
Parameter genProof : Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

Lemma txValid_nil : forall t, txValid t [::].
Proof. done. Qed.

(** VAF **)
Lemma VAF_init : VAF GenesisBlock [::] (txs GenesisBlock).
Proof. by rewrite/VAF !eq_refl. Qed.

Lemma VAF_GB_first :
  forall bc, VAF GenesisBlock bc (txs GenesisBlock) -> bc = [::].
Proof. by rewrite/VAF eq_refl=>bc; case: ifP=>//=; move/andP; case=>/eqP. Qed.

(** FCR **)
Axiom FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

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
