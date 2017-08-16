From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Blockchain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BlockchainOrder.

Definition is_prefix (bc bc' : Blockchain) :=
  exists bc1, bc' = bc ++ bc1.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).

Lemma bc_pre_refl bc : [bc <<= bc].
Proof. by exists [::]; rewrite cats0. Qed.

Lemma bc_pre_trans bc1 bc2 bc3 :
  [bc1 <<= bc2] -> [bc2 <<= bc3] -> [bc1 <<= bc3].
Proof.
case=> a1 H1 [a2] H2; subst bc2.
by rewrite -catA in H2; exists (a1 ++ a2).
Qed.

Lemma bc_pre_gt bc bc' :
  [bc <<= bc'] -> bc' > bc.
Proof.
by case=>ext=>eq; rewrite eq; apply CFR_ext.
Qed.

End BlockchainOrder.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).

Section Forks.

Definition fork (bc bc' : Blockchain) : Prop :=
  exists (b : Block),
    bcSucc b bc != bcSucc b bc'.

(* TODO: prove fork facts! *)
Lemma bc_fork_neq bc bc' :
  fork bc bc' -> bc != bc'.
Proof.
case=> Of; case bc; case bc'; do? by [].
move=> h' B' h B. rewrite eqseq_cons negb_and.
Admitted.

Lemma bc_fork_sym bc bc' :
  fork bc bc' -> fork bc' bc.
Proof.
Admitted.

Lemma bc_fork_trans bc1 bc2 bc3 :
  fork bc1 bc2 -> fork bc2 bc3 -> fork bc1 bc3.
Proof.
case=> b1 H1 [b21] H2. rewrite /fork.
Admitted.

(*  /--B
* --
*   \-----A---C
*)
Lemma bc_fork_prefix A B C :
  fork A B -> [A <<= C] -> fork B C.
Proof.
Admitted.

Axiom btChain_fork :
  forall (bt : BlockTree) (bc : Blockchain) (b : Block),
  let: bc' := btChain (btExtend bt b) in
    btChain bt = bc ->
    b \notin bc ->
    prevBlockHash (bcLast bc') != hashB (bcLast bc) ->
    fork bc bc'.

End Forks.
