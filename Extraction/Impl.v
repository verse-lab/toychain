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
  mkB (("0x6150cb353fe365318be1040f4f1d55ba6a6235c7fdee7e94602fed76f112f2de")%string <: Hash)
      [::]
      ((N_of_nat 0) <: VProof).

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.
Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

(* Hash should be HexStrings prefixed with 0x, e.g. '0x1c2139314aab35' *)
Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.

Definition WorkAmnt := N_ordType.

(* Lookup table; lz[i] = how many leading 0s does i have as a 4-bit binary number ? *)
Let leading_zeroes : seq N :=
  [:: 4; 3; 2; 2; 1; 1; 1; 1;
      0; 0; 0; 0; 0; 0; 0; 0
  ]%N .

Fixpoint _cbzs (s : string) : N :=
  match s with
  | String c s =>
        let d_opt := ascii_to_digit c in
        match d_opt with
        | None => N0
        | Some d =>
          let lz := (nth N0 leading_zeroes d) in
          if lz == N_of_nat(4) then (lz + _cbzs s)%N else lz
        end
  | _ => N0
  end.

(* Given a hex string, count how many binary zeroes it starts with *)
Definition count_binary_zeroes (s : string) : N :=
  match s with
  | String s0 (String so s)
      => if ascii_dec s0 "0"
        then if ascii_dec so "x"
          then _cbzs s
          else N0
        else N0
  | _ => N0
  end.

Definition work (b : block) : WorkAmnt :=
  count_binary_zeroes (hashB b).

Fixpoint total_work (bc : Blockchain) : N :=
  match bc with
  | b::bc' => (work b + total_work bc')%N
  | [::] => N_of_nat 0
  end.


(* (* For some reason, only ltb is defined in BinNatDef *) *)
(* Definition gtb x y := *)
(*  match (x ?= y)%N with Gt => true | _ => false end. *)

(* Infix ">?" := gtb (at level 70, no associativity) : N_scope. *)

(* This is supposed to behave as >, not < *)
Definition FCR bc bc' : bool :=
  let w := total_work bc in
  let w' := total_work bc' in
  let l := (List.length bc) in
  let l' := (List.length bc') in
  let eW := w == w' in
  let eL := l == l' in
  let eO := bc == bc' in

  (* This is written in this weird fashion to be able to prove both
     transitivity and totality. *)
  match eW, eL, eO with
  | true, true, true => false
  | true, true, false => ords bc bc'
  | true, _, _ => ~~ (Nat.leb l l')
  | false, _, _ => ~~ (w <=? w')%N
  end.

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
  else if (12 <? (work b))%N then true else false.

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
(* It's a bit of a pain to prove these, since we have different types of numbers. *)
Lemma FCR_ext :
  forall (bc : Blockchain) (b : block) (ext : seq block),
    bc ++ (b :: ext) > bc.
Proof.
move=>bc b ext; rewrite/FCR.
(* When total work is different, LHS will have more work *)
case: ifP; last first.
- move=>A; rewrite -N.ltb_antisym; elim: bc A=>//=.
  + move/negbT=>A; apply/N.ltb_lt.
    Search _ (~~ (?a  == 0)).
    (* lt0n is the nat version of this *)
    admit.
  + move=>x xs Hi X.
    case Q: (total_work (xs ++ b :: ext) == total_work xs).
    by move/eqP in Q; rewrite Q eq_refl in X.
    by specialize (Hi Q); move/N.ltb_lt in Hi;
       case: (N.add_lt_mono_l (total_work xs) (total_work (xs ++ b :: ext))  (work x))=>P _ ;
       specialize (P Hi); apply/N.ltb_lt.

(* When total work is equal, LHS is longer *)
- case: ifP;
  have X: (Datatypes.length bc + 0 = Datatypes.length bc) by [].
  by rewrite List.app_length -{2}X eqn_add2l.
  by move=>_ _; rewrite -PeanoNat.Nat.ltb_antisym List.app_length -{1}X;
     apply/PeanoNat.Nat.ltb_lt/ltP; rewrite ltn_add2l.
Admitted.

Lemma FCR_nrefl :
  forall (bc : Blockchain), bc > bc -> False.
Proof. by move=>bc; rewrite/FCR !eq_refl. Qed.

Lemma FCR_trans :
  forall (A B C : Blockchain), A > B -> B > C -> A > C.
Proof.
move=>x y z; rewrite/FCR.
case: ifP; case: ifP; case: ifP=>//=.
- case: ifP; case: ifP=>//=.
  + case: ifP=>//=;
    move=>A /eqP -> /eqP -> B /eqP -> /eqP -> C D;
    rewrite !eq_refl; case: ifP.
    by move/eqP=>X; subst z; move: (trans_ords C D) (irr_ords x)=>->.
    by move: (trans_ords C D).
  + by move=>A /eqP -> B /eqP -> /eqP ->; rewrite !eq_refl A.
  + by move=>/eqP -> A B /eqP -> /eqP A'; rewrite A' eq_refl in A.
  + by move=>_ _ _ _ /eqP ->.
- move=>/eqP -> A /eqP -> B; rewrite !eq_refl; case: ifP; case: ifP=>//=.
  + case: ifP.
    by move=>/eqP <- _ /eqP A'; rewrite A' eq_refl in A.
    by move=>_ _ /eqP B'; rewrite B' in B.
  + move=>/eqP <- _; move: B; rewrite -!PeanoNat.Nat.ltb_antisym;
    move/PeanoNat.Nat.ltb_lt/ltP=>B; move/PeanoNat.Nat.ltb_lt/ltP=>B'.
      by move: (ltn_trans B B') (ltnn (Datatypes.length y))=>->.
    move=>_ _; move: B; rewrite -!PeanoNat.Nat.ltb_antisym.
    move/PeanoNat.Nat.ltb_lt/ltP=>B; move/PeanoNat.Nat.ltb_lt/ltP=>B'.
      by move/ltP/PeanoNat.Nat.ltb_lt: (ltn_trans B' B).
- by move=>A B /eqP ->; rewrite A.
- by move=>/eqP <- /eqP <- A; rewrite A.
- by move=>A /eqP <- B; rewrite B.
- by move=>/eqP-> A _; rewrite -!N.ltb_antisym;
     move/N.ltb_lt=>B; move/N.ltb_lt=>B';
     move: (N.lt_trans _ _ _ B B') (N.lt_irrefl (total_work y)).
by move=>_ _ _; rewrite -!N.ltb_antisym;
   move/N.ltb_lt=>A; move/N.ltb_lt=>B; apply/N.ltb_lt;
   move: (N.lt_trans _ _ _ B A).
Qed.


Axiom FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.

Axiom FCR_rel :
  forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.

End ProofOfWork.
