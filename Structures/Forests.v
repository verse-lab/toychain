From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Blocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A formalization of a block forests *)
(* TODO: Go through this file and put the lemmas in a sensible order. *)

(************************************************************)
(******************* <parameters> ***************************)
(************************************************************)

Parameter Timestamp : Type.
Parameter Hash : ordType.
Parameter VProof : eqType.
Parameter Transaction : eqType.
Parameter Address : finType.

Definition block := @Block Hash Transaction VProof.

Parameter GenesisBlock : block.

Definition Blockchain := seq block.

(* In fact, it's a forest, as it also keeps orphan blocks *)
Definition BlockTree := union_map Hash block.

(* Transaction pools *)
Definition TxPool := seq Transaction.

Parameter hashT : Transaction -> Hash.
Parameter hashB : block -> Hash.
Parameter genProof : Address -> Blockchain -> TxPool -> Timestamp -> option (TxPool * VProof).
Parameter VAF : VProof -> Blockchain -> TxPool -> bool.
Parameter FCR : Blockchain -> Blockchain -> bool.

(* Transaction is valid and consistent with the given chain *)
Parameter txValid : Transaction -> Blockchain -> bool.
Parameter tpExtend : TxPool -> BlockTree -> Transaction -> TxPool.

(************************************************************)
(********************* </parameters> ************************)
(************************************************************)

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

(************************************************************)
(*********************** <axioms> ***************************)
(************************************************************)

(* 2.  Transaction validation *)

Axiom txValid_nil : forall t, txValid t [::].

(* 3.  Hashes *)

(* Axiom hashB_inj : injective hashB. *)

(* 4.  VAF *)

Axiom VAF_init : VAF (proof GenesisBlock) [::] (txs GenesisBlock).

Axiom VAF_GB_first :
  forall bc, VAF (proof GenesisBlock) bc (txs GenesisBlock) -> bc = [::].

(* 2. FCR *)

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

(************************************************************)
(*********************** </axioms> **************************)
(************************************************************)

Lemma FCR_trans_eq (A B C : Blockchain):
    A >= B -> B >= C -> A >= C.
Proof.
case=>H1[]H2.
- by subst C B; left.
- by subst B; right.
- by subst C; right.
by right; apply: (FCR_trans H1).
Qed.

Lemma FCR_trans_eq1 (A B C : Blockchain):
    A >= B -> B > C -> A > C.
Proof. by move=>[]H1 H2; [by subst B|]; apply: (FCR_trans H1). Qed.

Lemma FCR_trans_eq2 (A B C : Blockchain):
    A > B -> B >= C -> A > C.
Proof. by move=>H1[]H2; [by subst B|]; apply: (FCR_trans H1). Qed.

Lemma FCR_dual :
  forall (A B : Blockchain),
    (A > B = false) <-> (B >= A).
Proof.
split=>H.
* move: (FCR_rel A B); rewrite H; case; case; do? by [|right];
  by move=>/eqP H'; left; apply/eqP; rewrite eq_sym.
* case: H.
  by move=>->; case X: (A > A); by [|move: (FCR_nrefl X)].
  by move=>H; case X: (A > B); by [|move: (FCR_nrefl (FCR_trans H X))].
Qed.

Lemma Geq_trans :
  forall (A B C : Blockchain),
  A >= B -> B >= C -> A >= C.
Proof.
move=> A B C H1 H2; case: H1; case: H2.
by move=><- <-; left.
by move=>H ->; right.
by move=><-; right.
by move=>H1 H2; move: (FCR_trans H2 H1); right.
Qed.

Lemma FCR_excl :
  forall (bc bc' : Blockchain),
    bc > bc' -> bc' > bc -> False.
Proof.
by move=>bc bc' H1 H2; move: (FCR_trans H1 H2); apply FCR_nrefl.
Qed.


(******************************************************************)
(*                BlockTree implementation                        *)
(******************************************************************)

Definition btHasBlock (bt : BlockTree) (b : block) :=
  (#b \in dom bt) && (find (# b) bt == Some b).

Notation "b ∈ bt" := (btHasBlock bt b) (at level 70).
Notation "b ∉ bt" := (~~ btHasBlock bt b) (at level 70).

Definition has_init_block (bt : BlockTree) :=
  find (# GenesisBlock) bt = Some GenesisBlock.

Lemma has_init_block_free bt hb :
  has_init_block bt -> # GenesisBlock != hb ->
  has_init_block (free hb bt).
Proof. move=>Ib /eqP Ng; rewrite/has_init_block findF; case: ifP=>/eqP//=. Qed.

Definition validH (bt : BlockTree) :=
  forall h b, find h bt = Some b -> h = hashB b.

Lemma validH_free bt (b : block) :
  validH bt -> validH (free (# b) bt).
Proof. by move=>Vh h c; rewrite findF;case: ifP=>//_ /Vh. Qed.

Lemma validH_PtUn bt (b : block) :
  valid (#b \\-> b \+ bt) -> validH bt -> validH (#b \\-> b \+ bt).
Proof.
move=>V Vh; rewrite/validH=>ha a; rewrite findUnR ?V //=; case: ifP.
by specialize (Vh ha a).
rewrite findPt2 //=; case: ifP=>//=.
by move/andP=>[/eqP H _]; subst ha=>D; case=>E; subst b.
Qed.

Lemma validH_undef : validH um_undef.
Proof. by rewrite/validH=>h b; rewrite find_undef. Qed.

Definition btExtend (bt : BlockTree) (b : block) :=
  (* We only add "fresh" blocks *)
  if #b \in dom bt then
    if find (# b) bt == Some b then bt
    (* A hash collision makes the blocktree undefined *)
    else um_undef
  else (#b \\-> b \+ bt).

Lemma btExtendV bt b :
  valid (btExtend bt b) -> valid bt.
Proof.
rewrite/btExtend; case: ifP.
by case: ifP=>//=; rewrite valid_undef.
by move=>Nd; rewrite validPtUn Nd //==>[/andP] [].
Qed.

Lemma btExtendV_comm bt a b :
  valid (btExtend (btExtend bt a) b) =
  valid (btExtend (btExtend bt b) a).
Proof.
rewrite/btExtend; case: ifP; case: ifP; case: ifP; case: ifP;
move=>A B C D.
by rewrite D C B.
by rewrite D dom_undef in_nil validPtUn valid_undef.
by rewrite dom_undef in D.
by rewrite dom_undef in D.
- case: ifP; case: ifP.
  case: ifP=>X Y Z.
  by rewrite Y X in A; rewrite A in C.
  by rewrite find_undef in Z.
  by move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] _;
     move/eqP=>->_ ; rewrite !validPtUn !inE.
  case: ifP=>X Y Z.
  by rewrite Y X in A; rewrite A in C.
  by rewrite Y X dom_undef in A.
  move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP[]->.
    move/eqP=>E; move: A; rewrite X domPtUn inE=>/andP[]V _.
    move: B; rewrite E findUnR; last by move: V; rewrite !validPtUn.
    rewrite X findPt //==>/eqP []E'; subst b;
    by rewrite findUnR ?V //= X findPt //==>/eqP [].
- case: ifP.
  case: ifP=>X Y //=.
  by move: D; rewrite domPtUn inE Y=>/andP[] V _;
    move: B; rewrite findUnR ?V //= Y X.
  by move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] V;
    move/eqP=>E; move: A; rewrite X E domPtUn inE eq_refl Bool.orb_true_l;
    move: V; rewrite !validPtUn C X !Bool.andb_true_r//==>->.
- case: ifP; case: ifP=>//=.
  case: ifP=>X Y Z=>//=.
  by rewrite Y X in A; rewrite A in C.
  move=>X; move: D; rewrite domPtUn inE X Bool.orb_false_r=>/andP [] V.
  move/eqP=>E; move: B; rewrite E !findUnR;
    do? by move:V; rewrite !validPtUn C X //=.
  by rewrite X !findPt //= eq_sym=>->.
- case: ifP.
  case: ifP=>X Y; move: B; rewrite findUnR.
  by case: ifP; [rewrite X | rewrite Y].
  by move: D; rewrite domPtUn inE validPtUn Y C //==>/andP[].
  by case: ifP; rewrite join_undefR.
  by move: D; rewrite domPtUn inE validPtUn Y C //==>/andP[].
  by rewrite joinA (joinC (#a \\-> _) (#b \\-> _)) -joinA;
     rewrite validPtUn inE D //= Bool.andb_false_r valid_undef.
- rewrite D in A *; case: ifP=>//=.
  rewrite findUnR. by rewrite C B.
  by move: A; rewrite domPtUn inE=>/andP[].
- rewrite D in A *.
  by rewrite validPtUn D !validPtUn A D //= !Bool.andb_true_r.
- case: ifP; case: ifP; do? by rewrite join_undefR.
  case: ifP=>X Y Z.
  by rewrite Z in B.
  by rewrite find_undef in Z.
  move=>X; rewrite findUnR. by rewrite C B.
  by move: A; rewrite X domPtUn validPtUn inE X C //=;
     rewrite Bool.orb_true_r !Bool.andb_true_r.
- case: ifP.
  case: ifP=>X Y; first by rewrite Y X C in A.
  by rewrite !join_undefR.
  rewrite joinA (joinC (#a \\-> _) (#b \\-> _)) -joinA.
  suff: (# a \\-> a \+ bt) = um_undef by move=>->.
  by apply invalidE; rewrite validPtUn C Bool.andb_false_r.
- case: ifP; case: ifP=>X Y; do? by rewrite X C in B.
  by rewrite find_undef in Y.
  by rewrite X dom_undef in_nil in B.
- case: ifP; first by rewrite !validPtUn A C D //= !Bool.andb_true_r.
  move: B; rewrite domPtUn inE C Bool.orb_false_r=>/andP[]V /eqP E.
  contradict D.
  rewrite domPtUn inE E eq_refl Bool.orb_true_l Bool.andb_true_r.
  by move: V; rewrite !validPtUn C //= Bool.andb_true_r=>/andP[]->.
- case: ifP=>X.
  contradict D.
    rewrite domPtUn inE A Bool.orb_true_r validPtUn C //=.
    case V: (valid bt)=>//=.
    move: (invalidE bt); rewrite V //=; case=>Z _.
    have T: true by []. specialize (Z T).
    by move: Z A=>->; rewrite dom_undef in_nil.
  by rewrite joinA (joinC (#b \\-> _)) -joinA !validPtUn //=;
     rewrite A //= Bool.andb_false_r valid_undef !Bool.andb_false_l.
by rewrite !joinA (joinC (#b \\-> _) (#a \\-> _)).
Qed.

Lemma btExtendV_fold1 bt bs b :
  valid (foldl btExtend bt (rcons bs b)) -> valid (foldl btExtend bt bs).
Proof.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP.
case: ifP=>_ _ =>//=; last by rewrite valid_undef.
by move=>_; rewrite validPtUn /= =>/andP[H _].
Qed.

Lemma btExtendV_fold bt xs ys :
  valid (foldl btExtend bt (xs ++ ys)) -> valid (foldl btExtend bt xs).
Proof.
elim/last_ind: ys=>[|ys y Hi]; first by rewrite cats0.
by rewrite foldl_cat; move/btExtendV_fold1; rewrite -foldl_cat; apply Hi.
Qed.

Lemma btExtendV_fold_xs bt xs :
  valid (foldl btExtend bt xs) -> valid bt.
Proof.
have X: xs = ([::] ++ xs) by rewrite cat0s.
by rewrite X; move/btExtendV_fold.
Qed.

Lemma btExtendV_fold_dom bt xs b :
  valid (foldl btExtend bt xs) -> b \in xs ->
  # b \in dom (foldl btExtend bt xs).
Proof.
elim/last_ind: xs=>[|xs x Hi]//=.
move=>V; move: (btExtendV_fold1 V)=>V0; specialize (Hi V0).
rewrite -cats1 mem_cat inE=>/orP; case; last first.
- move/eqP=>E; subst x.
  rewrite foldl_cat //= {1}/btExtend; case: ifP; last first.
  by move=>X; rewrite domPtUn validPtUn V0 X inE X //=; apply/orP; left.
  case: ifP=>//= F D.
  by move: V; rewrite -cats1 foldl_cat //= {1}/btExtend D F valid_undef.
move=>X; specialize (Hi X).
rewrite foldl_cat //= {1}/btExtend; case: ifP; last first.
by move=>D; rewrite domPtUn validPtUn V0 D inE Hi //=; apply/orP; right.
case: ifP=>//= F D.
by move: V; rewrite -cats1 foldl_cat //= {1}/btExtend D F valid_undef.
Qed.

Lemma btExtendV_fold_dup bt xs a b :
  valid (foldl btExtend bt (rcons xs a)) ->
  b \in xs -> #a = #b -> a = b.
Proof.
elim/last_ind: xs=>[|xs x H]//=.
rewrite -!cats1 !foldl_cat //=.
have E: (btExtend (btExtend (foldl btExtend bt xs) a) x) =
        foldl btExtend bt (rcons (rcons xs a) x)
by rewrite -!cats1 -catA !foldl_cat //=.
rewrite btExtendV_comm E=>V; move: (btExtendV_fold1 V)=>V0.
specialize (H V0); rewrite mem_cat inE=>/orP; case=>//=.
move/eqP=>Eq; subst x; move=>Hh.
case X: (a == b); first by move/eqP: X.
contradict V.
rewrite -!cats1 !foldl_cat //=.
move: (btExtendV_fold1 V0)=>V1.
rewrite{1}/btExtend; case: ifP.
- case: ifP.
  rewrite{5}/btExtend; case: ifP.
  case: ifP; last by rewrite valid_undef.
  rewrite -Hh.
  move=>A B C _; contradict C.
  by rewrite{1}/btExtend B A; move/eqP: A=>-> /eqP [] Y;
     rewrite Y eq_refl in X.
  move=>A B C D; move: B.
  by rewrite{1}/btExtend A -Hh findPtUn ?D //==>/eqP [] Y;
     rewrite Y eq_refl in X.
  by rewrite valid_undef.
move=>D; rewrite{1}/btExtend.
case: ifP.
case: ifP; last by rewrite join_undefR valid_undef.
by move=>B A; rewrite -Hh validPtUn A //= Bool.andb_false_r.
by rewrite -Hh joinA (joinC _ (foldl btExtend _ _));
   move=>_; apply/negP; apply invalidE; rewrite pts_undef join_undefR.
Qed.

Lemma btExtendH bt b : valid bt -> validH bt -> validH (btExtend bt b).
Proof.
move=>V H z c; rewrite /btExtend.
case: ifP=>X.
- case: ifP=>_; by [move/H | rewrite find_undef].
rewrite findUnL ?validPtUn ?V ?X//.
case: ifP=>Y; last by move/H.
rewrite domPtK inE in Y; move/eqP: Y=>Y; subst z.
by rewrite findPt; case=>->.
Qed.

Lemma btExtendH_fold bt bs :
  validH bt -> valid (foldl btExtend bt bs) ->
  validH (foldl btExtend bt bs).
Proof.
move=>Vh V'; elim/last_ind: bs V' =>[|xs x Hi] V'; first done.
move: (btExtendV_fold1 V')=>V; move: (Hi V).
rewrite -cats1 foldl_cat /= {2}/btExtend; case: ifP.
case: ifP=>//=; by move: validH_undef.
move=>D H; rewrite/validH=>h b; rewrite findUnR ?validPtUn ?V ?D //=.
case: ifP; first by move: (H h b).
by rewrite findPt2; case: ifP=>//= /andP[/eqP ->] _ _ [] ->.
Qed.

Lemma btExtendIB bt b :
  validH bt -> valid (btExtend bt b) -> has_init_block bt ->
  has_init_block (btExtend bt b).
Proof.
move=>Vh V'; rewrite /btExtend/has_init_block=>Ib.
move: (btExtendV V')=>V; case: ifP=>X; last first.
by move: (find_some Ib)=>G; rewrite findUnR ?validPtUn ?X ?V //= G Ib.
case: ifP=>//=.
case: (um_eta X)=>v [F _].
rewrite F=>/eqP; move: (Vh _ _ F)=>H Neq.
contradict V'; rewrite/btExtend X; case: ifP.
by rewrite F=>/eqP [] E; subst v.
by rewrite valid_undef.
Qed.

Lemma btExtendIB_fold bt bs :
  validH bt -> valid (foldl btExtend bt bs) -> has_init_block bt ->
  has_init_block (foldl btExtend bt bs).
Proof.
move=>Vh V'; rewrite/has_init_block=>iB.
elim/last_ind: bs V'=>[|xs x Hi]; first done.
rewrite -cats1 foldl_cat /= {1}/btExtend; case: ifP.
- case: ifP; last by rewrite valid_undef.
  by move=>F D V; rewrite{1}/btExtend D F; apply Hi.
move=>Nd; rewrite validPtUn Nd /==>/andP[V _].
rewrite{1}/btExtend Nd findUnR ?validPtUn ?V ?Nd //=.
by move: (find_some (Hi V)) (Hi V)=>-> ->.
Qed.

Lemma in_ext bt b : valid (btExtend bt b) -> validH bt -> b ∈ btExtend bt b.
Proof.
move=>V' Vh; rewrite/btHasBlock/btExtend;
move: (btExtendV V')=>V; case: ifP=>//=; last first.
- rewrite domUn inE ?validPtUn ?V //==>D; rewrite D domPt inE/=.
  apply/andP; split.
  by apply/orP; left.
  by rewrite findUnL ?validPtUn ?V ?D //; rewrite domPt inE /=;
      case: ifP=>/eqP//= _; rewrite findPt /=.
move=>D; case: ifP.
by rewrite D=>/eqP ->; apply /andP; split=>//=.
case: (um_eta D)=>b' [] F' _; move: (Vh _ _ F')=>H F.
rewrite F' in F; contradict V'.
rewrite/btExtend D; case: ifP; last by rewrite valid_undef.
by rewrite F' F.
Qed.

Lemma btExtend_dom bt b :
  valid (btExtend bt b) -> {subset dom bt <= dom (btExtend bt b)}.
Proof.
move=>V' z; rewrite/btExtend; case:ifP=>C//=D.
case: ifP=>//= F.
by contradict V'; rewrite/btExtend C F valid_undef.
move: (btExtendV V')=>V.
by rewrite domUn inE andbC/= validPtUn/= V D/= C orbC.
Qed.

Lemma btExtend_dom_fold bt bs :
  valid (foldl btExtend bt bs) -> {subset dom bt <= dom (foldl btExtend bt bs)}.
Proof.
move=>V z; elim/last_ind: bs V=>[|xs x Hi]=>//.
move=>V'; move: (btExtendV_fold1 V')=>V D; specialize (Hi V D).
rewrite -cats1 foldl_cat /=; apply btExtend_dom=>//=.
by move: V'; rewrite -cats1 foldl_cat /=.
Qed.

Lemma btExtend_find bt z h b :
  valid (btExtend bt z) ->
  h \in dom bt ->
  find h (btExtend bt z) = Some b ->
  find h bt = Some b.
Proof.
move=>V' D; move: (btExtendV V')=>V.
rewrite/btExtend; case:ifP=>C.
case: ifP=>//=C'; first by rewrite find_undef.
rewrite findUnR ?validPtUn ?V ?C //; case: ifP=>//=.
by rewrite D.
Qed.

Lemma btExtend_find_fold bt h b bs :
  valid (foldl btExtend bt bs) ->
  h \in dom bt ->
  find h (foldl btExtend bt bs) = Some b ->
  find h bt = Some b.
Proof.
move=>V' D.
elim/last_ind: bs V'=>[|xs x Hi]=>//.
move=>V'; move: (btExtendV_fold1 V')=>V; move: V'.
rewrite -cats1 foldl_cat /= =>X.
specialize (Hi V); rewrite{1}/btExtend.
case: ifP.
case: ifP; last by rewrite find_undef.
by move=>_ _ ; apply Hi.
move=>Nd; rewrite findUnR ?validPtUn ?Nd ?V //.
case: ifP; first by move=>_; apply Hi.
move=>Nd'; rewrite findPt2 //=; case: ifP=>//=.
by move: (btExtend_dom_fold V D); rewrite Nd'.
Qed.

Lemma btExtend_in_either bt b b' :
  valid (btExtend bt b) ->  b ∈ btExtend bt b' -> b ∈ bt \/ b == b'.
Proof.
move=>V'; rewrite /btExtend/=;
move: (btExtendV V')=>V; case: ifP=>//= N.
case: ifP=>//=; first by left.
by rewrite/btHasBlock=>_/andP[]; rewrite dom_undef.
rewrite/btHasBlock domUn inE domPtK validPtUn V N.
move/andP=>[] /orP; case; last first.
move=>D /eqP; rewrite findUnL ?validPtUn ?V ?N //; case: ifP.
by rewrite domPtK inE=>/eqP hE; contradict D; rewrite hE N.
by move=>_ ->; rewrite D //=; left.
- rewrite inE=>/eqP ->; rewrite findUnL ?validPtUn ?V ?N //; case: ifP.
  by move=>_ /eqP F; move: (findPt_inv F); case=>_ ->; right.
  by move=>_ /eqP F; contradict N; move: (find_some F)=>->.
Qed.

Lemma btExtend_fold_in_either bt xs b :
  valid (foldl btExtend bt xs) -> b ∈ (foldl btExtend bt xs) ->
  b ∈ bt \/ b \in xs.
Proof.
elim/last_ind: xs=>[|xs x H]; first by left.
move=>V'; move: (btExtendV_fold1 V')=>V; specialize (H V).
rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last first.
- move=>D; rewrite/btHasBlock=>/andP [].
  rewrite domPtUn inE=>/andP[]Z/orP; case.
  * move/eqP=>Hh; rewrite Hh findPtUn; last by rewrite -Hh.
    move/eqP=>[]E; subst x; right.
    by rewrite mem_cat inE eq_refl Bool.orb_true_r.
  move=>A; rewrite findPtUn2 ?Z //=; case: ifP.
  by move=>_ /eqP[]->; right; rewrite mem_cat inE eq_refl Bool.orb_true_r.
  move=>_ B; have X: (b ∈ foldl btExtend bt xs) by rewrite/btHasBlock A B.
  move: (H X); case; first by rewrite/btHasBlock=>->; left.
  by move=>M; right; rewrite mem_cat M Bool.orb_true_l.
case: ifP.
move=>_ _ M; case: (H M); first by left.
by move=>X; right; rewrite mem_cat X Bool.orb_true_l.
by move=> _ _; rewrite/btHasBlock dom_undef in_nil Bool.andb_false_l.
Qed.

Lemma btExtend_fold_in bt xs b :
  valid (foldl btExtend bt xs) -> b ∈ bt \/ b \in xs ->
  b ∈ (foldl btExtend bt xs).
Proof.
elim/last_ind: xs=>[|xs x H]; first by move=>_; case=>//=.
move=>V'; move: (btExtendV_fold1 V')=>V; specialize (H V).
rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last first.
- move=>D; case.
  * move=>Hv; have X: (b ∈ bt \/ b \in xs) by left.
    move: (H X); rewrite/btHasBlock=>/andP[] A B;
    rewrite domPtUn inE validPtUn V D A Bool.orb_true_r //=;
    (rewrite findPtUn2; last by rewrite validPtUn V D);
    case: ifP=>//=; by move/eqP=>E; move: D A; rewrite E=>->.

  * rewrite mem_cat inE=>/orP; case=>Hv.
    have X: (b ∈ bt \/ b \in xs) by right.
    move: (H X); rewrite/btHasBlock=>/andP[] A B;
    rewrite domPtUn inE validPtUn V D A Bool.orb_true_r //=;
    (rewrite findPtUn2; last by rewrite validPtUn V D);
    case: ifP=>//=; by move/eqP=>E; move: D A; rewrite E=>->.

  * by move/eqP in Hv; rewrite/btHasBlock domPtUn Hv inE eq_refl D;
    rewrite validPtUn V D findPtUn ?validPtUn ?V ?D //=.
case:ifP.
* move=>F D; case=>Hv.
  by (have X: (b ∈ bt \/ b \in xs) by left); move: (H X).
  move: Hv; rewrite mem_cat inE=>/orP; case=>Hv.
  by (have X: (b ∈ bt \/ b \in xs) by right); move: (H X).
  by move/eqP in Hv; subst x; rewrite/btHasBlock D F.
move=>F D; contradict V'.
by rewrite -cats1 foldl_cat //= {1}/btExtend D F valid_undef.
Qed.

Lemma btExtend_idemp bt b :
  valid (btExtend bt b) -> btExtend bt b = btExtend (btExtend bt b) b.
Proof.
move=>V'; move: (btExtendV V')=>V; rewrite{2}/btExtend; case: ifP.
case: ifP=>//=.
move=>X; rewrite{1}/btExtend; case: ifP=>D.
case: ifP=>F; last by rewrite dom_undef.
by move=>_; contradict X; rewrite/btExtend D F F.
by contradict X; rewrite/btExtend D; rewrite findPtUn ?validPtUn ?V ?D //= eq_refl.
move=>X; contradict X.
rewrite/btExtend; case: ifP=>D.
case: ifP=>F; first by rewrite D.
by contradict V'; rewrite/btExtend D F valid_undef.
by rewrite domPtUn inE validPtUn V D //= eq_refl.
Qed.

(* Just a reformulation *)
Lemma btExtend_preserve (bt : BlockTree) (ob b : block) :
  valid (btExtend bt b) ->
  ob ∈ bt -> ob ∈ btExtend bt b.
Proof.
move=>V'; move: (btExtendV V')=>V; rewrite/btHasBlock=>/andP [H0 H1].
rewrite/btExtend; case: ifP=>D.
- case: ifP=>F.
  by rewrite H0 H1.
  by contradict V'; rewrite/btExtend D F valid_undef.
have Vu: (valid (# b \\-> b \+ bt)) by rewrite validPtUn V D.
rewrite findUnR // H0 H1 domUn inE Vu H0 /=.
by apply/andP; split=>//=; apply/orP; right.
Qed.

Lemma btExtend_withDup_noEffect (bt : BlockTree) (b : block):
  b ∈ bt -> bt = (btExtend bt b).
Proof. by rewrite/btHasBlock/btExtend=>/andP[]->->. Qed.

(* There must be a better way to prove this. *)
Lemma btExtend_comm bt b1 b2 :
  valid (btExtend (btExtend bt b1) b2) ->
  btExtend (btExtend bt b1) b2 = btExtend (btExtend bt b2) b1.
Proof.
move=>V2; move: (btExtendV V2)=>V1; move: (btExtendV V1)=>V0.
have V1': valid (btExtend bt b2).
rewrite/btExtend; case: ifP.
- case: ifP=>//= F D.
  contradict V2; rewrite{2}/btExtend; case: ifP.
  case: ifP=>_ _; rewrite/btExtend.
    by rewrite D F valid_undef.
    by rewrite dom_undef validPtUn //= dom_undef valid_undef //=.
  move=>Nd;
  by rewrite/btExtend domPtUn validPtUn inE Nd V0 D Bool.orb_true_r //=;
     rewrite findUnR ?validPtUn ?V0 ?Nd //= D F valid_undef.
by move=>Nd; rewrite validPtUn V0 Nd.
(* Now have V1' *)
case A: (b1 ∈ bt).
- move/andP: A=>[A0 A1].
  rewrite ![btExtend _ b1]/btExtend A0 A1 (btExtend_dom V1' A0).
  case: ifP=>//=; rewrite{1}/btExtend; case: ifP.
  case: ifP; first by rewrite A1.
  by move=>F D; contradict V1'; rewrite/btExtend D F valid_undef.
  by move=>Nd; move: V1'; rewrite{1}/btExtend Nd=>V;
     rewrite findUnR ?V1' //= A0 A1.
case B: (b2 ∈ bt).
- move/andP: B=>[B0 B1].
  rewrite ![btExtend _ b2]/btExtend B0 (btExtend_dom V1 B0).
  case: ifP; first by rewrite B1.
  rewrite{1}/btExtend; move/nandP: A=>[A0|A1].
  case: ifP; first by move=>D; rewrite D in A0.
    by clear A0; move=>A0; rewrite findUnR ?validPtUn ?V0 ?A0 //= B0 B1.
  rewrite B1; case: ifP.
  case: ifP; first by move/eqP=>F; rewrite F in A1; move/eqP: A1.
    by clear A1; move=>A1 A0 _; rewrite/btExtend A0 A1.
   by move=>Nd; rewrite findUnR ?validPtUn ?V0 ?A0 ?Nd //= B0 B1.
move/nandP: A=>[A0|A1]; move/nandP: B=>[B0|B1].
- have VPt1: (forall a, valid (# b1 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 A0.
  apply Bool.negb_true_iff in A0; apply Bool.negb_true_iff in B0.
  rewrite/btExtend A0 B0; case: ifP.
  + rewrite domPtUn VPt1 inE B0 //= =>/orP [] //==>/eqP H.
    rewrite -H findUnR //= A0 domPtUn inE eq_refl VPt1 A0 findUnR //= A0 !findPt /=.
    case: ifP; rewrite eq_sym=>/eqP; case: ifP=>/eqP=>//=.
    by case=>->.
  have VPt2: (forall a, valid (# b2 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 B0.
  move=>X; have H: ((# b1 == # b2) = false)
   by move: X; rewrite domPtUn inE VPt1 B0 //==>/norP [/eqP H _]; apply/eqP.
  rewrite findUnR //= A0 domPtUn inE VPt2 A0 findPt2 eq_sym H //=.
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
- have VPt1: (forall a, valid (# b1 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 A0.
  apply Bool.negb_true_iff in A0;
  rewrite/btExtend A0.
  rewrite domPtUn VPt1 inE //=; case: ifP.
  + move=>/orP [].
    by move/eqP=>H; rewrite -H findUnR //= A0 findPt domUn VPt1 !inE domPt A0 inE eq_refl //=;
       rewrite findUnR //= A0 findPt //= eq_sym; case: ifP=>//= /eqP[]->.
    move=>D; rewrite findUnR //= D; case: ifP.
      by move/eqP=>E; rewrite E in B1; move/eqP: B1.
      by rewrite dom_undef //= join_undefR.
  move/norP=>[Nh Nd]; case: ifP; case: ifP.
  case: ifP; do? by move=>_ D; rewrite D in Nd.
  by rewrite domPtUn inE A0=>Nd' /andP [] VPt2 /orP []=>//=;
     move/eqP=>H; rewrite H in Nh; move/eqP: Nh.
  by move=>D; rewrite D in Nd.
  move=>_ _;
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
- have VPt2: (forall a, valid (# b2 \\-> a \+ bt)). by move=>a; rewrite validPtUn V0 B0.
  apply Bool.negb_true_iff in B0.
  rewrite/btExtend B0 domPtUn VPt2 inE //=.
  case: ifP; case: ifP; case: ifP;
  do? by [
    move/eqP=>A; rewrite A in A1; move/eqP: A1 |
    rewrite dom_undef
  ]. case: ifP.
  move=>/orP [] //= /eqP H; rewrite H findUnL; last by rewrite -H; apply VPt2.
  rewrite domPt inE eq_refl //= findUnR; last by rewrite -H; apply VPt2.
  move=>F ->; rewrite findPt //=; case: ifP=>/eqP; first by case=>E; subst b2.
  by move: F; rewrite findPt //= eq_sym=>/eqP.
  by move/norP=>[]Nh _ F Nd;
     rewrite domPtUn inE B0 //==>/andP [] _ /orP[]=>//= /eqP H;
     rewrite H in Nh; move/eqP: Nh.
  move=>X Y; rewrite domPtUn inE B0=>/andP [] _ /orP []=>//=/eqP H.
  rewrite -H eq_refl //= findUnL; last by rewrite H; apply VPt2.
  rewrite domPt inE eq_refl //= findPt //=; case: ifP=>//=.
  move/eqP=>[E]; subst b2; contradict X.
  by rewrite findUnR ?validPtUn ?V0 ?B0 //= findPt //==>/eqP.
  move=>_ D; rewrite findUnR ?VPt2 //= D -(Bool.if_negb _ (find (# b1) bt == Some b1) _) A1.
  case: ifP=>_ _; first by rewrite join_undefR.
  have X: (# b1 \\-> b1 \+ bt = um_undef) by
    apply invalidE; rewrite validPtUn V0 D.
  by rewrite joinA (joinC (#b1 \\-> _)) -X joinA.
  by move/orP=>[] //= /eqP H; rewrite H=>D; rewrite H in VPt2;
     rewrite domPtUn inE D eq_refl VPt2.
  by rewrite (joinC (#b1 \\-> _)) (joinC (#b2 \\-> _));
    rewrite (joinC (#b2 \\-> _)) joinA (joinC bt).
(* Nastiest case - 16 subcases to be handled one-by-one *)
rewrite/btExtend; case: ifP; case: ifP; case: ifP; case: ifP.
by move/eqP=>B; rewrite B in B1; move/eqP: B1.
by move=>_ /eqP A; rewrite A in A1; move/eqP: A1.
by rewrite dom_undef.
by rewrite dom_undef.
case: ifP; case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  move=>_ D; rewrite domPtUn inE=>/andP[] _ /orP[].
  by move/eqP=>H F Nd; move: F; rewrite H findUnL ?validPtUn ?V0 ?Nd //=;
    rewrite domPt inE eq_refl findPt //==>/eqP[]->.
  by move=>->.
  move=>Nf Nd2 _ F Nd1. rewrite domPtUn inE Nd2 //==>/andP[]_ /orP[]=>//= /eqP H.
  move: F; rewrite -H findUnL ?validPtUn ?V0 ?Nd1 //= domPt inE eq_refl //= findPt //=.
  move/eqP=>[]E; subst b2; contradict Nf.
  by rewrite findUnL ?validPtUn ?V0 ?Nd1 //= domPt inE eq_refl //= findPt //==>/eqP [].
case: ifP.
  case: ifP=>//=.
  move=>_ D; contradict V1';
  rewrite/btExtend D; case: ifP=>/eqP E;
    by [rewrite E in B1; move/eqP: B1|rewrite valid_undef].
  move=>D A F B; rewrite domPtUn inE D=>/andP []_/orP[] //= /eqP H; rewrite H.
  by contradict A; rewrite domPtUn inE eq_sym H eq_refl D validPtUn V0 D.
case: ifP; case: ifP=>//=.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  move=>F D _ Nf D'; move: F Nf; rewrite !findUnL ?validPtUn ?V0 ?D ?D' //=.
  rewrite !domPt !inE //= inE (eq_sym (#b2)); case: ifP.
  by move/eqP=>->; rewrite !findPt //==>/eqP []-> /eqP.
  by move=>_ /eqP F; move: (find_some F)=>Nd'; rewrite Nd' in D'.
case: ifP.
  case: ifP; first by move/eqP=> B; move/eqP: B1; rewrite B.
  by rewrite join_undefR.
  move=>D _ _ _. rewrite domUn inE D domPt //= inE=>/andP []_/orP[]//=.
  by move/eqP=><-; rewrite joinA pts_undef join_undefL.
by move=>_/eqP A; rewrite A in A1; move/eqP: A1.
by move=>_/eqP A; rewrite A in A1; move/eqP: A1.
case: ifP; case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by rewrite dom_undef.
  by move=>F D' _ _ D; move: F; rewrite findUnR ?validPtUn ?V0 ?D' //= D;
     move/eqP=>A; rewrite A in A1; move/eqP: A1.
  by rewrite join_undefR.
case: ifP.
  case: ifP; last by rewrite !join_undefR.
  by move/eqP=> B; rewrite B in B1; move/eqP: B1.
  rewrite join_undefR=>_ _ _ D _; rewrite joinA (joinC (#b1 \\-> _)).
  suff: ~~ valid(#b1 \\-> b1 \+ bt) by move/invalidE; rewrite -joinA=>->; rewrite join_undefR.
  by rewrite validPtUn V0 D.
by case: ifP; [move=>_ _ -> | rewrite dom_undef].
rewrite domPtUn inE=>_ /andP[]_/orP []; last by move=>->.
  by move/eqP=>-> D; rewrite domPtUn inE eq_refl //= validPtUn V0 D.
case: ifP.
  by move/eqP=>B; rewrite B in B1; move/eqP: B1.
  by move=>_D D' _; rewrite domPtUn validPtUn V0 inE D' //==>-> //= /norP[].
by move=>_ _ _ _; rewrite !joinA (joinC (#b2 \\-> _)).
Qed.

Definition no_collisions (bt : BlockTree) (xs : seq block) :=
  valid bt /\
  forall a, a \in xs ->
    (forall b, b \in xs -> # a = # b -> a = b) /\
    (forall b, b ∈ bt -> # a = # b -> a = b).

Lemma btExtendV_valid_no_collisions bt xs :
  valid (foldl btExtend bt xs) -> no_collisions bt xs.
Proof.
elim/last_ind: xs=>[|xs x H0] //=.
- move=>V; move: (btExtendV_fold1 V)=>V1; specialize (H0 V1).
  move: H0; rewrite/no_collisions.
  move=>[] V0 N; split=>//=.
  move=>a; rewrite -cats1 mem_cat inE=>/orP; case; last first.
  * move/eqP=>E; subst a; split.
    move=>b; rewrite mem_cat inE=>/orP; case; last first.
    by rewrite eq_sym=>/eqP.
    by apply (btExtendV_fold_dup V).
    move=>b; rewrite/btHasBlock=>/andP[D F] Hh.
    move: V; rewrite -cats1 foldl_cat //= {1}/btExtend.
    move: (btExtend_dom_fold V1 D)=>D'; rewrite Hh D'.
    case: ifP; last by rewrite valid_undef.
    move=>F' _; move/eqP in F'.
    by move: (btExtend_find_fold V1 D F'); move/eqP: F=>-> []->.
  move=>X; specialize (N a X); case: N=>N0 N1; split=>b; last by apply N1.
  rewrite mem_cat inE=>/orP; case; first by apply N0.
  move/eqP=>E; subst b=>/eqP Hh; rewrite eq_sym in Hh; move/eqP in Hh.
  by move: (btExtendV_fold_dup V X Hh)=>->.
Qed.

Lemma btExtendV_no_collisions_valid bt xs :
  validH bt -> no_collisions bt xs -> valid (foldl btExtend bt xs).
Proof.
elim/last_ind: xs=>[|xs x H1] //=.
by rewrite/no_collisions=>_; case.
rewrite/no_collisions=>Vh; case=>V N.
have N0: no_collisions bt xs.
rewrite/no_collisions; split=>//=.
  move=>a X; have X0: a \in rcons xs x
    by rewrite mem_rcons inE X Bool.orb_true_r.
  specialize (N a X0); move: N=>[]N0 N1; split=>b; last by apply N1.
  move=>X1; have X2: b \in rcons xs x.
    by rewrite mem_rcons inE X1 Bool.orb_true_r.
  by apply N0.
specialize (H1 Vh N0); rewrite -cats1 foldl_cat //= {1}/btExtend.
case: ifP; last by move=>D; rewrite validPtUn H1 D.
case: ifP=>//= F D; contradict H1.
(* Hmm *)
have X: (x \in rcons xs x) by rewrite mem_rcons mem_head.
specialize (N x X); move: N0=>N'; case: N=>N0 N1.
move: (um_eta D)=>[b] [F'] zz; rewrite F' in F.
specialize (N0 b); specialize (N1 b).
move: (btExtendH_fold Vh (dom_valid D) F')=>Hh.
rewrite Hh in D F'; have H: b ∈ (foldl btExtend bt xs).
  by rewrite/btHasBlock D F' eq_refl.
case Z: (x == b); first by move/eqP: Z F=>->; rewrite eq_refl.
case: (btExtend_fold_in_either (dom_valid D) H).
by move=>Q; move: (N1 Q Hh) Z=>->; rewrite eq_refl.
move=>R; have Q: (b \in rcons xs x)
  by rewrite -cats1 mem_cat inE R Bool.orb_true_l.
by move: (N0 Q Hh) Z=>->; rewrite eq_refl.
Qed.

Lemma btExtendV_fold_comm' bt xs ys :
  validH bt ->
  valid (foldl btExtend (foldl btExtend bt xs) ys) ->
  valid (foldl btExtend (foldl btExtend bt ys) xs).
Proof.
move=>Vh.
elim/last_ind: ys=>[|ys y V1]//= V.
move: (btExtendV_fold1 V)=>V0; specialize (V1 V0).
rewrite -foldl_cat; apply btExtendV_no_collisions_valid=>//=.
rewrite/no_collisions; split.
have X: (xs = [::] ++ xs) by [].
by move: V0; rewrite -foldl_cat X; move/btExtendV_fold/btExtendV_fold.
move: V; rewrite -foldl_cat; move/btExtendV_valid_no_collisions.
rewrite/no_collisions; case=>V H.
move=>a; rewrite mem_cat Bool.orb_comm=>X.
specialize (H a); rewrite mem_cat in H; specialize (H X).
case: H=>H0 H1; split=>//=.
move=>b; rewrite mem_cat Bool.orb_comm -mem_cat; apply H0.
Qed.

Lemma btExtendV_fold_comm bt xs ys :
  validH bt ->
  valid (foldl btExtend (foldl btExtend bt xs) ys) =
  valid (foldl btExtend (foldl btExtend bt ys) xs).
Proof.
move=>Vh.
have T: true by [].
have X: forall (a b : bool), a <-> b -> a = b.
by move=>a b []; case: a; case: b=>//= A B;
   [specialize (A T) | specialize (B T)].
by apply X; split; apply btExtendV_fold_comm'.
Qed.

Lemma btExtendV_fold' bt xs ys :
  validH bt-> valid (foldl btExtend bt (xs ++ ys)) -> valid (foldl btExtend bt ys).
Proof. by move=>Vh; rewrite foldl_cat btExtendV_fold_comm //= -foldl_cat=>/btExtendV_fold. Qed.

Section BlockTreeProperties.

(* b is the previous of b' in bt:
.... b <-- b' ....
*)
Definition next_of (bt : BlockTree) b : pred Block :=
  [pred b' | (hashB b == prevBlockHash b') && (hashB b' \in dom bt)].

(* All paths/chains should start with the GenesisBlock *)
Fixpoint compute_chain' (bt : BlockTree) b remaining n : Blockchain :=
  (* Preventing cycles in chains *)
  if (# b) \in remaining
  then
    (* Protect against possibility of hash-collision in b *)
    if b ∈ bt then
        let rest := seq.rem (hashB b) remaining in
        (* Supporting primitive inductions *)
        if n is n'.+1 then
            match find (prevBlockHash b) bt with
            (* No parent *)
            | None => [:: b]
            | Some prev =>
                (* Stop at GenesisBlock *)
                if b == GenesisBlock then [:: b] else
                (* Build chain prefix recursively *)
                rcons (nosimpl (compute_chain' (free (# b) bt) prev rest n')) b
            end
        else [::]
      else [::]
  else [::].

(* Compute chain from the block *)
Definition compute_chain bt b :=
  compute_chain' bt b (dom bt) (size (dom bt)).

(* Total get_block function *)
Definition get_block (bt : BlockTree) k : Block :=
  if find k bt is Some b then b else GenesisBlock.

(* Collect all blocks *)
Definition all_blocks (bt : BlockTree) := [seq get_block bt k | k <- dom bt].

Definition is_block_in (bt : BlockTree) b := exists k, find k bt = Some b.

(* A certificate for all_blocks *)
Lemma all_blocksP bt b : reflect (is_block_in bt b) (b \in all_blocks bt).
Proof.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  by exists k; rewrite /get_block E.
case=>k F; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists k; last by rewrite /get_block F.
by move/find_some: F.
Qed.

Lemma all_blocksP' bt b : validH bt -> reflect (b ∈ bt) (b \in all_blocks bt).
Proof.
move=>Vh.
case B : (b \in all_blocks bt); [constructor 1|constructor 2].
- move: B; rewrite /all_blocks; case/mapP=>k Ik->{b}.
  move/um_eta: Ik=>[b]/=[E H].
  rewrite/get_block E /btHasBlock; specialize (Vh _ _ E); subst k.
  by move: (find_some E)=>->; rewrite E eq_refl.
case=>H; rewrite/btHasBlock; move/negP: B=>B; apply: B.
rewrite /all_blocks; apply/mapP.
exists (#b) => //.
move/andP: H=>[H1 H2]=>//=.
rewrite/btHasBlock in H; rewrite/get_block.
case X: (find _ _)=>[b'|].
by case/andP: H; rewrite X eq_sym=>_ /eqP; case.
move/andP: H=>[H1 H2]; rewrite X in H2.
by contradict H2.
Qed.

(* All chains from the given tree *)
Definition good_chain (bc : Blockchain) :=
  if bc is h :: _ then h == GenesisBlock else false.

Fixpoint hash_chain' (b : block) (bc : Blockchain) :=
  match bc with
  | [::] => true
  | b' :: bc' => (prevBlockHash b' == # b) && (hash_chain' b' bc')
  end.

Fixpoint hash_chain (bc : Blockchain) :=
  match bc with
  | [::] => true
  | [:: b] => true
  | b :: bc' => hash_chain' b bc'
  end.

(* This one is not needed for hash_chain_rcons *)
Lemma hash_chain_last bc b :
  hash_chain (rcons bc b) ->
  bc = [::] \/ prevBlockHash b = # (last GenesisBlock bc).
Proof.
case: bc=>[|h t]; first by left.
rewrite last_cons rcons_cons -cats1/=.
case: t=>/=[|c t/andP[/eqP E] H/=]; first by rewrite andbC/==>/eqP=>?; right.
right; clear E h.
elim: t c H=>//=[c|h t Hi c/andP[/eqP E H]]; first by rewrite andbC/==>/eqP.
by apply Hi.
Qed.

Lemma hash_chain_rcons bc b :
  prevBlockHash b = # (last GenesisBlock bc) ->
  hash_chain bc ->
  hash_chain (rcons bc b).
Proof.
case: bc=>[|h t]//. rewrite last_cons rcons_cons/= -cats1.
case: t=>//=[|c t E/andP[/eqP->]H]; first by move=>->; rewrite eqxx.
rewrite eqxx/=; clear h.
elim: t c H E=>//= [c _->|h t Hi c/andP[/eqP ->]H E]; rewrite eqxx//=.
by apply: Hi.
Qed.

Lemma hash_chain_behead b bc :
  hash_chain (b :: bc) ->
  hash_chain bc.
Proof. by case: bc=>//= a l /andP [P] ->; case: l. Qed.

Lemma hash_chain_behead' b b' bc :
  hash_chain ([:: b, b' & bc]) ->
  prevBlockHash b' = # b.
Proof.
case: bc=>//=; first by move/andP=>[] /eqP ->.
by move=>a l /and3P [] /eqP ->.
Qed.

Lemma hash_chain_uniq_hash_nocycle b bc :
  hash_chain (b :: bc) ->
  uniq (map hashB (b :: bc)) ->
  (forall c, c \in bc -> prevBlockHash c != # last GenesisBlock (b :: bc)).
Proof.
elim: bc b=>//h t Hi.
specialize (Hi h); move=>b.
move=>Hc; move: (hash_chain_behead Hc)=>Hc'.
specialize (Hi Hc').
rewrite -cat1s map_cat cat_uniq=>/and3P [] _ X U'.
specialize (Hi U').
move=>c; rewrite in_cons=>/orP; case; last by apply Hi.
move/eqP=>Z; subst c.
move: (hash_chain_behead' Hc)=>H; rewrite H.
case C: (# b != # last GenesisBlock ([:: b] ++ h :: t))=>//=.
(* X -> # b \notin (map hashB h::t) *)
have Y:  ([seq # i | i <- [:: b]] = [:: # b]) by [].
have Z: (has (mem [:: # b]) [seq # i | i <- h :: t] ==
        mem [seq # i | i <- h :: t] (# b)).
rewrite //= !in_cons (eq_sym (# h) _); case: (# b == # h)=>//=.
elim: [seq # i | i <- t]=>//=.
by move=>a l //= /eqP ->; rewrite !inE (eq_sym a _).

move/eqP in Z; rewrite Y Z inE in X; clear Y Z.
case C': (# b == # last h t); last by rewrite C' in C.
move/eqP in C'; rewrite C' in X.
(* X is a contradiction *)
move: X; rewrite map_f //=; apply mem_last.
Qed.

(* Transaction validity *)
Fixpoint valid_chain' (bc prefix : seq block) :=
  if bc is b :: bc'
  then [&& VAF (proof b) prefix (txs b) && all [pred t | txValid t prefix] (txs b) & valid_chain' bc' (rcons prefix b)]
  else true.

Definition valid_chain bc := valid_chain' bc [::].

Definition all_chains bt := [seq compute_chain bt b | b <- all_blocks bt].

Definition good_chains bt := [seq c <- all_chains bt | good_chain c && valid_chain c].

(* Get the blockchain *)
Definition take_better_bc bc2 bc1 :=
  if (good_chain bc2 && valid_chain bc2) && (bc2 > bc1) then bc2 else bc1.

Definition btChain bt : Blockchain :=
  foldr take_better_bc [:: GenesisBlock] (all_chains bt).

End BlockTreeProperties.


(**********************************************************)

Section BtChainProperties.

Lemma btExtend_blocks (bt : BlockTree) (b : block) : valid (btExtend bt b) ->
  {subset all_blocks bt <= all_blocks (btExtend bt b)}.
Proof.
move=>V z/all_blocksP=>[[k]F]; apply/all_blocksP.
exists k; rewrite/btExtend; case:ifP=>// N.
case: ifP=>//=.
by move=>Nf; contradict V; rewrite/btExtend N Nf valid_undef.
rewrite findUnR.
by move/find_some: (F)=>->.
by rewrite validPtUn N //=; move: V; rewrite/btExtend N validPtUn N.
Qed.

Lemma compute_chain_no_block bt (pb : block) (hs : seq Hash) n :
  pb ∉ bt -> compute_chain' bt pb hs n = [::].
Proof.
move=>Nb; case: n=>//=[|?].
by case: ifP=>//=; case: ifP.
case: ifP=>//=; case: ifP=>//=.
move: Nb; rewrite/btHasBlock=>/nandP; case.
by move=>H/andP[H1 H2]; rewrite H1 in H.
by move=>H/andP[H1 [/eqP H2]]; rewrite H2 in H; move/eqP: H.
Qed.

Lemma compute_chain_no_block' bt (pb : block) (hs : seq Hash) n :
  # pb \notin hs -> compute_chain' bt pb hs n = [::].
Proof. by case: n=>//=[|?]; move/negbTE=>->. Qed.

Lemma size_free n h (bt : BlockTree):
  valid bt -> n.+1 = size (dom bt) ->
  h \in dom bt -> n = size (dom (free h bt)).
Proof.
move=>V S K.
case: (um_eta K)=>b[F]E; rewrite E in S V.
rewrite (size_domUn V) domPtK/= addnC addn1 in S.
by case: S.
Qed.

Lemma compute_chain_equiv  bt (pb : block) (hs1 hs2 : seq Hash) n :
  uniq hs1 -> uniq hs2 -> hs1 =i hs2 ->
  compute_chain' bt pb hs1 n = compute_chain' bt pb hs2 n.
Proof.
elim: n pb bt hs1 hs2=>//=[|n Hi] pb bt hs1 hs2 U1 U2 D; rewrite -D//.
case: ifP=>//G; case: (find (prevBlockHash pb) bt)=>[v|]=>//.
suff X: seq.rem (# pb) hs1 =i seq.rem (# pb) hs2.
- by rewrite (Hi v (free (# pb) bt) (seq.rem (# pb) hs1)
             (seq.rem (# pb) hs2) (rem_uniq _ U1) (rem_uniq _ U2) X).
by move=>z; rewrite (mem_rem_uniq _ U2) (mem_rem_uniq _ U1) !inE D.
Qed.

Lemma dom_rem1 (bt : BlockTree) h1 h2 a :
  valid (h1 \\-> a \+ bt) -> (h2 == h1) = false ->
  seq.rem h2 (dom (h1 \\-> a \+ bt)) =i dom (h1 \\-> a \+ free h2 bt).
Proof.
move=>V N z.
have X: h1 \\-> a \+ free h2 bt = free h2 (h1 \\-> a \+ bt)
  by rewrite freePtUn2// N.
rewrite X domF !inE.
case B: (z == h2).
- by move/eqP:B=>B; subst h2; rewrite rem_filter ?(dom_uniq _)// mem_filter/= eqxx.
move/negbT: (B)=>B'.
case C: (z \in dom (h1 \\-> a \+ bt)).
- by rewrite (rem_neq B' C) eq_sym; move/negbTE:B'=>->.
by rewrite eq_sym B; apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma dom_rem2 h (bt : BlockTree) : seq.rem h (dom bt) =i dom (free h bt).
Proof.
move=>z; case B: (z == h).
- move/eqP:B=>B; subst h.
  rewrite (rem_filter _ (@uniq_dom _ _ _ bt)) /predC1 mem_filter domF/=.
  by rewrite inE eqxx.
move/negbT: (B)=>B'; rewrite domF inE eq_sym B.
case C: (z \in dom bt); first by rewrite (rem_neq B' C).
by apply/negP=>/mem_rem=>E; rewrite E in C.
Qed.

Lemma compute_chain_notin_hash bt (b b' : block) (hs : seq Hash) n :
  valid bt -> (# b) \notin hs ->
  # b \notin (map hashB (compute_chain' bt b' hs n)).
Proof.
elim: n b b' bt hs=>[|n Hi] b b' bt hs V B/=; first by case: ifP=>//=; case: ifP.
case: ifP=>//B'; case:ifP=>//B0.
case D1: (prevBlockHash b' \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; rewrite inE; apply/negbT/negP=>/eqP Z; move: Z B' B=>-> ->.
- move=>pb F; rewrite F; case: ifP=>//=.
  by move/eqP=> Z; subst b'=>_ _; rewrite inE;
     case X: (#b == # GenesisBlock)=>//=; move/eqP: X B' B=>-> ->.
move=>X _ _; rewrite map_rcons.
apply/negP; rewrite -cats1 mem_cat; apply/negP/orP; case.
have H1: valid (free (# b') bt) by rewrite validF.
have H2: (# b \notin (seq.rem (# b') hs)).
  by move: (in_seq_excl B' B); rewrite eq_sym=>Neq; apply rem_neq_notin.

by move=>In; move: In (Hi b pb (free (# b') bt) _ H1 H2) ->.
by rewrite inE=>/eqP Y; move: Y B' B=>-> ->.
Qed.

Lemma compute_chain_uniq_hash bt b :
  valid bt -> uniq (map hashB (compute_chain bt b)).
Proof.
move=>V; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt V hs Es En=>[|n Hi] b bt V hs Es En/=; first by case:ifP=>//=; case: ifP.
case: ifP=>//B; case: ifP=>//B0.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last by move=>-> _.
move=>pb->Eb _; case: ifP=>//; rewrite map_rcons rcons_uniq=>_.
apply/andP; split.
- apply compute_chain_notin_hash.
  by rewrite validF.
  have H1: (uniq hs) by rewrite Es uniq_dom.
  by rewrite mem_rem_uniq=>//=; rewrite inE; apply/nandP; left; apply/negP; move/eqP.
have H1: valid (free (# b) bt) by rewrite validF.
have H2: n = size (dom (free (# b) bt)).
  by apply: size_free=>//=; do? rewrite -Es.
move: (Hi pb _ H1 _ (erefl _) H2)=>U.
rewrite -(compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (uniq_dom _))
          (uniq_dom (free (# b) bt)) (dom_rem2 _ _)) in U.
by rewrite Es U.
Qed.

Lemma compute_chain_uniq bt b :
  valid bt -> uniq (compute_chain bt b).
Proof. by move=>V; apply: map_uniq; apply compute_chain_uniq_hash. Qed.

(* Every block in a blockchain is also in the BlockTree *)
(* See btChain_mem2; need has_init_block *)
Lemma block_in_chain bt b0 b :
  valid bt -> has_init_block bt ->
  b \in compute_chain bt b0 -> b ∈ bt.
Proof.
move=>V Ib; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b0 bt hs Es En V Ib=>[|n Hi] b0 bt hs Es En V Ib/=; first by case:ifP=>//=; case: ifP.
case: ifP=>//B; case: ifP=>//B0.
case D1: (prevBlockHash b0 \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; rewrite inE/==>/eqP Z; subst b0 hs.
  move=>pb->Eb _; case: ifP.
  by move/eqP=>Z; subst b0; rewrite inE=>/eqP ->.
rewrite mem_rcons; subst hs.
have H1: valid (free (# b0) bt) by rewrite validF.
have H3: n = size (dom (free (# b0) bt)) by apply: size_free=>//.
move: (Hi pb _ _ (erefl _) H3 H1)=>H H0.
rewrite inE=>/orP[]=>[/eqP Z|]; first by subst b0; rewrite /btHasBlock.
rewrite -(compute_chain_equiv (free (# b0) bt) pb n (rem_uniq _ (uniq_dom _))
         (uniq_dom (free (# b0) bt)) (dom_rem2 _ _)) in H.
move/H; rewrite/btHasBlock; rewrite domF !inE; case: ifP.
- move/eqP=><-.
  case X: (# b0 == # GenesisBlock).
  (* Lots of fiddling to not have to use hash injectivity *)
  + rewrite/btHasBlock in B0; move/andP: B0=>[_ C].
    move/eqP in X; rewrite X in C.
    rewrite/has_init_block in Ib.
    rewrite Ib in C; rewrite eq_sym in H0.
    have C': (GenesisBlock == b0) by [].
    by rewrite C' in H0.
  + have X': (# GenesisBlock != # b0) by rewrite eq_sym X. clear X.
    by move=>H'; move: (has_init_block_free Ib X')=>H2; specialize (H' H2).
rewrite/has_init_block findF; case: ifP; last first.
by move=>_ Neq H'; move/andP: (H' Ib)=>[->]//=; rewrite findF; case: ifP=>//=.
(* Again, the fiddling *)
move/eqP=>X; rewrite/btHasBlock in B0; move/andP: B0=>[_ C].
rewrite -X in C; rewrite/has_init_block in Ib.
rewrite Ib in C; case Eq: (GenesisBlock == b0).
by move/eqP in Eq; subst b0; move/eqP in H0.
have C': (GenesisBlock == b0) by [].
by rewrite C' in Eq.
Qed.

Lemma last_in_chain bt b :
  valid bt ->
  let bc := (compute_chain bt b) in
  bc == [::] \/ b \in bc.
Proof.
move=>V; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En V=>[|n Hi] b bt hs Es En V/=.
by left; case: ifP=>//=; case: ifP=>//=.

case: ifP=>B; last by left. case: ifP=>B0; last by left.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last first.
- by move=>->_; right; rewrite inE; apply/eqP.
move=>pb->Eb _; case: ifP.
by right; rewrite inE; apply/eqP.
by right; rewrite mem_rcons inE; apply/orP; left.
Qed.

Lemma btExtend_chain_prefix_ind bt a b n hs :
  valid (btExtend bt a) -> validH bt -> valid bt ->
  hs = dom bt -> n = size hs -> (# a \in dom bt) = false ->
  exists p : seq block,
    p ++ compute_chain' bt b hs n =
    compute_chain' (# a \\-> a \+ bt) b (dom (# a \\-> a \+ bt))
      (size (dom (# a \\-> a \+ bt))).
Proof.
move=>V0 Vh V Es En B.
rewrite size_domUn ?validPtUn ?V ?B// domPtK-!Es-En [_ + _] addnC addn1.
elim: n b bt V0 V Vh B hs Es En=>[|n Hi] b bt V0 V Vh B hs Es En.
- rewrite {1}/compute_chain'; move/esym/size0nil: En=>->.
  by move: (compute_chain' _ _ _ 1)=>c/=; exists c; rewrite cats0.
have V': valid (# a \\-> a \+ bt) by rewrite validPtUn V B.
rewrite {2}/compute_chain' -!/compute_chain'.
case: ifP=>Bb; last first.
- exists [::]; rewrite compute_chain_no_block'//.
  apply/negbT/negP=>I1; move/negP:Bb=>Bb; apply: Bb; subst hs.
  by rewrite domUn inE V' I1 orbC.
rewrite {1}/compute_chain' -!/compute_chain'.
case: ifP=>X; last first.
case: ifP; last by  exists [::].
- by eexists (match _ with | Some prev => if b == GenesisBlock then [:: b] else rcons _ b
                           | None => [:: b] end); rewrite cats0.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last first.
+ move=>-> _; rewrite findUnR ?validPtUn ?V ?B// D1.
  case D2: (prevBlockHash b \in dom (#a \\-> a));
  case: dom_find (D2)=>//; last first.
  move=>-> _; rewrite/btHasBlock findUnR ?validPtUn ?V ?B// Bb //=;
  case: ifP; first by move/andP=>[-> ->]; exists [::].
    move/nandP; case.
    * move=>Nd; case: ifP; case: ifP; do? by [move=>D; rewrite D in Nd|exists [::]].
      by move: X; rewrite Es=>->.
    by move: X; rewrite Es=>->; case: ifP=>//=; exists [::].
  move=>pb pbH; rewrite pbH; rewrite domPtK inE in D2; move/eqP:D2=>D2.
  have: (# pb = #a) by rewrite D2 in pbH; move: (findPt_inv pbH)=>[] _ -> _.
  move=>H; rewrite -H freePt2// D2; move/eqP: H; rewrite eq_sym=>H; rewrite H=> _ _.
  case: ifP; case: ifP; do? by [case: ifP=>//=; exists [::] | exists [::]];
    do? by rewrite Es in X; move/eqP in H; rewrite -H /btHasBlock Bb X //=;
       rewrite findUnR ?validPtUn ?V ?B// X=>->.
    by case: ifP; by [exists [::] | rewrite -cats1; eexists].
move=>pb Hf; rewrite updF Hf eqxx=>Eb _.
case: ifP; last first.
- case: ifP.
  by rewrite Es in X; rewrite/btHasBlock domPtUn V' X findUnR //= X=>/andP[_ /eqP -> /eqP].
  by exists [::].
case: ifP.
  case: ifP.
  by exists [::]=>//=; rewrite findUnR ?validPtUn ?V ?B// D1 Hf.
  by rewrite Es in X; rewrite/btHasBlock Bb X /= findUnR ?B// X=>->.
move=>bNg.
have Bn' : # b == # a = false by apply/negbTE/negP=>/eqP=>E;
           rewrite -E -Es X in B.
rewrite (freePtUn2 (#b) V') !Bn' !(Vh _ _ Hf).
subst hs.
rewrite findUnR ?validPtUn ?V ?B//; move: (Vh (prevBlockHash b) pb Hf)=><-; rewrite D1 Hf.
(* It's time to unleash the induction hypothesis! *)
have H0: valid (btExtend (free (# b) bt) a)
  by rewrite/btExtend domF inE B Bn' validPtUn validF V domF //= inE Bn' B.
have H1: valid (free (# b) bt) by rewrite validF.
have H2: validH (free (# b) bt) by apply validH_free.
have H3: (# a \in dom (free (# b) bt)) = false by rewrite domF inE Bn' B.
have H4: n = size (dom (free (# b) bt)) by apply: size_free.
case: (Hi pb (free (# b) bt) H0 H1 H2 H3 (dom (free (# b) bt)) (erefl _) H4)=>q E.
case: ifP; last by rewrite/btHasBlock Bb X findUnR ?B// X=>->.
move=>_ _.
exists q; rewrite -rcons_cat; congr (rcons _ b).
(* Final rewriting of with the unique lists *)
rewrite (compute_chain_equiv _ _ _ _ _ (dom_rem2 (#b) bt))
        ?(uniq_dom _) ?(rem_uniq _ (uniq_dom bt))// E.
by rewrite -(compute_chain_equiv _ _ _ _ _ (dom_rem1 V' Bn'))
           ?(uniq_dom _) ?(rem_uniq _ (uniq_dom _)).
Qed.

Lemma btExtend_chain_prefix bt a b :
  valid (btExtend bt a) -> validH bt ->
  exists p, p ++ (compute_chain bt b) = compute_chain (btExtend bt a) b .
Proof.
move=>V0 Vh; move: (btExtendV V0)=>V.
case B: (a ∈ bt); rewrite/btHasBlock in B.
by exists [::]; move/andP: B=>[B0 B1]; rewrite /btExtend B0 B1.
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.

move/nandP: B=>[B|B]; rewrite/btExtend.
- case: ifP; first by move=>X; rewrite X in B.
  clear B; move=>B.
  by apply btExtend_chain_prefix_ind.
case: ifP.
case: ifP; first by move/eqP=>B'; rewrite B' in B; move/eqP: B.
by clear B; move=>B D; contradict V0; rewrite/btExtend D B valid_undef.
move: B=>_ B.
by apply btExtend_chain_prefix_ind.
Qed.

Lemma compute_chain_gb_not_within' bt b:
  valid bt -> validH bt -> (* has_init_block bt -> *)
 [\/ compute_chain bt b = [::],
      b = GenesisBlock /\ compute_chain bt b = [:: b] |
      exists h t, compute_chain bt b = h :: t /\
              forall c, c \in t -> c != GenesisBlock].
Proof.
move=>V Vh; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
case D: ((# b) \in hs); last first.
- by elim: n En=>/=[|n Hi]; rewrite D; constructor.
elim: n b bt V Vh hs Es En D=>[|n Hi] b bt V Vh hs Es En D/=.
- by move/esym/size0nil: En=>Z; subst hs; rewrite Z in D.
(* Induction step *)
rewrite D; case: ifP; last by constructor 1. move=>Hb.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//;
last by move=>->_; constructor 3; exists b, [::].
+ move=>pb F; move: (Vh _ _ F)=>E _ _; rewrite F; rewrite !E in F D1 *.
have H1: valid (free (# b) bt) by rewrite validF.
have H2: validH (free (# b) bt) by apply: validH_free.
have H3: n = size (dom (free (# b) bt)) by apply: size_free=>//; rewrite -Es//.
have Uh: uniq hs by rewrite Es uniq_dom.
case G: (b == GenesisBlock); first by constructor 2; move/eqP in G.
constructor 3.
case Eh: (#pb == #b).
- exists b, [::]; split=>//.
  rewrite -cats1; suff: (compute_chain' (free (# b) bt) pb (seq.rem (# b) hs) n = [::]) by move=>->.
  clear Hi H3 En; elim: n=>/=; first by case: ifP=>//=; case: ifP=>//=.
  move=>n H; case: ifP=>//=; move/eqP in Eh; rewrite Eh.
  by rewrite mem_rem_uniq // inE=>/andP [] /eqP.
- have H4: # pb \in dom (free (# b) bt) by rewrite -dom_rem2 mem_rem_uniq // inE Eh.
  (* Can finally use the induction hypothesis *)
  case: (Hi pb _ H1 H2 _ (erefl _) H3 H4)=>//=;
  rewrite Es (compute_chain_equiv (free (# b) bt) pb n (rem_uniq _ (uniq_dom _))
                                  (uniq_dom (free (# b) bt)) (dom_rem2 _ _)).
  by move=>->; rewrite -cats1; exists b, [::].
  by case=>Eq; subst pb=>->; rewrite -cats1; exists GenesisBlock, [:: b]; split=>// c;
         rewrite inE=>/eqP ->; rewrite G.
  by move=>[h][t][Eq]Nc; exists h, (rcons t b); rewrite -rcons_cons Eq; split=>//;
     move=>c; rewrite -cats1 mem_cat=>/orP; case; [apply Nc|];
     rewrite inE=>/eqP ->; rewrite G.
Qed.

Lemma compute_chain_gb_not_within bt b:
  valid bt -> validH bt ->
  compute_chain bt b = [::] \/
  exists h t, compute_chain bt b = h :: t /\
         forall c, c \in t -> c != GenesisBlock.
Proof.
move=>V Vh.
case: (compute_chain_gb_not_within' b V Vh)=>H; [by left|right|by right].
by exists GenesisBlock, [::]; case: H=>[G C]; subst b.
Qed.

Lemma btExtend_compute_chain bt a b :
  valid (btExtend bt a) -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  (compute_chain (btExtend bt a) b) = compute_chain bt b.
Proof.
move=>V' Vh Ib G; move: (btExtendV V')=>V.
move: (@btExtendH _ a V Vh)=>Vh'.
Check btExtendIB.
move: (btExtendIB Vh V' Ib)=>Ib'.
case: (btExtend_chain_prefix b V' Vh)
      (compute_chain_gb_not_within b V' Vh')=>p <- H.
suff X: p = [::] by subst p.
case: H; first by elim: p=>//.
case=>h[t][E]H; case:p E=>//=x xs[]->{x}Z; subst t.
have X: GenesisBlock \in xs ++ compute_chain bt b.
- rewrite mem_cat orbC; rewrite /good_chain in G.
by case: (compute_chain bt b) G=>//??/eqP->; rewrite inE eqxx.
by move/H/eqP: X.
Qed.

(* Chains from blocks are only growing as BT is extended *)
Lemma btExtend_chain_grows bt a b :
  valid (btExtend bt a) -> validH bt ->
  compute_chain (btExtend bt a) b >= compute_chain bt b.
Proof.
move=>V' H; move: (btExtendV V')=>V; apply: FCR_subchain.
by case: (btExtend_chain_prefix b V' H)=>p<-; exists p, [::]; rewrite cats0.
Qed.

Lemma init_chain bt :
  has_init_block bt ->
  compute_chain bt GenesisBlock = [:: GenesisBlock].
Proof.
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n bt hs Es En=>[|n Hi] bt hs Es En Ib=>/=;
subst hs; move/find_some: (Ib).
- by move/esym/size0nil:En=>->.
move=>->; case: ifP.
by case (find (prevBlockHash GenesisBlock) bt)=>// b; case: ifP=>// /eqP.
by move: Ib (find_some Ib); rewrite/has_init_block/btHasBlock=>-> ->; rewrite eq_refl.
Qed.

Lemma all_chains_init bt :
  has_init_block bt -> [:: GenesisBlock] \in all_chains bt.
Proof.
move=>H; rewrite /all_chains; apply/mapP.
exists GenesisBlock; last by rewrite (init_chain H).
by apply/mapP; exists (# GenesisBlock);
[by move/find_some: H|by rewrite /get_block H].
Qed.

(* Important lemma: btChain indeed delivers a chain in bt *)
Lemma btChain_in_bt bt :
  has_init_block bt ->
  btChain bt \in all_chains bt.
Proof.
rewrite /btChain=>H; move: (all_chains_init H)=>Ha.
move:(all_chains bt) Ha=>acs.
elim: acs=>//=bc rest Hi Ha.
case/orP: Ha=>G.
- move/eqP:G=>G; subst bc; rewrite /take_better_bc/=.
  case: ifP=>X; first by rewrite inE eqxx.
  rewrite -/take_better_bc; clear Hi X H.
  elim: rest=>//=; rewrite ?inE ?eqxx//.
  move=> bc rest Hi/=; rewrite {1}/take_better_bc.
  case:ifP=>_; first by rewrite !inE eqxx orbC.
  by rewrite !inE in Hi *; case/orP: Hi=>->//; rewrite ![_||true]orbC.
move/Hi: G=>{Hi}; rewrite inE.
move: (foldr take_better_bc [:: GenesisBlock] rest)=>l.
rewrite /take_better_bc/=.
case: ifP=>_; first by rewrite eqxx.
elim: rest=>//=; rewrite ?inE ?eqxx//.
move=> bc' rest Hi/=. rewrite inE=>/orP[].
- by move=>/eqP=>Z; subst bc'; rewrite eqxx orbC.
by case/Hi/orP=>->//; rewrite ![_||true]orbC.
Qed.

Lemma btChain_mem2 (bt : BlockTree) (b : block) :
  valid bt -> has_init_block bt ->
  b \in btChain bt -> b ∈ bt.
Proof.
move=>V H.
move: (btChain_in_bt H); move: (btChain bt)=>bc H2 H1.
case/mapP:H2=>b0 _ Z; subst bc.
Check block_in_chain.
by move: (block_in_chain V H H1).
Qed.

Lemma btChain_mem (bt : BlockTree) (b : block) :
  valid bt -> has_init_block bt ->
  b ∉ bt -> b \notin btChain bt.
Proof.
move=>V H.
by move/negP=>B; apply/negP=>G; apply: B; apply: (btChain_mem2 V H).
Qed.

Definition bc_fun bt := fun x =>
   [eta take_better_bc (([eta compute_chain bt] \o
   [eta get_block bt]) x)].

Lemma good_init bc :
  good_chain bc -> [:: GenesisBlock] > bc = false.
Proof.
rewrite /good_chain. case: bc=>//h t/eqP->.
by apply/FCR_dual; apply: FCR_subchain; exists [::], t.
Qed.

(* This is going to be used for proving X1 in btExtend_sameOrBetter *)
Lemma better_chains1 bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall h bc' bc,
    bc' >= bc ->
    valid_chain bc' /\ good_chain bc' ->
    valid_chain bc /\ good_chain bc ->
    f' h bc' >= f h bc.
Proof.
move=>V B Vh H/=h bc' bc Gt [T' Gb'] [T Gb]; rewrite /bc_fun/=.
have V': valid (btExtend bt b)
  by rewrite/btExtend/valid; case: ifP=>//= D;
     move: (validR V)=>V'; contradict V; rewrite validPtUn D V' //=.
set bc2 := compute_chain (# b \\-> b \+ bt) b.
case E: (#b == h).
- move/eqP:E=>Z; subst h.
  rewrite /get_block !findPtUn//.
  have X: find (# b) bt = None.
  + case: validUn V=>//_ _/(_ (# b)); rewrite domPtK inE eqxx.
    by move/(_ is_true_true); case : dom_find=>//.
  rewrite !X init_chain//; clear X; rewrite /take_better_bc/=.
  case: ifP=>[/andP[X1 X2]|X]/=; rewrite (good_init Gb) andbC//=.
  + by right; apply: (FCR_trans_eq2 X2).
(* Now check if h \in dom bt *)
case D: (h \in dom bt); last first.
- rewrite /get_block (findUnL _ V) domPtK inE.
  case: ifP; first by case/negP; move/eqP => H_eq; move/negP: E; rewrite H_eq.
  move => H_eq {H_eq}.
  case: dom_find D=>//->_{E h}.
  rewrite /take_better_bc/= !init_chain//; last first.
  + by move: (btExtendIB Vh V' H); rewrite/btExtend(negbTE B).
  by rewrite !(good_init Gb)!(good_init Gb') -(andbC false)/=.
case: dom_find D=>//c F _ _.
rewrite /get_block (findUnL _ V) domPtK inE.
case: ifP; first by case/negP; move/eqP => H_eq; move/negP: E; rewrite H_eq.
move => H_eq {H_eq}.
rewrite !F.
move: (Vh h _ F); move/find_some: F=>D ?{E bc2}; subst h.
have P : exists p, p ++ (compute_chain bt c) = compute_chain (# b \\-> b \+ bt) c.
- by move: (btExtend_chain_prefix c V' Vh); rewrite /btExtend(negbTE B).
case:P=>p E; rewrite /take_better_bc.
case G1: (good_chain (compute_chain bt c))=>/=; last first.
- case G2: (good_chain (compute_chain (# b \\-> b \+ bt) c))=>//=.
  by case: ifP=>///andP[_ X]; right; apply: (FCR_trans_eq2 X).
(* Now need a fact about goodness monotonicity *)
move: (btExtend_compute_chain V' Vh H G1).
rewrite /btExtend (negbTE B)=>->; rewrite G1/=.
case:ifP=>[/andP[X1' X1]|X1]; case: ifP=>[/andP[X2' X2]|X2]=>//; do?[by left].
- by right; apply: (FCR_trans_eq2 X1 Gt).
by rewrite X2'/= in X1; move/FCR_dual: X1.
Qed.

Lemma tx_valid_init : all [pred t | txValid t [::]] (txs GenesisBlock).
Proof.
elim: (txs GenesisBlock) => //= tx txs IH.
apply/andP; split => //.
exact: txValid_nil.
Qed.

Lemma valid_chain_init : valid_chain [:: GenesisBlock].
Proof.
rewrite /valid_chain/=; apply/andP; split => //.
apply/andP; split; last by apply tx_valid_init.
exact: VAF_init.
Qed.

Lemma good_chain_foldr bt bc ks :
  valid_chain bc -> good_chain bc ->
  valid_chain (foldr (bc_fun bt) bc ks) /\
  good_chain (foldr (bc_fun bt) bc ks).
Proof.
elim: ks=>//=x xs Hi T G; rewrite /bc_fun/take_better_bc/= in Hi *.
case: ifP=>[/andP[B1 B2]|B]; first by rewrite andbC in B1; move/andP: B1.
by apply: Hi.
Qed.

Lemma good_chain_foldr_init bt ks :
  valid_chain (foldr (bc_fun bt) [:: GenesisBlock] ks) /\
  good_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof.
move: (@good_chain_foldr bt [:: GenesisBlock] ks valid_chain_init)=>/=.
by rewrite eqxx=>/(_ is_true_true); case.
Qed.

Lemma good_foldr_init bt ks : good_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof. by case: (good_chain_foldr_init bt ks). Qed.

Lemma tx_valid_foldr_init bt ks : valid_chain (foldr (bc_fun bt) [:: GenesisBlock] ks).
Proof. by case: (good_chain_foldr_init bt ks). Qed.

Lemma better_chains_foldr bt b :
  valid (# b \\-> b \+ bt) ->
  # b \notin dom bt -> validH bt -> has_init_block bt ->
  let f := bc_fun bt in
  let f' := bc_fun (# b \\-> b \+ bt) in
  forall ks bc' bc,
    bc' >= bc ->
    valid_chain bc' /\ good_chain bc' ->
    valid_chain bc /\ good_chain bc ->
    foldr f' bc' ks >= foldr f bc ks.
Proof.
move=>V B Vh H f f'; elim=>//h hs Hi bc' bc Gt TG1 TG2 /=.
move: (Hi _ _ Gt TG1 TG2)=>{Hi}Hi.
case: TG1 TG2=>??[??].
by apply: better_chains1=>//; apply: good_chain_foldr=>//.
Qed.

(* Monotonicity of BT => Monotonicity of btChain *)
Lemma btExtend_sameOrBetter bt b :
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  btChain (btExtend bt b) >= btChain bt.
Proof.
rewrite /btChain.
case B : (#b \in dom bt).
  by rewrite /btExtend B; case: ifP; [left|rewrite valid_undef].
move=>V' Vh Ib; rewrite /all_chains/all_blocks -!seq.map_comp/=.
move: (btExtendV V')=>V0; have V: (valid (# b \\-> b \+ bt)) by rewrite validPtUn V0 B.
rewrite/btExtend B.
case: (dom_insert V)=>ks1[ks2][->->]; rewrite -![# b :: ks2]cat1s.
rewrite !foldr_map -/(bc_fun bt) -/(bc_fun (# b \\-> b \+ bt)) !foldr_cat.
set f := (bc_fun bt).
set f' := (bc_fun (# b \\-> b \+ bt)).
have X1: foldr f' [:: GenesisBlock] ks2 >= foldr f [:: GenesisBlock] ks2.
 - elim: ks2=>//=[|k ks Hi]; first by left.
   by apply: better_chains1 ; rewrite ?B; do? [apply: good_chain_foldr_init]=>//.
apply: better_chains_foldr=>//;
do? [apply good_chain_foldr_init=>//]; [by apply/negbT| |]; last first.
- apply: good_chain_foldr; rewrite ?good_foldr_init ?tx_valid_foldr_init//.
simpl; rewrite {1 3}/f'/bc_fun/=/take_better_bc/=.
case:ifP=>///andP[B1 B2]. right.
apply: (FCR_trans_eq2 B2).
by apply: better_chains_foldr=>//=; [by apply/negbT|by left | |]; do?[rewrite ?valid_chain_init ?eqxx//].
Qed.

Lemma btExtend_fold1_comm bt b bs:
  validH bt ->
  valid (btExtend (foldl btExtend bt bs) b) ->
  btExtend (foldl btExtend bt bs) b =
  foldl btExtend (btExtend bt b) bs.
Proof.
move=>Vh; elim/last_ind: bs=>[|xs x H]//=.
move=>V; have V0: valid (btExtend (foldl btExtend bt xs) b).
by move: V; rewrite -cats1 foldl_cat //= btExtendV_comm; move/btExtendV.
rewrite -cats1 !foldl_cat //= -H ?V0 //= btExtend_comm ?V0 //=.
by move: V; rewrite -cats1 foldl_cat //=.
Qed.

(* This should be true even without validH, but don't know how to prove. *)
Lemma btExtend_fold_comm (bt : BlockTree) (bs bs' : seq block) :
  validH bt ->
  foldl btExtend (foldl btExtend bt bs) bs' =
  foldl btExtend (foldl btExtend bt bs') bs.
Proof.
move=>Vh.
case V: (valid (foldl btExtend (foldl btExtend bt bs) bs')); last first.
- have V': ~~ valid (foldl btExtend (foldl btExtend bt bs') bs) = true.
    by rewrite btExtendV_fold_comm //= V.
  by move: V V'; rewrite -Bool.negb_true_iff;
     move/invalidE=>->; move/invalidE=>->.
have V': valid (foldl btExtend (foldl btExtend bt bs') bs) = true.
  by rewrite btExtendV_fold_comm //= V.
elim/last_ind: bs' V V'=>[|xs x Hi] V V'/=; first done.
rewrite -cats1 !foldl_cat Hi=>/=; last first.
  by move: (btExtendV_fold1 V); rewrite btExtendV_fold_comm.
  by move: (btExtendV_fold1 V).
(* Note that we don't even use the induction hypothesis! *)
apply btExtend_fold1_comm.
apply btExtendH_fold=>//=.
by move: V'; rewrite -foldl_cat; move/btExtendV_fold; move/btExtendV_fold1.
move: V'; rewrite -cats1 -foldl_cat -catA foldl_cat foldl_cat btExtendV_fold_comm //=.
apply btExtendH_fold=>//=.
by move: V; move/btExtendV_fold1; rewrite btExtendV_fold_comm ?Vh //=;
   rewrite -foldl_cat; move/btExtendV_fold.
Qed.

Lemma btExtend_fold_preserve (ob : block) bt bs:
    valid (foldl btExtend bt bs) -> ob ∈ bt ->
    ob ∈ foldl btExtend bt bs.
Proof.
elim/last_ind: bs=>[|xs x Hi]//.
rewrite -cats1 foldl_cat /=.
move=>V'; move: (btExtendV V').
move=>V H; specialize (Hi V H).
by apply btExtend_preserve.
Qed.

Lemma btExtend_fold_sameOrBetter bt bs:
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  btChain (foldl btExtend bt bs) >= btChain bt.
Proof.
elim/last_ind: bs=>[|xs x Hi]/=; first by left.
rewrite -cats1 foldl_cat /=.
move=>Vx; have: valid (btExtend (foldl btExtend bt xs) x) by [].
move/btExtendV=>V Vh Ib; specialize (Hi V Vh Ib).
have: (btChain (btExtend (foldl btExtend bt xs) x)
        >= btChain (foldl btExtend bt xs)).
  by apply btExtend_sameOrBetter; do? [apply btExtendH_fold | apply btExtendIB_fold].
move=>H; case: Hi; case: H.
by move=>->->; left.
by move=>H1 H2; rewrite H2 in H1; right.
by move=>->; right.
by move=>H1 H2; move: (FCR_trans H1 H2); right.
Qed.

(* monotonicity of (btChain (foldl btExtend bt bs)) wrt. bs *)
Lemma btExtend_monotone_btChain (bs ext : seq block) bt:
  valid (foldl btExtend bt (bs ++ ext)) ->
  validH bt -> has_init_block bt ->
  btChain (foldl btExtend bt (bs ++ ext)) >= btChain (foldl btExtend bt bs).
Proof.
elim/last_ind: ext=>[|xs x H]/=.
by rewrite foldl_cat; left.
move=>V'; have: valid (foldl btExtend bt (bs ++ rcons xs x)) by [].
rewrite foldl_cat; move/btExtendV_fold1=>V; rewrite -cats1.
move=>Vh Ib.
rewrite -foldl_cat in V; specialize (H V Vh Ib).
apply btExtend_fold_sameOrBetter.
by rewrite cats1 -foldl_cat.
by apply btExtendH_fold=>//; apply: (btExtendV_fold V).
apply btExtendIB_fold=>//; apply: (btExtendV_fold V).
Qed.

Lemma btExtend_not_worse (bt : BlockTree) (b : block) :
    valid (btExtend bt b) -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (btExtend bt b)).
Proof.
move=>V Vh Ib;
move: (btExtend_sameOrBetter V Vh Ib); case.
by move=>->; apply: (FCR_nrefl).
move=>H; case X: (btChain bt > btChain (btExtend bt b)); last done.
by move: (FCR_nrefl (FCR_trans H X)).
Qed.

Lemma btExtend_fold_not_worse (bt : BlockTree) (bs : seq block) :
    valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
    ~ (btChain bt > btChain (foldl btExtend bt bs)).
Proof.
move=>V Vh Ib; move: (btExtend_fold_sameOrBetter V Vh Ib); case.
by move=><-; apply: FCR_nrefl.
by apply: FCR_excl.
Qed.

Lemma btExtendV_within bt bs b :
  validH bt ->
  valid (foldl btExtend bt bs) ->
  b \in bs ->
  valid (btExtend bt b).
Proof.
move=>Vh V H; move: (in_seq H)=>[bf] [af] H0.
rewrite H0 in V; clear H0; elim: bf V=>[|x xs Hi]//=.
have E:
  valid (foldl btExtend (btExtend bt b) af) =
  valid (foldl btExtend (foldl btExtend bt [::b]) af) by [].
by rewrite E -foldl_cat=>B; move: (btExtendV_fold B).
rewrite -cat1s {2}/btExtend; case: ifP.
case: ifP.
by rewrite cat1s=>_ _ A; apply Hi.
by move=>_ _; move/btExtendV_fold; rewrite -(cat0s xs);
   move/btExtendV_fold; rewrite valid_undef.
move=>D.
have X: (# x \\-> x \+ bt = btExtend bt x) by rewrite/btExtend D.
have Y: (btExtend bt x) = foldl btExtend bt [:: x] by [].
rewrite X Y -(foldl_cat _ _ [:: x] _).
by move/btExtendV_fold'=>Z; move: (Z Vh); rewrite cat1s; apply Hi.
Qed.

Lemma btExtend_fold_within bt bs bf b af :
  validH bt ->
  valid (foldl btExtend bt bs) ->
  bs = bf ++ b::af ->
  foldl btExtend (btExtend bt b) (af ++ bf) =
  foldl btExtend bt bs.
Proof.
move=>Vh V E; subst bs; rewrite -cat1s catA.
move: (btExtendV_fold_xs V)=>V0.
rewrite (foldl_cat _ _ (bf ++ [::b]) _).
have X: foldl btExtend bt (bf ++ [:: b]) =
        foldl btExtend bt ([:: b] ++ bf).
by rewrite !foldl_cat; apply btExtend_fold_comm=>//=.
rewrite X !foldl_cat //=; apply btExtend_fold_comm.
by apply btExtendH.
Qed.

Lemma btExtend_seq_same_bt bt b bs:
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  b \in bs -> bt = foldl btExtend bt bs ->
  bt = btExtend bt b.
Proof.
move=>V Vh Ib H1.
move: (in_seq H1)=>[bf] [af] H2; rewrite H2.
move: (btExtendV_within Vh V H1)=>V'.
move: (btExtendV V')=>V0; move=>H;
rewrite -cat1s in H. rewrite H.
rewrite foldl_cat btExtend_fold_comm. rewrite foldl_cat /= - foldl_cat.
(have: validH (btExtend bt b) by apply btExtendH)=>Vh'.
(have: has_init_block (btExtend bt b) by apply btExtendIB)=>Ib'.
move: (btExtend_fold_within Vh V H2)=>Eq; rewrite Eq.
apply btExtend_withDup_noEffect.
apply btExtend_fold_in=>//=; by right.
done.
Qed.

Lemma btExtend_seq_same bt b bs:
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  b \in bs -> btChain bt = btChain (foldl btExtend bt bs) ->
  btChain bt = btChain (btExtend bt b).
Proof.
move=>V Vh Ib H1.
move: (in_seq H1)=>[bf] [af] H2; rewrite H2.
move: (btExtendV_within Vh V H1)=>V'.
move: (btExtendV V')=>V0.
move=>H;
move: (btExtend_sameOrBetter V' Vh Ib)=>H0.
case: H0; first by move/eqP; rewrite eq_sym=>/eqP.
rewrite -cat1s in H.
move=>/=Con; rewrite H in Con; clear H; contradict Con.
rewrite foldl_cat btExtend_fold_comm. rewrite foldl_cat /= - foldl_cat.
(have: validH (btExtend bt b) by apply btExtendH)=>Vh'.
(have: has_init_block (btExtend bt b) by apply btExtendIB)=>Ib'.
apply btExtend_fold_not_worse=>//=.
by move: (btExtend_fold_within Vh V H2)=>Eq; rewrite Eq.
done.
Qed.

Lemma btExtend_seq_sameOrBetter bt b bs:
    valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
    b \in bs -> btChain bt >= btChain (foldl btExtend bt bs) ->
    btChain bt >= btChain (btExtend bt b).
Proof.
move=>V Vh Ib H1; case.
by move=>H2; left; apply (btExtend_seq_same V Vh Ib H1 H2).
by move=>Con; contradict Con; apply btExtend_fold_not_worse.
Qed.

Lemma btExtend_seq_sameOrBetter_fref :
  forall (bc : Blockchain) (bt : BlockTree) (b : block) (bs : seq block),
    valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
    b \in bs -> bc >= btChain bt ->
    bc >= btChain (foldl btExtend bt bs) ->
    bc >= btChain (btExtend bt b).
Proof.
move=> bc bt b bs V Vh Ib H HGt HGt'.
move: (btExtendV_within Vh V H)=>V'.
move: (btExtendV V')=>V0.
move: (in_seq H)=>[bf] [af] H'; rewrite H' in HGt'; clear H;
(have: validH (btExtend bt b) by apply btExtendH)=>Vh';
(have: has_init_block (btExtend bt b) by apply btExtendIB)=>Ib'.
move: (btExtend_sameOrBetter V' Vh Ib)=>H.
move: (btExtend_fold_sameOrBetter V Vh Ib).
rewrite -cat1s foldl_cat btExtend_fold_comm in HGt' *.
rewrite foldl_cat /= -foldl_cat in HGt' *.
move: (btExtend_fold_within Vh V H')=>Eq.
have V1: valid (foldl btExtend (btExtend bt b) (af ++ bf)) by rewrite Eq.
move=>H0; case: HGt; case: HGt'; case: H; case: H0; move=>h0 h1 h2 h3.
- by left; rewrite h1 h3.
- by rewrite h3 in h2; rewrite h2 in h0; contradict h0; rewrite Eq; apply: FCR_nrefl.
- by rewrite -h0 in h1; contradict h1; subst bs; rewrite -Eq; apply btExtend_fold_not_worse.
- by subst bs; rewrite -Eq -h2 h3 in h0; contradict h0; apply: FCR_nrefl.
- by left; apply/eqP; rewrite eq_sym; rewrite -h3 in h1; apply/eqP.
- by rewrite -h3 in h1; rewrite -h1 in h2;
  contradict h2; apply btExtend_fold_not_worse.
- by rewrite -h3 in h0; subst bs; rewrite Eq h0 in h2; contradict h2; apply: FCR_nrefl.
- by rewrite h3 in h2; move: (FCR_trans h0 h2)=>C;
  contradict C; rewrite -Eq; apply: FCR_nrefl.
- by right; rewrite h1.
- by right; rewrite h1.
- by rewrite -h0 in h1; contradict h1; rewrite - Eq; apply btExtend_fold_not_worse.
- by subst bc; apply btExtend_fold_sameOrBetter.
- by right; rewrite -h1 in h3.
- by right; rewrite -h1 in h3.
- by rewrite -h0 in h1; contradict h1; rewrite -Eq; apply btExtend_fold_not_worse.
have: (btChain (foldl btExtend (btExtend bt b) (af ++ bf))
        >= btChain (btExtend bt b)) by apply: btExtend_fold_sameOrBetter.
case=>[|H].
by move=><-; right.
by right; move: (FCR_trans h2 H).
done.
Qed.

(* Trivial sub-case of the original lemma; for convenience *)
Lemma btExtend_seq_sameOrBetter_fref' :
  forall (bc : Blockchain) (bt : BlockTree) (b : block) (bs : seq block),
    valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
    b \in bs -> bc >= btChain bt ->
    bc = btChain (foldl btExtend bt bs) ->
    bc >= btChain (btExtend bt b).
Proof.
move=>bc bt b bs V Vh Ib iB Gt Eq.
(have: (bc >= btChain (foldl btExtend bt bs)) by left)=>GEq; clear Eq.
by move: (btExtend_seq_sameOrBetter_fref V Vh Ib iB Gt GEq).
Qed.

Lemma bc_spre_gt bc bc' :
  [bc <<< bc'] -> bc' > bc.
Proof. by case=>h; case=>t=>eq; rewrite eq; apply FCR_ext. Qed.

(*************************************************************)
(************    Remaining properties   **********************)
(*************************************************************)

Lemma foldl1 {A B : Type} (f : A -> B -> A) (init : A) (val : B) :
  foldl f init [:: val] = f init val.
Proof. done. Qed.

Lemma foldr1 {A B : Type} (f : A -> B -> B) (fin : B) (val : A) :
  foldr f fin [:: val] = f val fin.
Proof. done. Qed.

Lemma good_chain_btExtend bt X b :
  valid (btExtend bt X) -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  good_chain (compute_chain (btExtend bt X) b).
Proof.
move=>V Vh Ib Gc.
by move: (@btExtend_compute_chain _ X b V Vh Ib Gc)=>->.
Qed.

Lemma good_chain_btExtend_fold bt bs b :
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  good_chain (compute_chain (foldl btExtend bt bs) b).
Proof.
move=>V Vh Ib Gc.
elim/last_ind: bs V=>[|xs x Hi] V//.
rewrite -cats1 foldl_cat /=;
have V': valid (foldl btExtend bt xs) by move/btExtendV_fold1: V.
apply good_chain_btExtend.
by rewrite -cats1 foldl_cat //= in V.
by move: (@btExtendH_fold _ xs Vh)=>H; move/btExtendV_fold1: V=>V; specialize (H V).
by move: (btExtendIB_fold Vh V' Ib).
by specialize (Hi V').
Qed.

Lemma btExtend_compute_chain_fold bt bs b :
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  good_chain (compute_chain bt b) ->
  (compute_chain (foldl btExtend bt bs) b) = compute_chain bt b.
Proof.
move=>V Vh Ib G; elim/last_ind: bs V=>[|xs x Hi] V//.
rewrite -cats1 foldl_cat /=.
have V': valid (foldl btExtend bt xs) by move/btExtendV_fold1: V.
have V0: valid (btExtend (foldl btExtend bt xs) x) by move: V; rewrite -cats1 foldl_cat //=.
specialize (Hi V'); rewrite -Hi.
apply btExtend_compute_chain=>//=.
by apply btExtendH_fold.
by apply btExtendIB_fold.
by rewrite -Hi in G.
Qed.


(***********************************************************)
(*******      <btExtend_mint and all it needs>     *********)
(***********************************************************)

Lemma btChain_is_largest bt c :
  c \in good_chains bt -> btChain bt >= c.
Proof.
rewrite /btChain/good_chains; elim: (all_chains bt) c=>//=bc bcs Hi c.
case: ifP=>X/=; last by rewrite {1 3}/take_better_bc X=>/Hi.
rewrite inE; case/orP; last first.
- rewrite {1 3}/take_better_bc X=>/Hi=>{Hi}Hi.
  by case: ifP=>//=Y; right; apply:(FCR_trans_eq2 Y Hi).
move/eqP=>?; subst c; rewrite {1 3}/take_better_bc X/=.
by case: ifP=>//=Y; [by left|by move/FCR_dual: Y].
Qed.

Lemma btChain_good bt : good_chain (btChain bt).
Proof.
rewrite /btChain.
elim: (all_chains bt)=>[|bc bcs Hi]/=; first by rewrite eqxx.
rewrite {1}/take_better_bc; case:ifP=>//.
by case/andP=>/andP[->].
Qed.

Lemma btChain_tx_valid bt : valid_chain (btChain bt).
Proof.
rewrite /btChain.
elim: (all_chains bt)=>[|bc bcs Hi]/=;first by rewrite valid_chain_init.
rewrite {1}/take_better_bc; case:ifP=>//.
by case/andP=>/andP[_ ->].
Qed.

Lemma btChain_in_good_chains bt :
  has_init_block bt -> btChain bt \in good_chains bt.
Proof.
move=> Ib; rewrite/good_chains mem_filter; apply/andP; split;
by [rewrite btChain_good btChain_tx_valid | apply (btChain_in_bt Ib)].
Qed.

Lemma compute_chain_rcons bt c pc :
  valid bt -> validH bt -> c ∈ bt ->
  c != GenesisBlock ->
  find (prevBlockHash c) bt = Some pc ->
  compute_chain' bt c (dom bt) (size (dom bt)) =
  rcons (compute_chain' (free (# c) bt) pc
        (dom (free (# c) bt)) (size (dom (free (# c) bt)))) c.
Proof.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n c pc bt hs Es En=>[|n _]/= c pc bt hs Es En V Vh D Ng F;
move: D; rewrite/btHasBlock=>/andP[D0 D1].
- subst hs; move/esym/size0nil: En=>Z.
  by rewrite Z in D0.
rewrite D0 Es F; case: ifP=>Hc.
  rewrite D1//=; case: ifP; last first.
+ move=>_; congr (rcons _ _).
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es uniq_dom.
have U2: uniq (dom (free (#c) bt)) by rewrite uniq_dom.
have N: n = (size (dom (free (# c) bt))).
- by apply: size_free=>//; rewrite -?Es//.
rewrite -N; clear N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2) Es//.
by apply: dom_rem2.
by move/eqP in Ng; move/eqP.
by rewrite D0 in Hc.
Qed.

Lemma compute_chain_genesis bt :
  valid bt -> validH bt -> has_init_block bt ->
  compute_chain' bt GenesisBlock (dom bt) (size (dom bt)) =
  [:: GenesisBlock].
Proof.
move=>V Vh Ib.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n Es En=>[|n _]/= Es En.
- suff: False by [].
  by move: (find_some Ib); rewrite -Es;
     move/eqP in En; rewrite eq_sym in En; move/eqP in En; move: (size0nil En)=>->.
rewrite Es (find_some Ib);
case D: ((prevBlockHash GenesisBlock) \in dom bt); case: dom_find (D)=>//=.
move=>pb -> _ _; case: ifP.
  by case: ifP=>//=; move/eqP.
  by move: Ib (find_some Ib); rewrite/has_init_block/btHasBlock=>[]->->/eqP.
move=>->; case: ifP=>//=.
  by move: Ib (find_some Ib); rewrite/has_init_block/btHasBlock=>[]->->/eqP.
Qed.

Lemma compute_chain_noblock bt b c :
  valid bt -> validH bt ->
  b ∈ bt ->
  b \notin compute_chain bt c ->
  compute_chain bt c = compute_chain (free (#b) bt) c.
Proof.
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n c b bt hs Es En=>[|n Hi]/= c b bt hs Es En V Vh;
rewrite/btHasBlock=>/andP[Hb0 Hb1].
- suff X: size (dom (free (# b) bt)) = 0.
  by rewrite X=>/=_; case:ifP=>_; case:ifP=>_//=;
     case: ifP=>_//=; case: ifP.
  suff X: bt = Unit by subst bt; rewrite free0 dom0.
  subst hs; move/esym/size0nil: En=>Z.
  by apply/dom0E=>//z/=; rewrite Z inE.
(* These two seem to always appear in these proofs... *)
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)).
- apply: size_free=>//; by rewrite Es in En.
case: ifP=>[X|X _]; rewrite Es in X; last first.
- rewrite -H3; clear Hi En H3; case:n=>//=[|n]; first by case:ifP=>//=; case: ifP.
  by rewrite domF inE X; case:ifP; case: ifP.
case: dom_find X=>// prev F _ _ //=.
(* c != prev, but #c = # prev. Collision detection in compute_chain' *)
case: ifP; last first.
move=>F' _; have Nc: (c ∉ (free (# b) bt)).
    rewrite/btHasBlock; apply/nandP. rewrite domF inE //=;
    case: ifP; first by left.
    by rewrite findF eq_sym=>->; right; move/eqP: F'=>F'; apply/eqP.
by rewrite -H3; move: (compute_chain_no_block (dom (free (# b) bt)) n Nc)=>->.
move=>F'; (have Eq: (prev = c) by rewrite F in F'; move/eqP: F'=>[]); subst prev; clear F'.
case D: ((prevBlockHash c) \in dom bt); last first.
- case: dom_find (D)=>//->_; rewrite inE=>N; rewrite -H3.
  clear Hi; elim: n En H3=>/=[|n _]En H3; last first.
  case X: (#b == #c).
  by move/eqP: X F Hb1=>-> -> C; (have: (c == b) by [])=>/eqP X; subst b; move/eqP in N.
  + have Y: find (prevBlockHash c) (free (# b) bt) = None.
    * suff D': (prevBlockHash c) \notin dom (free (# b) bt) by case: dom_find D'.
      by rewrite domF inE D; case:ifP.
    rewrite Y; clear Y.
    have K : #c \in dom (free (# b) bt).
      by rewrite domF inE X (find_some F).
    by rewrite K; case: ifP=>//=; rewrite/btHasBlock K findF//= (eq_sym (#c) _) X F=>/eqP.
  (* Now need to derive a contradiction from H3 *)
  rewrite Es in En.
  have X: #c \in dom (free (# b) bt).
  + rewrite domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP: C F Hb1=>->->; rewrite eq_sym=>/eqP []; move/eqP: N.
  by move/esym/size0nil: H3=>E; rewrite E in X.

(* Now an interesting, inductive, case *)
case: dom_find D=>//pc F' _ _; rewrite F'=>Hn.
case: ifP.
* move/eqP=>G; subst c; move: Hn; case: ifP=>/eqP //= _ H; rewrite inE in H;
  apply/eqP; rewrite eq_sym; apply/eqP; apply compute_chain_genesis=>//=.
  by apply validH_free.
  by apply has_init_block_free=>//=; case X: (# GenesisBlock == # b)=>//=;
     move/eqP: X F Hb1=>->->; rewrite eq_sym=>/eqP []; move/eqP: H.

move/eqP=>Ng; move:Hn; case: ifP=>/eqP //= _ Hn.
rewrite mem_rcons inE in Hn; case/norP: Hn=>/negbTE N Hn.
have Dc: #c \in dom (free (# b) bt).
  + rewrite domF inE.
    case: ifP=>C; last by apply: (find_some F).
    by move/eqP: C F Hb1=>->->; rewrite eq_sym=>/eqP[]; move/eqP: N.

(* Now need to unfold massage the RHS of the goal with compute_chain', so
   it would match the Hi with (bt := free (# c) bt, c := pc) etc *)
have X: compute_chain' (free (# b) bt) c
                       (dom (free (# b) bt))
                       (size (dom (free (# b) bt))) =
        rcons (compute_chain' (free (# b) (free (# c) bt)) pc
                              (dom (free (# b) (free (# c) bt)))
                              (size (dom (free (# b) (free (# c) bt))))) c.
- rewrite freeF.
  have Z: (#b == #c) = false
    by move: Dc; rewrite domF inE; case: ifP=>//=.
  rewrite Z.
  (* Given everything in the context, this should be a trivial lemma,
     please extract it and prove (takig bt' = free (# b) bt) *)
  (* From Dc, F, N & Z have c ∈ (free (# b) bt) ! *)
  apply: compute_chain_rcons=>//; rewrite ?validF//.
  + by apply: validH_free.
  + by rewrite/btHasBlock Dc findF (eq_sym (#c) _) Z F//=.
  + by apply/eqP.
  suff X: prevBlockHash c == # b = false by rewrite findF X.
  apply/negP=>/eqP Y; rewrite -Y in Z.
  move/Vh: (F')=>E'; rewrite E' in Y Z F'.
  have Hb1': find (# b) bt == Some b by [].
  move: Y F' Hb1'=>->->/eqP []=>Eq; subst pc.
  have T: exists m, n = m.+1.
  + rewrite Es in En.
    clear Hn Hi E' En H1 Vh; subst hs.
    case: n H3=>//[|n]; last by exists n.
    by move/esym/size0nil=>E; rewrite E in Dc.
  case: T=>m Zn; rewrite Zn/= in Hn.
  rewrite Es in Hn.
  have X: # b \in seq.rem (# c) (dom bt) by
    apply: rem_neq=>//=; by rewrite Z.
    (* by apply/negP => H_eq; by case/negP: Z. *)
  have Hb': (b ∈ free (# c) bt)
    by rewrite/btHasBlock domF inE (eq_sym (#c) _) Z Hb0 findF Z Hb1.
  rewrite X Hb' in Hn.
  case: (find _ _) Hn=>[?|]; last by rewrite inE eqxx.
  case: ifP; first by (move=>_; rewrite inE=>/eqP).
  by rewrite mem_rcons inE eqxx.
(* The interesting inductive case! *)
rewrite H3 X; congr (rcons)=>//.
have U1: uniq (seq.rem (# c) hs) by rewrite rem_uniq// Es uniq_dom.
have U2: uniq (dom (free (#c) bt)) by rewrite uniq_dom.
rewrite -(Hi pc b (free (#c) bt) (dom (free (# c) bt)) (erefl _)) ?validF//.
- rewrite -H3.
  rewrite ((compute_chain_equiv (free (# c) bt) pc n) U1 U2)//.
  by rewrite Es; apply: dom_rem2.
- (* prove out of H3 and N *)
  rewrite Es in En; apply: (size_free V En).
  by apply:(find_some F).
- by apply: validH_free.
- rewrite/btHasBlock domF inE (eq_sym (#c) _) Hb0 findF;
    case: ifP=>//=.
    by move=>Heq; move/eqP: Heq F Hb1=>->-> C;
      (have: (c == b) by []); rewrite eq_sym N.
rewrite -(compute_chain_equiv (free (# c) bt) pc n U1 U2)//.
by rewrite Es; apply: dom_rem2.
Qed.

Lemma compute_chain_prev bt b pb :
  valid bt -> validH bt -> b ∈ bt -> pb ∈ bt ->
  b != GenesisBlock ->
  prevBlockHash b = # pb ->
  b \notin (compute_chain bt pb) ->
  compute_chain bt b = rcons (compute_chain bt pb) b.
Proof.
move=>V Vh D D' Ng Hp Nh.
rewrite (compute_chain_noblock V Vh D Nh).
rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En V Vh Ng D D' Hp Nh=>[|n Hi] b bt hs Es En V Vh Ng D D' Hp Nh/=;
move: D; rewrite/btHasBlock=>/andP[D0 D1].
- by rewrite -Es in D0; move/esym/size0nil: En=>Z; rewrite Z in D0.
rewrite {1}Es D0 Hp.
have H1: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)).
- by apply: size_free=>//; rewrite Es in En.
rewrite D1=>//=.
rewrite/btHasBlock in D'; move/andP: D'=>[P0 [/eqP P1]].
rewrite P1; case: ifP=>//=; [by move/eqP; move/eqP: Ng|move=>_].
congr (rcons _ _).
rewrite H3.
have U1: uniq (seq.rem (# b) hs) by rewrite Es rem_uniq// uniq_dom.
have U2: uniq (dom (free (# b) bt)) by rewrite uniq_dom.
rewrite (compute_chain_equiv (free (#b) bt) pb
                 (size (dom (free (# b) bt))) U1 U2)//.
by rewrite Es; apply: dom_rem2.
Qed.

Lemma compute_chain_last bt b :
    (compute_chain bt b = [::]) \/ # last GenesisBlock (compute_chain bt b) = # b.
Proof.
rewrite/compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En=>[|n Hi] b bt hs Es En/=.
- by left; case: ifP=>//=; case: ifP=>//=.
case: ifP; last by left.
case: ifP; last by left.
move=>Hb; case D1: (prevBlockHash b \in dom bt); case: dom_find D1=>//=;
last by move=>->; right.
by move=>pb F _ _; right; rewrite F; case: ifP=>//=; rewrite last_rcons.
Qed.

Lemma compute_chain_hash_chain bt b :
  valid bt -> validH bt ->
  hash_chain (compute_chain bt b).
Proof.
move=>V Vh; rewrite /compute_chain.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En V Vh=>[|n Hi] b bt hs Es En V Vh/=.
- by case: ifP=>//=; case: ifP=>//=.
case: ifP=>X //=; case: ifP=>Hb//=.
move: Hb; rewrite/btHasBlock=>/andP[Hb0 Hb1].
have H1: validH (free (# b) bt) by apply validH_free.
have H2: valid (free (# b) bt) by rewrite validF.
have H3: n = size (dom (free (# b) bt)).
- by apply: size_free=>//; rewrite Es in En X.
case D1: (prevBlockHash b \in dom bt); case: dom_find (D1)=>//; last by move=>->.
move=> pb F; rewrite F; case: ifP=>//= A _ _.
rewrite H3.
have U1: uniq (seq.rem (# b) hs) by rewrite Es rem_uniq// uniq_dom.
have U2: uniq (dom (free (# b) bt)) by rewrite uniq_dom.
rewrite (compute_chain_equiv (free (#b) bt) pb
          (size (dom (free (# b) bt))) U1 U2)//;
last by rewrite Es; apply: dom_rem2.
have Df: (dom (free (# b) bt) = dom (free (# b) bt)) by [].
move: (Hi pb (free (# b) bt) (dom (free (# b) bt)) Df H3 H2 H1)=>H.
move: (Vh _ _ F)=>Hc; rewrite -H3.
case: (compute_chain_last (free (# b) bt) pb); rewrite/compute_chain -H3.
by move=>->.
by move=>L; apply hash_chain_rcons=>//=; rewrite L.
Qed.

Lemma good_chain_nocycle bt bc c lb :
  valid bt -> validH bt -> has_init_block bt ->
  bc = compute_chain bt lb ->
  good_chain bc ->
  c \in bc ->
  c == GenesisBlock \/ prevBlockHash c != # lb.
Proof.
move=>V Vh Ib.
case: (compute_chain_last bt lb); first by move=>->->.
move=>L; move: (compute_chain_uniq_hash lb V)=>Uh.
move: (compute_chain_hash_chain lb V Vh)=>Hc C Gc.
case: bc C Gc=>//=; move=>b bc C /eqP Z; subst b.
rewrite inE=>/orP; case; first by left.
rewrite -C in Hc Uh L.
move=>In; move: (hash_chain_uniq_hash_nocycle Hc Uh)=>H.
by specialize (H c In); rewrite L in H; right.
Qed.

Lemma btExtend_mint_ext bt bc b :
  let pb := last GenesisBlock bc in
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  bc = compute_chain bt pb ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  VAF (proof b) bc (txs b) ->
  compute_chain (btExtend bt b) b = rcons bc b.
Proof.
move=>pb V' Vh Ib E HGood Hp Hv; move: (btExtendV V')=>V.
suff X: compute_chain (btExtend bt b) b =
        rcons (compute_chain (btExtend bt b) pb) b.
- rewrite E in HGood.
  rewrite (btExtend_compute_chain V' Vh Ib HGood) in X.
  by rewrite X -E.
have Vh': validH (btExtend bt b) by apply:btExtendH.
have D: b ∈ (btExtend bt b) by apply in_ext.
case X: (b == GenesisBlock)=>//=.
by move/eqP in X; subst b; move: (VAF_GB_first Hv) (HGood) ->.
apply: compute_chain_prev=>//=.
(* apply in_ext=>//=. *)
case: (last_in_chain pb V).
by rewrite -E; move/eqP=>Eq; rewrite Eq in HGood.
move=>In; move: (block_in_chain V Ib In).
rewrite/btExtend; case: ifP=>//=.
case: ifP=>//=.
by move=>A B; contradict V'; rewrite/btExtend B A valid_undef.
rewrite/btHasBlock domUn inE validPtUn V //=.
move=>Nb /andP [] -> F; apply/andP; split.
by rewrite Nb //=; apply/orP; right.
rewrite findUnR; move/eqP in F; move: (find_some F).
by move=>->; apply/eqP.
by rewrite validPtUn V //= Nb.
by rewrite X.
rewrite E in HGood.
rewrite (btExtend_compute_chain V' Vh Ib HGood) -E.
case Y: (b \in bc)=>//=.
rewrite -E in HGood.
(* Contradiction X Y Hp E *)
case: (good_chain_nocycle V Vh Ib E HGood Y).
by rewrite X.
by rewrite Hp=>/eqP.
Qed.

Lemma chain_from_last bt c :
  valid bt -> validH bt -> has_init_block bt ->
  c \in all_chains bt -> c = compute_chain bt (last GenesisBlock c).
Proof.
move=>V Vh Ib/mapP[b] H1 H2.
suff X: (last GenesisBlock (compute_chain bt b)) = b.
- by rewrite -H2 in X; rewrite X.
move/mapP:H1=>[h]; move =>D.
case: dom_find (D)=>//b' F _ _; move/Vh: (F)=>?; subst h.
rewrite /get_block F=>?; subst b'.
rewrite /compute_chain; clear H2 V Vh Ib.
have Ek: dom bt = dom bt by [].
have Es: size (dom bt) = size (dom bt) by [].
move: {-2}(size (dom bt)) Es=>n.
move: {-2}(dom bt) Ek=>hs Es En.
elim: n b bt hs Es En D F=>[|n Hi] b bt hs Es En D F/=.
- by rewrite -Es in D; move/esym/size0nil: En=>Z; rewrite Z in D.
rewrite Es D; case (find _ _)=>[?|]//; case: ifP=>//=.
by case: ifP=>//=; rewrite last_rcons.
by rewrite/btHasBlock D F //=; (have: Some b == Some b by [])=>->.
by rewrite/btHasBlock D F //=; (have: Some b == Some b by [])=>->.
Qed.

Definition valid_chain_block bc (b : block) :=
  [&& VAF (proof b) bc (txs b) & all [pred t | txValid t bc] (txs b)].

Lemma valid_chain_last_ind c b prefix:
  VAF (proof b) prefix (txs b) ->
  all [pred t | txValid t prefix] (txs b) ->
  valid_chain' c (rcons prefix b) ->
  valid_chain' (b :: c) prefix.
Proof. by move=>/=->->. Qed.

Lemma valid_chain_last bc b :
  valid_chain_block bc b -> valid_chain bc -> valid_chain (rcons bc b).
Proof.
move=>H1.
have H2 := H1.
move/andP: H2 => [P1 P2].
have Z: bc = [::] ++ bc by rewrite ?cats0 ?cat0s.
rewrite Z in P1, P2; rewrite /valid_chain; clear Z.
move: [::] P1 P2 => p.
elim: {-1}bc p H1.
- by move=>p _ /= A B _; rewrite cats0 in A, B; rewrite A B.
move=>x xs Hi p T A B/=/andP[Z1 Z2]; rewrite Z1//=.
by apply: (Hi (rcons p x) T _ _ Z2); rewrite cat_rcons.
Qed.

Lemma btExtend_mint_good_valid bt b :
  let bc := btChain bt in
  let pb := last GenesisBlock bc in
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  valid_chain_block bc b ->
  good_chain bc ->
  prevBlockHash b = #pb ->
  good_chain (compute_chain (btExtend bt b) b) /\
  valid_chain (compute_chain (btExtend bt b) b).
Proof.
move=>bc pb V' Vh Ib Tb Gc Hv; move: (btExtendV V')=>V.
(have: bc \in all_chains bt by move: (btChain_in_bt Ib))=>InC.
(have: bc = compute_chain bt pb by move: (chain_from_last V Vh Ib InC))=>C.
move: (btExtend_mint_ext V' Vh Ib C Gc Hv)=>->; subst bc; last by move/andP: Tb => [Hv' Hi].
rewrite/good_chain. case X: (rcons _ _)=>[|x xs].
contradict X; elim: (btChain bt)=>//.
have: (good_chain (btChain bt) = true)by [].
rewrite/good_chain/=; case X': (btChain _)=>[|h t]; first done.
move/eqP=>Eq; subst h; rewrite X' rcons_cons in X; case: X=> ??.
subst x xs; split=>//.
move: (btChain_tx_valid bt)=>Tc.
rewrite !X' in Tb Tc; rewrite -rcons_cons.
by apply: valid_chain_last.
Qed.

Lemma btExtend_mint bt b :
  let pb := last GenesisBlock (btChain bt) in
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  valid_chain_block (btChain bt) b ->
  prevBlockHash b = # pb ->
  btChain (btExtend bt b) > btChain bt.
Proof.
move=>lst V' Vh Ib T mint; move: (btExtendV V')=>V.
have HGood: good_chain (rcons (btChain bt) b).
- by move: (btChain_good bt); rewrite {1}/good_chain; case (btChain bt).
have Hvalid: valid_chain (rcons (btChain bt) b).
- by move: (btChain_tx_valid bt); apply: valid_chain_last.
have E: compute_chain (btExtend bt b) b = rcons (btChain bt) b.
- move/andP: T => [Hv Ht].
  apply btExtend_mint_ext=>//=.
  by move/(chain_from_last V Vh Ib): (btChain_in_bt Ib).
apply btChain_good.
have HIn : rcons (btChain bt) b \in
           filter (fun c => good_chain c && valid_chain c) (all_chains (btExtend bt b)).
- rewrite mem_filter HGood Hvalid/=-E/all_chains; apply/mapP.
  exists b=>//; rewrite /all_blocks/btExtend in V'*; apply/mapP; exists (#b).
  + case: ifP; last by rewrite domPtUn inE eqxx andbC //= validPtUn V=>->.
    case: ifP=>//=B A; by rewrite B A valid_undef in V'.
  rewrite /get_block; case:ifP V'=>X V'; last by rewrite findPtUn.
  case: dom_find X=>//b' F _ _.
  rewrite F; case: ifP.
  by move/eqP=>[]Eq; subst b'; rewrite F.
  by move=>Neq; rewrite F Neq valid_undef in V'.
move/btChain_is_largest: HIn=>H; apply: (FCR_trans_eq1 H).
by rewrite -cats1; apply: FCR_ext.
Qed.

(***********************************************************)
(*******      </btExtend_mint and all it needs>     ********)
(***********************************************************)

Definition good_bt bt :=
  forall b, b \in all_blocks bt ->
            good_chain (compute_chain bt b) && valid_chain (compute_chain bt b).

Lemma btExtend_good_chains_fold  bt bs:
  valid (foldl btExtend bt bs) -> validH bt -> has_init_block bt ->
  {subset good_chains bt <= good_chains (foldl btExtend bt bs) }.
Proof.
move=>V Vh Hib c; rewrite !mem_filter=>/andP[G]; rewrite G/=.
rewrite/good_chains/all_chains=>/mapP[b]H1 H2; apply/mapP; exists b.
- apply/mapP; exists (#b).
  + apply/(btExtend_dom_fold V).
    case/mapP: H1=>z; move=>D.
    rewrite /get_block; case: (@dom_find _ _ _ z) (D)=>//b' F _ _.
    by rewrite F=>Z; subst b'; move/Vh: F=><-.
  case/mapP: H1=>z; move=>D.
  move/(btExtend_dom_fold V): (D)=>D'.
  rewrite {1}/get_block; case:dom_find (D)=>//b' F _ _.
  rewrite F=>?; subst b'.
  rewrite /get_block. case:dom_find (D')=>//b' F' _ _.
  move: (Vh _ _ F)=>H; rewrite -H F'.
  by move: (btExtend_find_fold V D F'); rewrite F=>[][].
rewrite btExtend_compute_chain_fold=>//; rewrite -H2.
by case/andP: G.
Qed.

Lemma good_chains_subset bt :
  { subset good_chains bt <= all_chains bt }.
Proof. by move=>ch; rewrite mem_filter; move/andP=>[]. Qed.

Lemma btExtend_new_block cbt b :
  valid (btExtend cbt b) ->
  # b \notin dom cbt ->
  b \in all_blocks (btExtend cbt b).
Proof.
move=>V' N; move: (btExtendV V')=>V.
move/negbTE: N=>N.
rewrite /btExtend !N in V' *.
case:(@dom_insert _ _ (#b) b cbt V')=>ks1[ks2][_].
rewrite /all_blocks=>->.
apply/mapP; exists (#b); last first.
- by rewrite /get_block findUnL// domPt inE eqxx findPt.
by rewrite mem_cat orbC inE eqxx.
Qed.

Lemma btExtend_get_block bt b k :
  valid (btExtend bt b) -> #b \notin dom bt -> k != #b ->
  get_block (btExtend bt b) k = get_block bt k.
Proof.
move=>V' D N; move: (btExtendV V')=>V; rewrite /get_block/btExtend (negbTE D).
rewrite findUnL ?validPtUn ?D ?V //=.
by rewrite domPt inE eq_sym (negbTE N).
Qed.

Lemma good_chain_rcons bc b :
  good_chain bc -> good_chain (rcons bc b).
Proof. by move=>Gc; elim: bc Gc=>//. Qed.

Lemma btExtend_good_split cbt b :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  good_bt cbt -> #b \notin dom cbt -> good_bt (btExtend cbt b) ->
  exists cs1 cs2,
    good_chains cbt = cs1 ++ cs2 /\
    good_chains (btExtend cbt b) = cs1 ++ [:: compute_chain (btExtend cbt b) b] ++ cs2.
Proof.
move=>V' Vh Hib Hg N Hg'; move: (btExtendV V')=>V.
have G: good_chain (compute_chain (btExtend cbt b) b).
- by case/andP: (Hg' b (btExtend_new_block V' N)).
have T: valid_chain (compute_chain (btExtend cbt b) b).
- by case/andP: (Hg' b (btExtend_new_block V' N)).
have Eb: btExtend cbt b = (#b \\-> b \+ cbt) by rewrite /btExtend (negbTE N).
have V0: valid (#b \\-> b \+ cbt) by rewrite -Eb.
(* move: (V); rewrite (btExtendV _ b)=>V'; rewrite !Eb in V' *. *)
move: (@dom_insert _ _ (#b) b cbt V0)=>[ks1][ks2][Ek]Ek'.
(* Massaging the left part *)
set get_chain := [eta compute_chain cbt] \o [eta get_block cbt].
rewrite /good_chains{1}/all_chains/all_blocks -!seq.map_comp Ek map_cat filter_cat.
rewrite -/get_chain.
exists [seq c <- [seq get_chain i | i <- ks1] | good_chain c & valid_chain c],
       [seq c <- [seq get_chain i | i <- ks2] | good_chain c & valid_chain c]; split=>//.
rewrite /all_chains/all_blocks Eb Ek' /= -cat1s.
have [N1 N2] : (#b \notin ks1) /\ (#b \notin ks2).
- have U : uniq (ks1 ++ # b :: ks2) by rewrite -Ek'; apply:uniq_dom.
  rewrite cat_uniq/= in U; case/andP: U=>_/andP[]H1 H2.
  case/andP:H2=>->_; split=>//; by case/norP: H1.
have [D1 D2] : {subset ks1 <= dom cbt} /\ {subset ks2 <= dom cbt}.
- by split=>k; rewrite Ek mem_cat=>->//; rewrite orbC.
rewrite !map_cat !filter_cat ; congr (_ ++ _); clear Ek Ek'.
- rewrite -!Eb;elim: ks1 N1 D1=>//k ks Hi/= N1 D1.
  have Dk: k \in dom cbt by apply: (D1 k); rewrite inE eqxx.
  have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N1 .
  rewrite !(btExtend_get_block V' N Nk); rewrite /get_chain/=.
  set bk := (get_block cbt k).
  have Gk: good_chain (compute_chain cbt bk) && valid_chain (compute_chain cbt bk).
  - by apply: Hg; apply/mapP; exists k.
  case/andP: (Gk)=>Gg Gt.
  rewrite !(btExtend_compute_chain V' Vh Hib Gg) !Gk/=.
  congr (_ :: _); apply: Hi; first by rewrite inE in N1; case/norP:N1.
  by move=>z=>D; apply: D1; rewrite inE D orbC.
rewrite -[(compute_chain _ b) :: _]cat1s; congr (_ ++ _)=>/=; rewrite -!Eb.
- suff D: (get_block (btExtend cbt b) (# b)) = b by rewrite D G T.
  by rewrite /get_block/btExtend (negbTE N) findUnL ?V'// domPt inE eqxx findPt.
elim: ks2 N2 D2=>//k ks Hi/= N2 D2.
have Dk: k \in dom cbt by apply: (D2 k); rewrite inE eqxx.
have Nk: k != #b by apply/negbT/negP=>/eqP=>?; subst k; rewrite inE eqxx in N2.
rewrite !(btExtend_get_block V' N Nk); rewrite /get_chain/=.
set bk := (get_block cbt k).
have Gk: good_chain (compute_chain cbt bk) && valid_chain (compute_chain cbt bk).
- by apply: Hg; apply/mapP; exists k.
case/andP: (Gk)=>Gg Gt.
rewrite !(btExtend_compute_chain V' Vh Hib Gg) !Gk/=.
congr (_ :: _); apply: Hi; first by rewrite inE in N2; case/norP:N2.
by move=>z=>D; apply: D2; rewrite inE D orbC.
Qed.

Definition take_better_alt bc2 bc1 := if (bc2 > bc1) then bc2 else bc1.

(* Alternative definition of btChain, more convenient to work with *)
(* only good chains. *)
Lemma btChain_alt bt:
  btChain bt =
  foldr take_better_alt [:: GenesisBlock] (good_chains bt).
Proof.
rewrite /btChain/take_better_bc/take_better_alt/good_chains.
elim: (all_chains bt)=>//c cs/= Hi.
by case C: (good_chain c && valid_chain c)=>//=; rewrite !Hi.
Qed.

Lemma best_chain_in cs :
  foldr take_better_alt [:: GenesisBlock] cs = [:: GenesisBlock] \/
  foldr take_better_alt [:: GenesisBlock] cs \in cs.
Proof.
elim: cs=>[|c cs Hi]; [by left|].
rewrite /take_better_alt/=; case:ifP; rewrite -/take_better_alt=>X.
- by right; rewrite inE eqxx.
case/FCR_dual: X=>X.
- by rewrite !X in Hi *; right; rewrite inE eqxx.
by case: Hi=>H; [left| right]=>//; rewrite inE orbC H.
Qed.

Lemma foldr_better_mono bc cs : foldr take_better_alt bc cs >= bc.
Proof.
elim: cs=>//=[|c cs Hi/=]; first by left.
rewrite {1 3}/take_better_alt; case: ifP=>G//.
by right; apply:(FCR_trans_eq2 G Hi).
Qed.

Lemma best_element_in bc cs1 cs2 bc' :
  bc > [:: GenesisBlock] ->
  bc > foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) ->
  bc \in cs1 ++ [:: bc'] ++ cs2 ->
  bc = foldr take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc'] ++ cs2).
Proof.
move=>Gt H1 H2.
have G: forall c, c \in cs1 ++ cs2 -> bc > c.
- elim: (cs1 ++ cs2) H1=>//=c cs Hi H z.
  rewrite {1}/take_better_alt in H; move: H.
  case:ifP=>//G1 G2.
  + rewrite inE; case/orP; first by move/eqP=>?; subst z.
    by move/Hi: (FCR_trans G2 G1)=>G3; move/G3.
  rewrite inE; case/orP; last by move/(Hi G2).
  move/eqP=>?; subst z; case/FCR_dual: G1=>G1; first by rewrite !G1 in G2.
  by apply: (FCR_trans G2 G1).
have [G1 G2]: ((forall z, z \in cs1 -> bc > z) /\
               forall z, z \in cs2 -> bc > z).
- split=>z H; move: (G z); rewrite mem_cat H/=; first by move/(_ is_true_true).
  by rewrite orbC; move/(_ is_true_true).
clear G.
have Z: bc = bc'.
- suff C: bc \in [:: bc'] ++ cs2.
  + elim: (cs2) C G2=>//=[|c cs Hi C G2]; first by rewrite inE=>/eqP.
    rewrite inE in C; case/orP:C; first by move/eqP.
    by move/G2; move/FCR_nrefl.
  elim: (cs1) G1 H2=>//=c cs Hi G1 H2.
  rewrite inE in H2; case/orP: H2.
  + move/eqP=>Z; subst c; move: (G1 bc).
    by rewrite inE eqxx/==>/(_ is_true_true)/FCR_nrefl.
  rewrite mem_cat; case/orP=>// G.
  by move: (G1 bc); rewrite inE orbC G/==>/(_ is_true_true)/FCR_nrefl.
subst bc'; clear H1 H2.
(* Ok, here comes the final blow *)
suff C: bc = foldr take_better_alt [:: GenesisBlock] ([:: bc] ++ cs2).
- rewrite foldr_cat -C; clear C.
  elim: cs1 G1=>//c cs Hi G1; rewrite /take_better_alt/=-/take_better_alt.
  case: ifP=>G.
  - move: (FCR_trans_eq2 G (foldr_better_mono bc cs))=>G'.
    move: (G1 c). rewrite inE eqxx/==>/(_ is_true_true) G3.
    by move: (FCR_nrefl (FCR_trans G' G3)).
  by case/FCR_dual: G=>G;
     apply: Hi=>z T; move: (G1 z); rewrite inE T orbC/=;
     by move/(_ is_true_true).
clear G1 cs1.
simpl; rewrite {1}/take_better_alt.
suff C: bc > foldr take_better_alt [:: GenesisBlock] cs2 by rewrite C.
elim: cs2 G2=>//=c cs Hi G.
rewrite {1}/take_better_alt; case: ifP=>C.
- by move: (G c); rewrite inE eqxx/=; move/(_ is_true_true).
apply: Hi=>z T; move: (G z); rewrite inE T orbC/=.
by move/(_ is_true_true).
Qed.

Lemma better_comm bc x y :
  take_better_alt (take_better_alt bc x) y =
  take_better_alt (take_better_alt bc y) x.
Proof.
rewrite/take_better_alt.
case X: (bc > x); case Y: (bc > y).
  by rewrite X.
case/FCR_dual: Y=>H.
  by subst bc; rewrite X.
  by move: (FCR_trans H X)=>->.
case/FCR_dual: X=>H.
  by subst bc; rewrite Y; case: ifP=>//=.
  by move: (FCR_trans H Y)=>->; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
case/FCR_dual: X; case/FCR_dual: Y.
  by move=>->->; case: ifP=>//=.
  by move=>H Eq; subst bc; rewrite H; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
  by move=>-> H; rewrite H; case: ifP=>//=;
     move=>H'; move: (FCR_nrefl (FCR_trans H H')).
case: ifP; case: ifP=>//=.
  by move=>H H'; move: (FCR_nrefl (FCR_trans H H')).
case/FCR_dual=>X; case/FCR_dual=>Y//.
  by move: (FCR_nrefl (FCR_trans X Y)).
Qed.

Lemma better_comm' x y :
  take_better_alt x y = take_better_alt y x.
Proof.
rewrite/take_better_alt; case: ifP; case: ifP; do? by [].
by move=>H1 H2; move: (FCR_nrefl (FCR_trans H1 H2)).
move/FCR_dual=>H1/FCR_dual H2; case: H1; case: H2; do? by [].
by move=>H1 H2; move: (FCR_nrefl (FCR_trans H1 H2)).
Qed.

Lemma foldl_better_comm bc cs1 cs2 :
  foldl take_better_alt (foldl take_better_alt bc cs1)
    cs2 =
  foldl take_better_alt (foldl take_better_alt bc cs2)
    cs1.
Proof.
elim/last_ind: cs1=>[|xs x Hi]/=; first done.
rewrite -cats1 !foldl_cat -Hi; clear Hi.
elim/last_ind: cs2=>[|ys y Hi]/=; first done.
rewrite -cats1 !foldl_cat Hi /=; apply better_comm.
Qed.

Lemma foldl_better_comm_cat bc cs1 cs2 :
  foldl take_better_alt bc (cs1 ++ cs2) =
  foldl take_better_alt bc (cs2 ++ cs1).
Proof. by rewrite !foldl_cat; apply foldl_better_comm. Qed.

Lemma foldl_foldr_better bc cs :
  foldr take_better_alt bc cs =
  foldl take_better_alt bc cs.
Proof.
elim: cs=>//[x xs Hi].
rewrite -(@cat1s _ x xs) foldr_cat foldl_cat /=.
rewrite better_comm' -(@foldl1 _ _ _ bc x).
by rewrite -foldr1 foldl_better_comm /= Hi.
Qed.

Lemma foldl_better_reduce bc cs :
  bc > [:: GenesisBlock] ->
  foldl take_better_alt bc cs =
  take_better_alt bc (foldl take_better_alt [:: GenesisBlock] cs).
Proof.
move=>Gt; elim/last_ind: cs=>/=[|cs c Hi].
  by rewrite/take_better_alt Gt.
rewrite -cats1 !foldl_cat /= Hi.
rewrite{1 2 4}/take_better_alt.
case X: (bc > foldl take_better_alt [:: GenesisBlock] cs).
- case: ifP.
  by move=>Y; rewrite{1}/take_better_alt; case: ifP=>//=;
     case: ifP; do? by [rewrite X|rewrite Y].
  case/FCR_dual=>Y.
    by subst c; rewrite{1 3}/take_better_alt; case: ifP=>//=;
       case: ifP=>//= Y; move: (FCR_nrefl (FCR_trans X Y)).
    rewrite{1 3}/take_better_alt; case: ifP.
      by case: ifP=>//= Z;
         [move: (FCR_nrefl (FCR_trans X (FCR_trans Z Y))) |
          move=>Y'; move: (FCR_nrefl (FCR_trans Y Y'))].
      case: ifP=>//=.
        by move=>Z; move: (FCR_nrefl (FCR_trans X (FCR_trans Z Y))).
- case/FCR_dual: X=>H.
  by rewrite H; case: ifP=>//= X;
     rewrite/take_better_alt X /=; case: ifP=>//=; by rewrite X.
  case: ifP.
  * move=>X; case: ifP=>//=.
      by rewrite{1}/take_better_alt X=>H'; move: (FCR_nrefl (FCR_trans H H')).
  * rewrite{1}/take_better_alt X /=; case/FCR_dual=>Y.
      by subst bc; move: (FCR_nrefl H).
      by rewrite{2}/take_better_alt X /=.
  case/FCR_dual=>X;
  rewrite{1 3}/take_better_alt; case: ifP; case: ifP=>//=.
    by rewrite X; move=>Y; move: (FCR_nrefl Y).
    by rewrite X; move=>_ H'; move: (FCR_nrefl (FCR_trans H H')).
    by move=>X'; move: (FCR_nrefl (FCR_trans X X')).
    by move=>_ H'; move: (FCR_nrefl (FCR_trans H (FCR_trans H' X))).
  by move=>X'; move: (FCR_nrefl (FCR_trans X X')).
Qed.

Lemma foldl_better_extract bc cs1 cs2 :
  foldl take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc] ++ cs2) =
  foldl take_better_alt [:: GenesisBlock] (cs1 ++ cs2 ++ [:: bc]).
Proof.
rewrite (@foldl_better_comm_cat [:: GenesisBlock] cs1 ([:: bc] ++ cs2)).
move: (@foldl_better_comm_cat [:: GenesisBlock] (cs1 ++ cs2) [:: bc]).
by rewrite -!catA; move=>->/=; apply foldl_better_comm_cat.
Qed.

Lemma lesser_elim bc cs1 cs2 :
  bc > [:: GenesisBlock] ->
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) > bc ->
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ cs2) >=
  foldr take_better_alt [:: GenesisBlock] (cs1 ++ [:: bc] ++ cs2).
Proof.
rewrite !foldl_foldr_better=>H G.
rewrite (@foldl_better_comm_cat [:: GenesisBlock] cs1 ([:: bc] ++ cs2)).
rewrite (@foldl_cat _ _ _ [:: GenesisBlock] ([:: bc] ++ cs2)).
rewrite /= better_comm'.
have X: take_better_alt bc [:: GenesisBlock] = bc.
  by rewrite/take_better_alt H.
rewrite X.
rewrite -(@foldl_cat _ _ take_better_alt bc).
rewrite (@foldl_better_comm_cat bc cs2 cs1).
set cs := (cs1 ++ cs2) in G *.
rewrite (@foldl_better_reduce bc)=>//.
rewrite{2}/take_better_alt; case: ifP.
  by move=>G'; move: (FCR_nrefl (FCR_trans G G')).
  case/FCR_dual=>[Eq|_].
   by rewrite Eq in G; move: (FCR_nrefl G).
   by left.
Qed.

Lemma complete_bt_extend_gt' cbt bt bs b :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  good_bt cbt -> #b \notin dom cbt -> good_bt (btExtend cbt b) ->
  btChain (btExtend bt b) > btChain cbt ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend bt b) = btChain (btExtend cbt b).
Proof.
move=>V' Vh Hib Vl' Vhl Hil Hg Nb Hg' Gt Ec.
move: (btExtendV V') (btExtendV Vl')=>V Vl.
have Z: (btExtend bt b = foldl btExtend bt [:: b]) by [].
have V0: valid (foldl btExtend (foldl btExtend bt bs) [::b]) by rewrite -Ec.
have H1: btChain (btExtend bt b) \in good_chains (btExtend cbt b).
- rewrite Ec; move: (btExtend_fold_comm bs [::b] Vhl)=>/=->.
  apply: btExtend_good_chains_fold=>//=.
  by rewrite Z btExtendV_fold_comm.
  by apply: (btExtendH Vl Vhl).
  by apply btExtendIB.
  by apply: btChain_in_good_chains; apply: btExtendIB.
set bc := btChain (btExtend bt b) in H1 Gt *.
have Gt' : bc > [::GenesisBlock].
- rewrite /good_chains mem_filter in H1.
  case/andP:H1; case/andP=>/good_init/FCR_dual; case=>//H _.
  subst bc; rewrite H in Gt.
  move: (btChain_in_good_chains Hib); rewrite /good_chains mem_filter.
  by case/andP; case/andP=>/good_init; rewrite Gt.
clear Vl Vhl Hil Ec. (* Let's forget about bt. *)
case: (btExtend_good_split V' Vh Hib Hg Nb Hg')=>cs1[cs2][E1]E2.
rewrite !btChain_alt in Gt *; rewrite E1 in Gt; rewrite !E2 in H1 *.
have I: [:: GenesisBlock] \in cs1 ++ cs2.
- rewrite -E1 mem_filter/= eqxx/=; apply/andP; split=>//; last by apply:all_chains_init.
  exact: valid_chain_init.
by apply: best_element_in.
Qed.

Lemma btExtend_with_new cbt bt bs b :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  btChain (btExtend bt b) > btChain cbt ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend bt b) = btChain (btExtend cbt b).
Proof.
move=>V' Vh Hib Vl' Vhl Hil Hg Hg' Gt Ec.
move: (btExtendV V') (btExtendV Vl')=>V Vl.
case Nb: (b ∈ cbt); last first.
- move/nandP: Nb=>[]Nb.
    by apply: (complete_bt_extend_gt' V' Vh Hib Vl' Vhl Hil Hg Nb Hg' Gt Ec).
  rewrite{2}/btExtend; case: ifP.
  case: ifP; first by move/eqP=>F; rewrite F in Nb; move/eqP: Nb.
  by move=>B A; contradict V'; rewrite/btExtend B A valid_undef.
  have V0: valid (foldl btExtend bt bs) by rewrite -Ec.
  move=>Nd; move: (btExtend_dom_fold V0); rewrite -Ec.
  have Nb': (#b \notin dom cbt) by rewrite Nd.
  move=>S; rewrite/btExtend; case: ifP.
  by move=>D; specialize (S _ D); rewrite S in Nd.
  move=>Nd'.
  move: (complete_bt_extend_gt' V' Vh Hib Vl' Vhl Hil Hg Nb' Hg' Gt Ec).
  by rewrite/btExtend Nd' Nd.

have Q : cbt = btExtend cbt b
  by rewrite/btHasBlock in Nb; move/andP: Nb=>[A B]; rewrite/btExtend A B.
rewrite Q Ec in Gt.
(* Gt is false *)
have Z: (btExtend (foldl btExtend bt bs) b =
         foldl btExtend (foldl btExtend bt bs) [:: b]) by [].
have Vz: valid (foldl btExtend (foldl btExtend bt bs) [:: b]) by rewrite -Ec.
move: (btExtend_fold_comm bs [::b] Vhl)=>Ez; rewrite Z Ez //= in Gt.
(* move: (btExtend_fold_comm bs [::b] Vl)=>/==>Z; rewrite Z in Gt. *)

(* Boring stuff *)
  (* have G1 : valid (btExtend bt b) by rewrite -(btExtendV bt b). *)
have G1: valid (foldl btExtend (btExtend bt b) bs).
  have XX: btExtend bt b = foldl btExtend bt [:: b] by [].
  by rewrite XX -Ez -Ec.
have G2 : validH (btExtend bt b) by apply: (btExtendH Vl Vhl).
have G3 : has_init_block (btExtend bt b) by apply btExtendIB.
by move/FCR_dual: (btExtend_fold_sameOrBetter G1 G2 G3); rewrite Gt.
Qed.

Lemma good_chains_subset_geq bt bt':
  valid bt -> validH bt -> has_init_block bt ->
  valid bt' -> validH bt' -> has_init_block bt' ->
  {subset good_chains bt <= good_chains bt' } ->
  btChain bt' >= btChain bt.
Proof.
move=>V Vh Ib V' Vh' Ib' S.
by specialize (S (btChain bt) (btChain_in_good_chains Ib));
   apply btChain_is_largest.
Qed.

Lemma geq_genesis bt :
  btChain bt >= [:: GenesisBlock].
Proof. by rewrite btChain_alt; apply foldr_better_mono. Qed.

Lemma btExtend_within_helper cbt bt b bs :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  valid_chain_block (btChain bt) b ->
  btChain cbt >= btChain (btExtend bt b) ->
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) > btChain cbt ->
  # b \notin dom cbt ->
  False.
Proof.
move=>V' Vh Hib Vl' Vhl Hil Hg Hg' T Geq P Ec Cont Nb.
move: (btExtendV V') (btExtendV Vl')=>V Vl.
case: (btExtend_good_split V' Vh Hib Hg Nb Hg')=>cs1[cs2][Eg][Eg'].
move: (btExtend_mint_good_valid Vl' Vhl Hil T (btChain_good bt) P)=>[Gb Tb].
move: (FCR_trans_eq2 Cont Geq)=>Gt'.
have v2': (validH (btExtend bt b)) by apply btExtendH.
have v3': (has_init_block (btExtend bt b)) by apply btExtendIB.

have R: (btChain (btExtend bt b) =
         foldr take_better_alt [:: GenesisBlock] (good_chains (btExtend bt b)))
  by rewrite btChain_alt.
rewrite !btChain_alt Eg Eg' -R in Geq Gt' Cont.

have H0: compute_chain (btExtend bt b) b \in good_chains (btExtend bt b).
  rewrite/good_chains mem_filter Gb Tb /=;
  rewrite/all_chains; apply/mapP; exists b=>//;
  apply/all_blocksP'; by [apply btExtendH| apply in_ext].
move: (btChain_is_largest H0)=>H; clear H0.
move: (FCR_trans_eq2 Gt' H)=>Gt; clear H.

have Eq: compute_chain (btExtend bt b) b = compute_chain (btExtend cbt b) b.
rewrite Ec -(@foldl1 _ _ btExtend (foldl _ _ _)) btExtend_fold_comm /= //.
apply/eqP; rewrite eq_sym; apply/eqP; apply btExtend_compute_chain_fold=>//.

have Z: (btExtend bt b = foldl btExtend bt [::b]) by [].
rewrite Z btExtendV_fold_comm ?Vh //= -Ec //=.

rewrite Eq in Gt. move: Gt.
rewrite foldl_foldr_better.
rewrite (foldl_better_extract (compute_chain (btExtend cbt b) b) cs1 cs2).
rewrite catA (@foldl_cat _ _ _ [:: GenesisBlock] (cs1 ++ cs2)) /=.
rewrite{1}/take_better_alt; case: ifP=>//;
last by move=>_ X; apply (FCR_nrefl X).
rewrite -Eq in Gt' Cont *=>H; clear Eq; move=>_.

(* Cont and H are contradictory *)
move: Cont.
rewrite foldl_foldr_better.
rewrite (foldl_better_extract (compute_chain (btExtend bt b) b) cs1 cs2).
rewrite catA (@foldl_cat _ _ _ [:: GenesisBlock] (cs1 ++ cs2)) /=.
rewrite -foldl_foldr_better in H *.
rewrite{1}/take_better_alt; case: ifP.
by move=>_ X; apply (FCR_nrefl X).
by move=>_ H'; apply (FCR_nrefl (FCR_trans H H')).
Qed.

Lemma btExtend_within cbt bt b bs :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  valid_chain_block (btChain bt) b ->
  btChain cbt >= btChain (btExtend bt b) ->
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) > btChain cbt -> False.
Proof.
move=>V' Vh Hib Vl' Vhl Hil Hg Hg' T Geq P Ec Cont.
move: (btExtendV V') (btExtendV Vl')=>V Vl.

case Nb: (b ∈ cbt); rewrite/btHasBlock in Nb.
by move/andP: Nb=>[A B]; rewrite/btExtend A B in Cont; apply: FCR_nrefl Cont.
(* Have to do this rubbish twice *)
move/nandP: Nb=>[]Nb.
by apply: (btExtend_within_helper V' Vh Hib Vl' Vhl Hil Hg Hg' T Geq P Ec Cont Nb).
have V0: valid (btExtend cbt b) by [].
contradict V0.
rewrite/btExtend; case: ifP=>//=.
case: ifP; first by move/eqP=>X; rewrite X in Nb; move/eqP: Nb.
by rewrite valid_undef.
clear Nb; move=>X; have Nb: (#b \notin dom cbt) by rewrite X.
by move: (btExtend_within_helper V' Vh Hib Vl' Vhl Hil Hg Hg' T Geq P Ec Cont Nb).
Qed.

Lemma btExtend_can_eq cbt bt b bs :
  valid (btExtend cbt b) -> validH cbt -> has_init_block cbt ->
  valid (btExtend bt b) -> validH bt -> has_init_block bt ->
  good_bt cbt -> good_bt (btExtend cbt b) ->
  valid_chain_block (btChain bt) b ->
  btChain cbt >= btChain (btExtend bt b) ->
  prevBlockHash b = # last GenesisBlock (btChain bt) ->
  cbt = foldl btExtend bt bs ->
  btChain (btExtend cbt b) = btChain cbt.
Proof.
move=>V Vh Hib Vl Vhl Hil Hg Hg' T Geq P Ec.
case: (btExtend_sameOrBetter V Vh Hib)=>//H1.
by move: (btExtend_within V Vh Hib Vl Vhl Hil Hg Hg' T Geq P Ec H1).
Qed.

End BtChainProperties.
