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
  ~[bc <<= bc'] /\  ~[bc' <<= bc].

Lemma bc_fork_neq bc bc' :
  fork bc bc' -> bc != bc' = true.
Proof.
elim=> H1 H2. elim: bc H1 H2=>[|x xs Hi] H1 H2.
- by contradict H1; exists bc'.
elim: bc' H1 H2 Hi=>[|y ys Hi H1 H2 Hi'].
- by [].
case B: (x == y); rewrite eqseq_cons Bool.negb_true_iff Bool.andb_false_iff.
- right. move/eqP in B. subst x. rewrite/is_prefix in H2.
  apply/negbTE/negP; move/eqP=>G. apply: H2.
  by exists [::]; rewrite cats0 G.
- by left.
Qed.

Lemma bc_fork_sym bc bc' :
  fork bc bc' -> fork bc' bc.
Proof.
rewrite/fork. elim. move=>nbb' nb'b. split; by [].
Qed.

Lemma bc_fork_prefix a b c :
  fork a b -> [b <<= c] -> fork a c.
Proof.
rewrite/fork. elim=>H2 H1[x] H3. subst c.
elim: x b H1 H2=>[|x xs Hi] b H1 H2.
- by rewrite cats0.
rewrite -cat_rcons. apply: Hi=>H.
- by apply: H1; case: H=>z->; rewrite cat_rcons; eexists _.
- rewrite/is_prefix in H H1 H2.
case: H=>z. elim/last_ind: z=>[|zs z Hi].
- by rewrite cats0=>Z; subst a; apply: H1; exists [:: x]; rewrite cats1.
rewrite -rcons_cat=>/eqP. rewrite eqseq_rcons. move/andP=>[/eqP Z]/eqP Z'.
by subst x b; apply: H2; exists zs.
Qed.

Axiom btChain_fork :
  forall (bt : BlockTree) (bc : Blockchain) (b : Block),
  let: bc' := btChain (btExtend bt b) in
    btChain bt = bc ->
    b \notin bc ->
    prevBlockHash (bcLast bc') != hashB (bcLast bc) ->
    fork bc bc'.

End Forks.
