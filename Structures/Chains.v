From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Strict version of the prefix *)
Definition is_strict_prefix {T: eqType} (bc bc' : seq T) :=
  exists b bc1, bc' = bc ++ (b :: bc1).

Notation "'[' bc1 '<<<' bc2 ']'" := (is_strict_prefix bc1 bc2).

Lemma isp_mt {T: eqType} (bc : seq T) : ~ is_strict_prefix bc [::].
Proof. by case=>b[bc1]; case: bc. Qed.

(* The corresponding checker *)
Fixpoint sprefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (sprefixb s1' s2')
    else true
  else false.         

Lemma sprefixP {T: eqType} (bc1 bc2 : seq T):
  reflect [bc1 <<< bc2] (sprefixb bc1 bc2).
Proof.
elim: bc2 bc1=>//=[|b2 bc2 Hi/=]bc1.
- case:bc1=>//=[|b1 bc1]; constructor 2=>//; apply: isp_mt.
case: bc1=>//[|b1 bc1]/=; first by constructor 1; exists b2, bc2.  
case X: (b1 == b2)=>/=; last first.
- constructor 2=>[[p]][bc']; rewrite cat_cons; case=>Z; subst b2.
  by rewrite eqxx in X.
- move/eqP: X=>X; subst b2.
case: Hi=>H; [constructor 1|constructor 2].
- by case:H=>x[xs]->; exists x, xs; rewrite cat_cons.  
case=>x[xs]; rewrite cat_cons; case=>Z; subst bc2; apply: H.
by exists x, xs.
Qed.

(* Non-strict prefix *)
Definition is_prefix {T :eqType} (bc bc' : seq T) :=
  exists bc1, bc' = bc ++ bc1.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).

Lemma bc_pre_refl {T :eqType} (bc : seq T) : [bc <<= bc].
Proof. by exists [::]; rewrite cats0. Qed.

Lemma bc_pre_trans {T :eqType} (bc1 bc2 bc3 : seq T) :
  [bc1 <<= bc2] -> [bc2 <<= bc3] -> [bc1 <<= bc3].
Proof.
case=> a1 H1 [a2] H2; subst bc2.
by rewrite -catA in H2; exists (a1 ++ a2).
Qed.

Lemma bc_spre_nrefl {T :eqType} (bc : seq T) : ~ [bc <<< bc].
Proof.
move=>[h][t]. elim: bc=>[|x xs H]; do? by[rewrite cat0s|case].
Qed.

Lemma bc_spre_trans {T :eqType} (bc1 bc2 bc3 : seq T) :
  [bc1 <<< bc2] -> [bc2 <<< bc3] -> [bc1 <<< bc3].
Proof.
move=>[x][xs]eq [y][ys]eq'. rewrite eq' eq. clear eq eq'.
rewrite/is_strict_prefix. eexists x, (xs ++ y :: ys).
by rewrite -catA.
Qed.

Lemma bc_spre_pre {T :eqType} (bc bc' : seq T) :
  [bc <<< bc'] -> [bc <<= bc'].
Proof. by move=>[] x [] xs=>->; exists (x :: xs). Qed.

Lemma bc_pre_spre {T :eqType} (bc bc' : seq T) :
  [bc <<= bc'] -> [bc <<< bc'] \/ bc == bc'.
Proof.
case; case; first by rewrite cats0=>->; right. 
by move=>x xs->; left; eexists x, xs.
Qed.

Lemma bc_pre_both {T :eqType} (bc1 bc2 : seq T) :
  [bc1 <<= bc2] -> [bc2 <<= bc1] -> bc1 == bc2.
Proof.
move=>H1 H2. move: (bc_pre_spre H1) (bc_pre_spre H2). clear H1 H2.
case=>A; case=>B; do? by [].
by move: (bc_spre_nrefl (bc_spre_trans A B)).
by rewrite eq_sym.
Qed.

Lemma bc_spre_both {T :eqType} (bc1 bc2 : seq T) :
  sprefixb bc1 bc2 -> sprefixb bc2 bc1 -> False.
Proof.
by move/sprefixP=>A /sprefixP=>B; move: (bc_spre_nrefl (bc_spre_trans A B)).
Qed.

Lemma bc_prefix_mt {T :eqType} (bc : seq T) : [bc <<= [::]] -> bc == [::].
Proof. by case: bc=>//b bc[x]. Qed.

Lemma bc_sprefix_mt {T :eqType} (bc : seq T) : [bc <<< [::]] -> False.
Proof. by case=>x [] xs; case: bc=>//b bc[x]. Qed.
 
Fixpoint prefixb {T: eqType} (s1 s2 : seq T) :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then (x == y) && (prefixb s1' s2')
    else true
  else s1 == [::].         

Lemma bc_prefixb_mt {T :eqType} (bc : seq T) : prefixb bc [::] -> bc == [::].
Proof. by case: bc=>//b bc[x]. Qed.

Lemma prefixP {T :eqType} (bc1 bc2 : seq T):
  reflect [bc1 <<= bc2] (prefixb bc1 bc2).
Proof.
elim: bc2 bc1=>//=[|b2 bc2 Hi/=]bc1.
- case B: (prefixb bc1 [::]); [constructor 1|constructor 2].
  + by move/bc_prefixb_mt/eqP: B=>->; exists [::].
  by case: bc1 B=>//b bc1/=_[?].
case: bc1=>//[|b1 bc1]; first by constructor 1; exists (b2::bc2). 
case X: (b1 == b2)=>/=; rewrite X/=; last first.
- constructor 2=>[[p]]; rewrite cat_cons; case=>Z; subst b2.
  by rewrite eqxx in X.
- move/eqP: X=>X; subst b2.
case: Hi=>H; [constructor 1|constructor 2].
- by case:H=>x->; exists x; rewrite cat_cons.  
case=>t; rewrite cat_cons; case=>Z; subst bc2; apply: H.
by exists t.
Qed.

Lemma prb_equiv {T: eqType} (bc1 bc2 : seq T) :
  prefixb bc1 bc2 = (bc1 == bc2) || (sprefixb bc1 bc2).
Proof.
apply/Bool.eq_iff_eq_true; split.
- move/prefixP=>[x]->; case: x=>[|x xs]; first by rewrite cats0 eqxx.
  by apply/orP; right; apply/sprefixP; exists x, xs.
- move/orP; case.
  by move/eqP=><-; apply/prefixP; apply bc_pre_refl.
  by move/sprefixP=>[] x [] xs eq; apply/prefixP; rewrite eq; exists (x :: xs).
Qed.

Notation "'[' bc1 '<<=' bc2 ']'" := (is_prefix bc1 bc2).
Notation "'[' bc1 '<<<' bc2 ']'" := (is_strict_prefix bc1 bc2).

(* Decidable fork *)
Definition fork {T: eqType} (bc1 bc2 : seq T) :=
  ~~[|| sprefixb bc1 bc2, sprefixb bc2 bc1 | bc1 == bc2].

Definition fork_rel {T: eqType} (bc1 bc2 : seq T) :=
  ~ ([bc1 <<= bc2] \/ [bc2 <<= bc1]).

Lemma forkP {T: eqType} (bc1 bc2 : seq T) :
  reflect (fork_rel bc1 bc2) (fork bc1 bc2).
Proof.
case F: (fork bc1 bc2); [constructor 1 | constructor 2].
- move/negP: F=>F; rewrite /fork_rel=>G; apply: F.
  case: G; case=>xs; case: xs=>[| x xs]; rewrite ?cats0=>->;
  do? [by rewrite eqxx ![_ || true]orbC].
  + by apply/orP; left; apply/sprefixP; eexists _, _.  
  by apply/orP; right; apply/orP; left; apply/sprefixP; eexists _, _.
move=>G. move/negP: F=>F;apply: F. rewrite /fork_rel in G.
case/orP.
- move/sprefixP=>[x][xs]E; apply: G; subst bc2.
  by left; eexists _.
  by rewrite orbC eq_sym -prb_equiv=>P21; apply: G; right; apply/prefixP.
Qed.

Lemma bc_fork_neq {T: eqType} (bc bc' : seq T) :
  fork bc bc' -> bc != bc'.
Proof.
move=>H; apply/negbT/negP=>Z; move/eqP:Z=>Z; subst bc'.
by case/orP: H; right; rewrite orbC eqxx. 
Qed.

Lemma bc_fork_nrefl {T: eqType} (bc : seq T) :
  fork bc bc -> False.
Proof. by move=>H; move: (bc_fork_neq H); move/eqP. Qed.

Lemma bc_fork_sym {T: eqType} (bc bc' : seq T) :
  fork bc bc' -> fork bc' bc.
Proof.
by rewrite/fork; rewrite eq_sym orbCA.
Qed.

Lemma bc_fork_prefix {T: eqType} (a b c : seq T):
  fork a b -> [b <<= c] -> fork a c.
Proof.
move/forkP=>F H; apply/forkP; move: F H.
move/Decidable.not_or.
case=>H2 H1[x] H3; subst c.
elim: x b H1 H2=>[|x xs Hi] b H1 H2.
- by rewrite cats0; case=>H; [apply: H2|apply:H1].
rewrite -cat_rcons; apply: Hi=>H.
- by apply: H1; case: H=>z->; rewrite cat_rcons; eexists _.
- rewrite/is_prefix in H H1 H2.
case: H=>z. elim/last_ind: z=>[|zs z Hi].
- by rewrite cats0=>Z; subst a; apply: H1; exists [:: x]; rewrite cats1.
rewrite -rcons_cat=>/eqP; rewrite eqseq_rcons; move/andP=>[/eqP Z]/eqP Z'.
by subst x b; apply: H2; exists zs.
Qed.

Inductive bc_rel {T : eqType} (bc bc' : seq T) : bool-> bool-> bool-> bool-> Set :=
| CmpBcEq of bc == bc' : bc_rel bc bc' true false false false
| CmpBcFork of fork bc bc' : bc_rel bc bc' false true false false
| CmpBcPre12 of sprefixb bc bc' : bc_rel bc bc' false false true false
| CmpBcPre21 of sprefixb bc' bc: bc_rel bc bc' false false false true.

Lemma bc_relP {T : eqType} (bc bc' : seq T) :
  bc_rel bc bc' (bc == bc') (fork bc bc') (sprefixb bc bc') (sprefixb bc' bc).
Proof.
case Eq: (bc == bc'); case F: (fork bc bc');
case S12: (sprefixb bc bc'); case S21: (sprefixb bc' bc);
do? by [
  constructor |
  contradict Eq; move: (bc_fork_neq F)=>/eqP=>A B; apply A; move/eqP in B |
  contradict Eq; move: (bc_spre_both S12 S21) |
  contradict S12; move/eqP: Eq=><-=>/sprefixP; apply: bc_spre_nrefl |
  contradict S21; move/eqP: Eq=><-=>/sprefixP; apply: bc_spre_nrefl
].
- by contradict F; move/norP=>[] C; rewrite S12 in C.
- by contradict F; move/norP=>[] _=>/norP; elim=>C; rewrite S21 in C.
- by contradict F; rewrite/fork Eq S12 S21.
Qed.
