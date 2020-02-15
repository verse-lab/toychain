From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.

Set Implicit Arguments.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

(***************************************************)
(*        Some useful facts about lists            *)
(***************************************************)

Lemma rem_neq {T: eqType} (x y : T) (ls : seq T) :
  x != y -> x \in ls -> x \in seq.rem y ls.
Proof.
move=>N; elim: ls=>//h ls Hi.
rewrite inE; case/orP=>//=.
- by move/eqP=>Z; subst h; move/negbTE: N=>->; rewrite inE eqxx.
by case: ifP=>//=N' /Hi; rewrite inE orbC=>->.
Qed.

Lemma rem_neq_notin {T: eqType} (x y : T) (ls : seq T) :
  x != y -> x \notin ls -> x \notin seq.rem y ls.
Proof.
move=>N; elim: ls=>//h ls Hi.
rewrite inE; case/norP=>//=.
move=>Neq Ni; specialize (Hi Ni); case: ifP=>//=.
by move=>Hy; rewrite inE; apply/norP; rewrite Hi.
Qed.

Lemma in_seq {T : eqType} (x : T) (xs : seq T) :
  x \in xs -> exists fs ls, xs = fs ++ x :: ls.
Proof.
move=>H. elim: xs H; first done.
move=>h t Hi; rewrite in_cons; move/orP; case.
by move/eqP=>->; exists [::], t.
by move=>H; move: (Hi H); move=>[fs] [ls]=>->; exists (h :: fs), ls.
Qed.

Lemma in_seq_neq {T : eqType} (x : T) (xs : seq T) :
  x \in xs -> exists fs ls, xs = fs ++ x :: ls /\ x \notin fs.
Proof.
move=>H. elim: xs H; first done.
move=>h t Hi; rewrite in_cons; move/orP; case.
by move/eqP=>->; exists [::], t.
move=>H; move: (Hi H); move=>[fs][ls][->]G.
case E: (x == h); last first.
- by exists (h :: fs), ls; split; rewrite ?cat_cons// inE E G.
by exists [::], (fs ++ x :: ls); split; move/eqP:E=>->.
Qed.

Lemma in_seq_excl {T : eqType} (x y : T) (xs : seq T) :
  x \in xs -> y \notin xs -> x != y.
Proof.
elim: xs=>[|h tl Hi]//.
rewrite !in_cons; case/orP=> H; case/norP=>H0.
by move/eqP in H; subst h=>_; rewrite eq_sym.
by move=> H'; apply (Hi H H').
Qed.
 
Lemma rem_elem {T: eqType} (p : T) xs ys :
  p \notin xs-> seq.rem p (xs ++ p :: ys) = xs ++ ys.
Proof.
elim: xs=>//=; first by rewrite eqxx.
move=>x xs Hi; rewrite inE=>/norP[H1 H2].
by move/negbTE: H1; rewrite eq_sym=>->; rewrite (Hi H2).
Qed.

Lemma in_rem_msg {T: eqType} p0 p ms (hs : seq T) :
  p0 \in hs -> p0 <> p ->
  p0 \in ms ++ seq.rem p hs.
Proof.
move=>iF0 E; rewrite mem_cat orbC; apply/orP; left.
suff N : (p0 != p) by rewrite (rem_neq N iF0).
by apply/negP=>/eqP Z; subst p0.
Qed.

Lemma dom_ord1 {K: ordType} {T} (j : K) (w : T) m :
  valid (j \\-> w \+ m) ->
  path ord j (dom m) ->
  dom (j \\-> w \+ m) = j :: (dom m).
Proof.
elim/um_indf: m=>/=[||k v m Hi V' P' V P].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR dom0 domPtK.
rewrite -joinCA in V; move: (Hi (validR V))=>{Hi}Hi.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).  
apply: (eq_sorted (@trans K) (A K))=>//=.
rewrite joinCA in V.
apply: uniq_perm_eq=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
- case: validUn V=>//_ _/(_ j).
  by rewrite domPtK inE eqxx uniq_dom=>/(_ is_true_true) ? ?; apply/andP.
move=>z; rewrite !inE !domUn !inE V domPtK inE (eq_sym z k).
by rewrite (validR V)/= domPtUn V'/= domPtK !inE.
Qed.

Lemma path_ord_sorted {K: ordType} z j (l : seq K) :
  sorted ord l -> path ord j l -> z \in l -> ord j z.
Proof.
elim: l z=>//h l Hi z/=P/andP[O _].
rewrite inE; case/orP; first by move/eqP=>->.
move=>I; apply: Hi=>//; first by apply:(path_sorted P).
clear I z; case: l O P=>//=x xs O/andP[O' ->]; rewrite andbC/=.
by apply: (@trans K _ _ _ O O').
Qed.

Lemma dom_ord2 {K: ordType} {T} (j k : K) (w v : T) m:
  valid (k \\-> v \+ (j \\-> w \+ m)) ->
  path ord j (dom m) ->
  dom (pts j w \+ (k \\-> v \+ m)) =
  if ord j k then j :: dom (k \\-> v \+ m) else k :: j :: (dom m).
Proof.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).
case: ifP=>X V P; rewrite joinCA in V.
- apply: (eq_sorted (@trans K) (A K))=>//=.
  + rewrite path_min_sorted//.
    apply/allP=>z.
    rewrite domUn inE (validR V) domPtK inE /=.
    case/orP; first by move/eqP=>->.
    by move/(path_ord_sorted (sorted_dom m) P).
  apply: uniq_perm_eq=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
  + by case: validUn V=>//_ _/(_ j);
       rewrite domPtK inE eqxx=>/(_ is_true_true) ? ?; apply/andP.
  move=>z; rewrite !inE !domUn !inE V domPtK inE /=.
  by rewrite (validR V)/= domPtUn /= domPtK !inE (validR V) (eq_sym z k).
apply: (eq_sorted (@trans K) (A K))=>//=.
- rewrite P andbC/=; case/orP: (total k j) X=>///orP[]; last by move=>->.
  move/eqP=>Z; subst j.
  case: validUn (V)=>//_ _/(_ k); rewrite domPtK inE eqxx=>/(_ is_true_true).
  by rewrite domUn inE domPtK inE eqxx/= andbC(validR V).
apply: uniq_perm_eq=>/=; rewrite ?dom_uniq ?[_&&true]andbC//=.
- rewrite joinCA in V; case: validUn (V)=>//_ _/(_ k).
  rewrite domPtK inE eqxx=>/(_ is_true_true)=>/negP N _.
  apply/andP; split; last first.
  + case: validUn (validR V)=>//_ _/(_ j).
    by rewrite domPtK inE eqxx=>/(_ is_true_true) ? ?; apply/andP.
  rewrite inE; apply/negP=>M; apply: N.
  by rewrite domUn inE (validR V) domPtK inE.
move=>z; rewrite !inE !domUn !inE V domPtK inE eq_sym/=.
rewrite domUn inE (validR V)/= domPtK inE.
by case: (j == z)=>//; case: (z == k).
Qed.

Lemma dom_insert {K: ordType} {T} (k : K) (v : T) m :
  valid (k \\-> v \+ m) ->
  exists ks1 ks2, dom m = ks1 ++ ks2 /\
                  dom (k \\-> v \+ m) = ks1 ++ k :: ks2.
Proof.
move=>V; elim/um_indf: m V=>//[||j w m' Hi V' P V].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR dom0 domPtK; exists [::], [::].
move: (V); rewrite -joinCA=>/validR/Hi[ks1][ks2][E1]E2.
(* So, j < (dom m'), hence it goes at the head *)
rewrite (dom_ord1 V' P) E1 (dom_ord2 V P) !E1 E2.
case: ifP=>_; first by exists (j :: ks1), ks2. 
by exists [::], (j :: ks1 ++ ks2). 
Qed.
