From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap.
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

Lemma in_seq {T : eqType} (x : T) (xs : seq T) :
  x \in xs -> exists fs ls, xs = fs ++ x :: ls.
Proof.
move=>H. elim: xs H; first done.
move=>h t Hi; rewrite in_cons; move/orP; case.
by move/eqP=>->; exists [::], t.
by move=>H; move: (Hi H); move=>[fs] [ls]=>->; exists (h :: fs), ls.
Qed.

Lemma in_rem_msg {T: eqType} p0 p ms (hs : seq T) :
  p0 \in hs -> p0 <> p ->
  p0 \in ms ++ seq.rem p hs.
Proof.
move=>iF0 E; rewrite mem_cat orbC; apply/orP; left.
suff N : (p0 != p) by rewrite (rem_neq N iF0).
by apply/negP=>/eqP Z; subst p0.
Qed.

Lemma keys_ord1 {K: ordType} {T} (j : K) (w : T) m :
  valid (j \\-> w \+ m) ->
  path ord j (keys_of m) ->
  keys_of (j \\-> w \+ m) = j :: (keys_of m).
Proof.
elim/gen_indf: m=>/=[||k v m Hi V' P' V P].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR keys0 um_keysPt.
rewrite -joinCA in V; move: (Hi (validR V))=>{Hi}Hi.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).  
apply: (eq_sorted (@trans K) (A K))=>//=; first by apply: keys_sorted.
rewrite joinCA in V.
apply: uniq_perm_eq=>/=; rewrite ?keys_uniq ?[_&&true]andbC//=.
- case: validUn V=>//_ _/(_ j).
  by rewrite um_domPt inE eqxx keys_dom=>/(_ is_true_true).
move=>z; rewrite !inE !keys_dom !domUn !inE V um_domPt inE eq_sym/=.
by rewrite (validR V)/= um_domPtUn V'/= um_domPt !inE.
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

Lemma keys_ord2 {K: ordType} {T} (j k : K) (w v : T) m:
  valid (k \\-> v \+ (j \\-> w \+ m)) ->
  path ord j (keys_of m) ->
  keys_of (pts j w \+ (k \\-> v \+ m)) =
  if ord j k then j :: keys_of (k \\-> v \+ m) else k :: j :: (keys_of m).
Proof.
have A: antisymmetric ord by move=>???/andP[]H1 H2; move: (nsym H1 H2).  
case: ifP=>X V P; rewrite joinCA in V.
- apply: (eq_sorted (@trans K) (A K))=>//=; first by apply: keys_sorted.
  + rewrite path_min_sorted ?(keys_sorted _)//.
    move=>z; rewrite keys_dom domUn inE (validR V) um_domPt inE -keys_dom/=.
    case/orP; first by move/eqP=><-.
    by move/(path_ord_sorted (keys_sorted m) P).
  apply: uniq_perm_eq=>/=; rewrite ?keys_uniq ?[_&&true]andbC//=.  
  + by case: validUn V=>//_ _/(_ j);
       rewrite um_domPt inE eqxx keys_dom=>/(_ is_true_true).  
  move=>z; rewrite !inE !keys_dom !domUn !inE V um_domPt inE eq_sym/=.
  by rewrite (validR V)/= um_domPtUn /= um_domPt !inE (validR V). 
apply: (eq_sorted (@trans K) (A K))=>//=; first by apply: keys_sorted.
- rewrite P andbC/=; case/orP: (total k j) X=>///orP[]; last by move=>->.
  move/eqP=>Z; subst j.
  case: validUn (V)=>//_ _/(_ k); rewrite um_domPt inE eqxx=>/(_ is_true_true).
  by rewrite domUn inE um_domPt inE eqxx/= andbC(validR V).
apply: uniq_perm_eq=>/=; rewrite ?keys_uniq ?[_&&true]andbC//=.
- rewrite joinCA in V; case: validUn (V)=>//_ _/(_ k).
  rewrite um_domPt inE eqxx keys_dom=>/(_ is_true_true)=>/negP N _.  
  apply/andP; split; last first.
  + case: validUn (validR V)=>//_ _/(_ j).
    by rewrite um_domPt inE eqxx=>/(_ is_true_true).
  rewrite inE keys_dom; apply/negP=>M; apply: N.
  by rewrite domUn inE (validR V) um_domPt inE eq_sym M.  
move=>z; rewrite !inE !keys_dom !domUn !inE V um_domPt inE eq_sym/=.
rewrite domUn inE (validR V)/= um_domPt inE eq_sym [k == z]eq_sym. 
by case: (j == z)=>//; case: (z == k).
Qed.

Lemma keys_insert {K: ordType} {T} (k : K) (v : T) m :
  valid (k \\-> v \+ m) ->
  exists ks1 ks2, keys_of m = ks1 ++ ks2 /\
                  keys_of (k \\-> v \+ m) = ks1 ++ k :: ks2.
Proof.
move=>V; elim/gen_indf: m V=>//[||j w m' Hi V' P V].
- by case: validUn=>//=_; rewrite valid_undef.
- by rewrite unitR keys0 um_keysPt; exists [::], [::].
move: (V); rewrite -joinCA=>/validR/Hi[ks1][ks2][E1]E2.
(* So, j < (keys_of m'), hence it goes at the head *)
rewrite (keys_ord1 V' P) E1 (keys_ord2 V P) !E1 E2.
case: ifP=>_; first by exists (j :: ks1), ks2. 
by exists [::], (j :: ks1 ++ ks2). 
Qed.
