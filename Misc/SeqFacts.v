From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.

Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma rem_neq {T: eqType} (x y :T) (ls : seq T) :
  x != y -> x \in ls -> x \in seq.rem y ls.
Proof.
move=>N; elim: ls=>//h ls Hi.
rewrite inE; case/orP=>//=.
- by move/eqP=>Z; subst h; move/negbTE: N=>->; rewrite inE eqxx.
by case: ifP=>//=N' /Hi; rewrite inE orbC=>->.        
Qed.