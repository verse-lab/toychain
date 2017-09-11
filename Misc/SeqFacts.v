From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
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

