From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
From fcsl
Require Import ordtype unionmap.
From Toychain
Require Import Types Parameters Address.
Require Import BinNat BinNatDef.
Require Import HexString String Ascii.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NEq.
Lemma eq_NP : Equality.axiom N.eqb.
Proof.
case=>[x|p x]//=; case: x.
by constructor 1; apply N.Private_Tac.eq_refl.
by constructor 2.
by constructor 2.
move=>p'; case X: (BinPos.Pos.eqb p p').
by constructor 1; move/BinPos.Peqb_true_eq: X=>->.
by constructor 2; case; move/BinPos.Pos.eqb_neq: X.
Qed.
End NEq.


Section NOrd.
Lemma irr_ltbN : irreflexive N.ltb.
Proof. by case=>[|n]//; apply N.ltb_irrefl. Qed.

Lemma trans_ltbN : transitive N.ltb.
Proof.
by move=>x y z; move=>/N.ltb_lt A /N.ltb_lt B;
   apply/N.ltb_lt; move: (N.lt_trans _ _ _ A B).
Qed.

Lemma total_ltbN x y : [|| N.ltb x y, x == y | N.ltb y x].
Proof.
apply/or3P; case: (N.compare_spec x y).
by move=>->; constructor 2.
by constructor 1; apply/N.ltb_lt.
by constructor 3; apply/N.ltb_lt.
Qed.

Definition N_ordMixin := Eval hnf in OrdMixin irr_ltbN trans_ltbN total_ltbN.
Canonical N_ordType := Eval hnf in OrdType N N_ordMixin.
End NOrd.

Section StringEq.

(* Define so we can reuse proofs from above *)
Definition ascii_eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
   (a0 == b0) && (a1 == b1) && (a2 == b2) && (a3 == b3)
   && (a4 == b4) && (a5 == b5) && (a6 == b6) && (a7 == b7)
 end.

Lemma ascii_eqP : Equality.axiom ascii_eqb.
Proof.
case=>a0 a1 a2 a3 a4 a5 a6 a7; case=>b0 b1 b2 b3 b4 b5 b6 b7.
rewrite/ascii_eqb.
(case:a0;case:b0=>/=; do? by constructor);
(case:a1;case:b1=>/=; do? by constructor);
(case:a2;case:b2=>/=; do? by constructor);
(case:a3;case:b3=>/=; do? by constructor);
(case:a4;case:b4=>/=; do? by constructor);
(case:a5;case:b5=>/=; do? by constructor);
(case:a6;case:b6=>/=; do? by constructor);
(case:a7;case:b7=>/=; do? by constructor).
Qed.

Definition ascii_eqMixin := EqMixin ascii_eqP.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.

Fixpoint string_eqb (s1 s2 : string): bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ascii_eqb c1 c2 && string_eqb s1' s2'
 | _,_ => false
end.

Lemma ascii_eqb_refl x : ascii_eqb x x.
Proof. by case: x=>b0 b1 b2 b3 b4 b5 b6 b7//=; rewrite !eq_refl. Qed.

Lemma string_eqP : Equality.axiom string_eqb.
Proof.
rewrite/Equality.axiom=>s1; elim: s1; first by case; constructor.
move=>x xs Hi; case; first by constructor.
move=>y ys; case E: (x == y).
- move/eqP in E; rewrite -E//=.
  rewrite ascii_eqb_refl//=; move: (Hi ys).
  case; first by move=>->; constructor.
  by move=>X; constructor; case.
move/eqP in E; have X: (String x xs <> String y ys) by case.
specialize (Hi ys); rewrite/string_eqb.
case Q: (ascii_eqb x y)=>//=.
by move: (ascii_eqP x y Q).
by constructor.
Qed.

Definition string_eqMixin := EqMixin string_eqP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
End StringEq.

Section StringOrd.

Lemma ascii_eqb_N x y :
  ascii_eqb x y = (N_of_ascii x == N_of_ascii y).
Proof.
case E: (x == y); first by move/eqP: E=>->; rewrite ascii_eqb_refl eq_refl.
have X: (ssrfun.cancel N_of_ascii ascii_of_N)
  by move=>z; apply ascii_N_embedding.
move: (can_eq X x y)=>->; rewrite E.
case Z: (ascii_eqb x y)=>//.
by move: (ascii_eqP x y Z); move/eqP: E.
Qed.

Definition ascii_ltb (a b : ascii) : bool := N.ltb (N_of_ascii a) (N_of_ascii b).

Lemma irr_ascii : irreflexive ascii_ltb.
by rewrite/irreflexive/ascii_ltb=>x; apply irr_ltbN.
Qed.

Lemma trans_ascii : transitive ascii_ltb.
by rewrite/transitive/ascii_ltb=>x y z; apply trans_ltbN.
Qed.

Lemma total_ascii x y : [|| ascii_ltb x y, x == y | ascii_ltb y x].
Proof.
rewrite/ascii_ltb.
suff X: ((x == y) = (N_of_ascii x == N_of_ascii y))
  by rewrite X; apply total_ltbN.
case Q: (x == y); first by move/eqP: Q=>->; rewrite eq_refl.
rewrite -ascii_eqb_N; case X: (ascii_eqb x y)=>//=.
by move: (ascii_eqP x y X); move/eqP: Q.
Qed.

Definition ascii_ordMixin := OrdMixin irr_ascii trans_ascii total_ascii.
Canonical Structure ascii_ordType := Eval hnf in OrdType ascii ascii_ordMixin.


(* Make use of embedding string -> seq ascii;
   This way, we can reuse the proofs from above.
   For some reason, Strings.v doesn't export this; so have to copy/paste.
*)
Fixpoint string_of_list_ascii (s : list ascii) : string
  := match s with
     | nil => EmptyString
     | cons ch s => String ch (string_of_list_ascii s)
     end.

Fixpoint list_ascii_of_string (s : string) : list ascii
  := match s with
     | EmptyString => nil
     | String ch s => cons ch (list_ascii_of_string s)
end.

Lemma embedding_list_ascii s : string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s as [|? ? IHs]; [ reflexivity | cbn; apply f_equal, IHs ].
Defined.

Definition string_ltb (s1 s2 : string): bool :=
  ords (list_ascii_of_string s1) (list_ascii_of_string s2).

Lemma irr_string : irreflexive string_ltb.
Proof. by elim=>[|c s x]; apply irr_ords. Qed.

Lemma trans_string : transitive string_ltb.
Proof.
by rewrite/transitive=>x y z; rewrite/string_ltb; apply trans_ords.
Qed.

Lemma total_string x y : [|| string_ltb x y, x == y | string_ltb y x].
Proof.
case X: ((x == y) == (list_ascii_of_string x == list_ascii_of_string y)).
by move/eqP in X; rewrite X; rewrite/string_ltb; apply total_ords.
have E: ssrfun.cancel list_ascii_of_string string_of_list_ascii .
  by move=>z; apply embedding_list_ascii.
by move: (can_eq E x y)=>X'; move: X; rewrite X' eq_refl.
Qed.

Definition string_ordMixin := OrdMixin irr_string trans_string total_string.
Canonical Structure string_ordType := Eval hnf in OrdType string string_ordMixin.

End StringOrd.


(** Instantiate the types *)
Module TypesImpl <: Types.
Definition Timestamp := N.
Definition Hash := string.
Definition VProof := N.
Definition Transaction := string.

(* XXX Having to do this is immensely annoying. Is there a better way? *)
Definition Hl (a b : Hash) := string_ltb a b.
Lemma irr_Hl : irreflexive Hl. Proof. by apply irr_string. Qed.
Lemma trans_Hl : transitive Hl. Proof. by apply trans_string. Qed.
Lemma total_Hl x y : [|| Hl x y, x == y | Hl y x]. Proof. by apply total_string. Qed.

Definition Hash_eqMixin := Eval hnf in EqMixin string_eqP.
Canonical Hash_eqType := Eval hnf in EqType Hash Hash_eqMixin.
Definition Hash_ordMixin := Eval hnf in OrdMixin irr_Hl trans_Hl total_Hl.
Canonical Hash_ordType := Eval hnf in OrdType Hash Hash_ordMixin.

Definition Vl (a b : VProof) := N.ltb a b.
Lemma irr_Vl : irreflexive Vl. Proof. by apply irr_ltbN. Qed.
Lemma trans_Vl : transitive Vl. Proof. by apply trans_ltbN. Qed.
Lemma total_Vl x y : [|| Vl x y, x == y | Vl y x]. Proof. by apply total_ltbN. Qed.

Canonical VProof_eqMixin := Eval hnf in EqMixin eq_NP.
Canonical VProof_eqType := Eval hnf in EqType VProof VProof_eqMixin.
Canonical VProof_ordMixin := Eval hnf in OrdMixin irr_Vl trans_Vl total_Vl.
Canonical VProof_ordType := Eval hnf in OrdType VProof VProof_ordMixin.

Definition Tl (a b : Transaction) := string_ltb a b.
Lemma irr_Tl : irreflexive Hl. Proof. by apply irr_string. Qed.
Lemma trans_Tl : transitive Hl. Proof. by apply trans_string. Qed.
Lemma total_Tl x y : [|| Tl x y, x == y | Tl y x]. Proof. by apply total_string. Qed.

Definition Transaction_eqMixin := Eval hnf in EqMixin string_eqP.
Canonical Transaction_eqType := Eval hnf in EqType Transaction Transaction_eqMixin.
Definition Transaction_ordMixin := Eval hnf in OrdMixin irr_Tl trans_Tl total_Tl.
Canonical Transaction_ordType := Eval hnf in OrdType Transaction Transaction_ordMixin.

Record Block  :=
  mkB {
    prevBlockHash : Hash;
    txs : seq Transaction;
    proof : VProof;
  }.

Definition eq_block b b':=
  match b, b' with
  | mkB p t pf, mkB p' t' pf' =>
    [&& p == p', t == t' & pf == pf']
  end.

Lemma eq_blockP : Equality.axiom eq_block.
Proof.
case=> p t pf; case=> p' t' pf'; rewrite /eq_block/=.
case H2: (p == p'); [move/eqP: H2=>?; subst p'| constructor 2];
  last by case=>?; subst p';rewrite eqxx in H2.
case H3: (t == t'); [move/eqP: H3=>?; subst t'| constructor 2];
  last by case=>?; subst t';rewrite eqxx in H3.
case H4: (pf == pf'); [move/eqP: H4=>?; subst pf'| constructor 2];
  last by case=>?; subst pf';rewrite eqxx in H4.
by constructor 1.
Qed.

Definition Block_eqMixin := Eval hnf in EqMixin eq_blockP.
Canonical Block_eqType := Eval hnf in EqType Block Block_eqMixin.

Lemma eq_block_fields b b':
  prevBlockHash b == prevBlockHash b' ->
  txs b == txs b' ->
  proof b == proof b' ->
  b == b'.
Proof.
by case: b=>b0 b1 b2; case: b'=> b0' b1' b2'=>//=; move=>/eqP -> /eqP -> /eqP ->.
Qed.

(* Do not confuse with FCR, which is what the protocol actually uses.
   This is a tie-breaker in case two blockchains have the same total work. *)
Definition block_ltb b b' :=
  let eA := txs b == txs b' in
  let eB := prevBlockHash b == prevBlockHash b' in
  let eC := proof b == proof b' in
  let A := ords (txs b) (txs b') in
  let B := Hl (prevBlockHash b) (prevBlockHash b') in
  let C := Vl (proof b) (proof b') in

  match eA, eB, eC with
  | true, true, true => false
  | true, true, false => C
  | true, _, _ => B
  | false, _, _ => A
  end.

  (* The definition above seems like overkill, but is actually minimal
      wrt. being provably both transitive and total. The one below is
      total, but not transitive:

        [|| ords (txs b) (txs b'), Hl (prevBlockHash b) (prevBlockHash b') |
                Vl (proof b) (proof b')].
   *)

Lemma irr_bl : irreflexive block_ltb.
Proof. by move=>x; rewrite/block_ltb !eq_refl. Qed.

Lemma trans_bl : transitive block_ltb.
Proof.
move=>x y z; rewrite/block_ltb; case: ifP; case: ifP; case: ifP=>//=;
move=> A B C D; (do? rewrite A; do? rewrite B; do? rewrite C; do? rewrite D).
- case: ifP; case: ifP=>//=.
  case: ifP; case: ifP=>//=.
  case: ifP. case: ifP.
    by move/eqP=><- _ _ _ _ _ D'; move: (trans_Vl D D') (irr_Vl (proof y))=>->.
    by move=>_ _ _ _ _ _ D'; move: (trans_Vl D D').
    by move/eqP: B=>-> ->.
    by move/eqP: C=>-> ->.
    by move/eqP in C; move/eqP in B; rewrite B C=>-> ->.
    by move/eqP: C=>-> /eqP -> /eqP.
    by move/eqP: C=>->.
- case: ifP; case: ifP=>//=.
  case: ifP. case: ifP. case: ifP;
    by move=>_ /eqP <- _ _ /eqP B'; rewrite B' in B; move/eqP: B.
    by move=>_ _ _ /eqP X; move: X D=>->.
    by move/eqP: A; move/eqP: C=>->->/eqP.
  case: ifP. case: ifP;
    by move=>_/eqP <- _ _ D'; move: (trans_Hl D' D) (irr_Hl (prevBlockHash x))=>->.
    by move=>_ _ _ D'; move: (trans_Hl D D').
    by move/eqP: A; move/eqP: C=>->-> /eqP.
- case: ifP. case: ifP. case: ifP;
    by move=>_ _ /eqP; move/eqP: C=>-> A'; rewrite A' eq_refl in A.
    by move=>_ /eqP; move/eqP: C=>-> A'; rewrite A' eq_refl in A.
    by move/eqP: C=>->.
- case: ifP=>//=. case: ifP.
  by move/eqP in B; rewrite B in C; rewrite C.
  by move/eqP: B=><-.
- by move/eqP  in B; rewrite B in C; rewrite C; rewrite B in D.
- by move: D; move/eqP: A=>-> X Y; move: (trans_ords X Y) (irr_ords (txs z))=>->.
by apply trans_ords.
Qed.

Lemma total_bl x y : [|| block_ltb x y, x == y | block_ltb y x].
Proof.
rewrite/block_ltb.
case: ifP; case: ifP.
- case: ifP; case: ifP.
  by move=>_ B C A; move: (eq_block_fields C A B)=>/eqP ->; rewrite !eq_refl.
  by move=>A _ _ /eqP A'; rewrite A' in A; move/eqP: A.
  move=>_ B /eqP C A; rewrite C eq_refl (eq_sym (proof _)) B;
  case/or3P: (total_Vl (proof x) (proof y)); first by move=>->.
    by move/eqP=>B'; rewrite B' in B; move/eqP: B.
    by move=>->; apply/or3P; constructor 3.
  by move=>A _ _ /eqP A'; rewrite A' in A; move/eqP: A.
- case: ifP. case: ifP. case: ifP;
  by move=>_ /eqP ->; rewrite eq_refl.
  case/or3P: (total_Hl (prevBlockHash x) (prevBlockHash y)).
    by move=>->.
    by move/eqP=>->; rewrite eq_refl.
    by move=>-> _ _ _ _; apply/or3P; constructor 3.
  by move=>A _ /eqP A'; rewrite A' in A; move/eqP: A.
- by move/eqP=>->; rewrite eq_refl.
- move=>_ X; case/or3P: (total_ords (txs x) (txs y)).
  by move=>->.
  by move/eqP=>X'; rewrite X' in X; move/eqP: X.
  by move=>->; apply/or3P; constructor 3.
Qed.

Definition block := Block.
Definition block_ordMixin := Eval hnf in OrdMixin irr_bl trans_bl total_bl.
Canonical block_ordType := Eval hnf in OrdType block block_ordMixin.

Definition Blockchain := seq block.

Definition TxPool := seq Transaction.
Definition BlockTree := union_map [ordType of Hash] block.
End TypesImpl.
