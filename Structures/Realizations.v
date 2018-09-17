From mathcomp.ssreflect
Require Import ssrnat eqtype choice fintype.

From fcsl
Require Import ordtype.

Section Params.
    Parameter Hash: Type.
    Parameter VProof : Type.
    
    Structure Address: Type := mkAddr {
        ip:nat*nat*nat*nat;
        port:nat
    }.

    Structure Transaction:Type := mkTx {
        source : Address;
        destination : Address;
        val:nat
    }.
End Params.

Section Canonicals.
Search "eqType".
    Definition VProof_eqMixin : Equality.mixin_of VProof. Admitted.
    Canonical VProof_eqType := EqType VProof VProof_eqMixin.

    Definition Hash_eqMixin : Equality.mixin_of Hash. Admitted.
    Canonical Hash_eqType := EqType Hash Hash_eqMixin.

    Definition Hash_ordMixin : Ordered.mixin_of Hash_eqType. Admitted.
    Canonical Hash_ordType := OrdType Hash Hash_ordMixin.

    Definition addr_eq (a b: Address):bool := andb (ip a == ip b) (port a == port b).

    Lemma eq_addrP : Equality.axiom addr_eq. 
    Admitted.

    Canonical Address_eqMixin:= Eval hnf in EqMixin eq_addrP.

    Canonical Address_eqType := Eval hnf in EqType Address Address_eqMixin.

    Definition Address_choiceMixin : Choice.mixin_of Address_eqType. Admitted. 

    Canonical Address__choiceType := Eval hnf in ChoiceType Address Address_choiceMixin.

    Definition Address_countMixin : Finite.mixin_of Address_eqType. Admitted.

    Canonical Addr_countType := Eval hnf in CountType Address Address_countMixin.

    Definition Address_finMixin : Finite.mixin_of Addr_countType. Admitted.
    Canonical Address_finType := Eval hnf in FinType Address Address_finMixin.

    Definition trans_eq (a b:Transaction):bool := ((source a) == (source b)) && ((destination a) == (destination b)) && ((val a) == (val b)).
    Lemma eq_transP : Equality.axiom trans_eq. Admitted.


    (* Proof.
        case => sa da ma [sb] db mb; rewrite/trans_eq/=.
        case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
        case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
        case P3: (ma == mb)=>/=; last by constructor 2; case=> _ _ /eqP; rewrite P3.
        by constructor 1; move/eqP: P1=><-; move/eqP: P2=><-; move/eqP: P3=><-.
    Qed. *)

    Canonical Transaction_eqMixin := Eval hnf in EqMixin eq_transP.
    Canonical Transaction_eqType := Eval hnf in EqType Transaction Transaction_eqMixin.
End Canonicals.


 