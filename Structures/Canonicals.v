From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun eqtype choice fintype.

From fcsl
Require Import ordtype.

Section Params.
    Parameter Hash: Type.
    Parameter VProof : Type.

    Structure Address: Type := mkAddr {
        ip:'I_1024*'I_1024*'I_1024*'I_1024;
        port:'I_1024
    }.

    Structure Transaction:Type := mkTx {
        source : Address;
        destination : Address;
        val:nat
    }.
End Params.

Section Canonicals.
    Definition VProof_eqMixin : Equality.mixin_of VProof. Admitted.
    Canonical VProof_eqType := EqType VProof VProof_eqMixin.

    Definition Hash_eqMixin : Equality.mixin_of Hash. Admitted.
    Canonical Hash_eqType := EqType Hash Hash_eqMixin.

    Definition Hash_ordMixin : Ordered.mixin_of Hash_eqType. Admitted.
    Canonical Hash_ordType := OrdType Hash Hash_ordMixin.
    
    (* Address
    Definition prod_of_address e :=
    let: mkAddr ipv4 portNum := e in (ipv4, portNum).

    Definition address_of_prod p :=
    let: (ipv4, portNum) := p in mkAddr ipv4 portNum.

    Lemma prod_of_addressK : cancel prod_of_address address_of_prod.
    Proof. by case. Qed.

    Definition address_eqMixin := CanEqMixin prod_of_addressK.
    Canonical Address_eqType := Eval hnf in EqType Address address_eqMixin.
    Definition address_choiceMixin := CanChoiceMixin prod_of_addressK.
    Canonical Address_choiceType := Eval hnf in ChoiceType Address address_choiceMixin.
    Definition address_countMixin := CanCountMixin prod_of_addressK.
    Canonical Address_countType := Eval hnf in CountType Address address_countMixin.
    Definition address_finMixin := CanFinMixin prod_of_addressK.
    Canonical Address_finType := Eval hnf in FinType Address address_finMixin. *)

(*     
    (* Transaction *)
    Definition prod_of_transaction e :=
    let: mkTx source destination val := e in (source, destination, val).

    Definition transaction_of_prod p :=
    let: (source, destination, val) := p in mkTx source destination val.

    Lemma prod_of_transactionK : cancel prod_of_transaction transaction_of_prod.
    Proof. by case. Qed.

    Definition transaction_eqMixin := CanEqMixin prod_of_transactionK.
    Canonical Transaction_eqType := Eval hnf in EqType Transaction transaction_eqMixin. *)

End Canonicals.


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