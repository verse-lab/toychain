From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun eqtype choice fintype ssrbool seq.

From fcsl
Require Import ordtype.

Section Params.
    Parameter VProof : Type.
    Parameter Hash : Type.

    Structure Address: Type := mkAddr {
        ip: 'I_2*'I_2*'I_2*'I_2;
        port:'I_2
    }.

    Structure Transaction:Type := mkTx {
        source : Address;
        destination : Address;
        val:nat
    }.
End Params.


Section Canonicals.

    (* Hash *)
    Axiom Hash_eqMixin : Equality.mixin_of Hash.
    Canonical Hash_eqType := Eval hnf in EqType Hash Hash_eqMixin.

    Axiom Hash_ordMixin : Ordered.mixin_of Hash_eqType.
    Canonical Hash_ordType := Eval hnf in OrdType Hash Hash_ordMixin.

    (* VProof *)
    Axiom VProof_eqMixin : Equality.mixin_of VProof.
    Canonical VProof_eqType := Eval hnf in EqType VProof VProof_eqMixin.

    (* Address *)
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
    Canonical Address_finType := Eval hnf in FinType Address address_finMixin.

    (* Transaction *)
    Definition prod_of_transaction e :=
    let: mkTx source destination val := e in (source, destination, val).

    Definition transaction_of_prod p :=
    let: (source, destination, val) := p in mkTx source destination val.

    Lemma prod_of_transactionK : cancel prod_of_transaction transaction_of_prod.
    Proof. by case. Qed.

    Definition transaction_eqMixin := CanEqMixin prod_of_transactionK.
    Canonical Transaction_eqType := Eval hnf in EqType Transaction transaction_eqMixin.

End Canonicals.