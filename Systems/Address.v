From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun eqtype choice fintype ssrbool seq.
From fcsl
Require Import ordtype.

(* This file exists because currently Coq cannot instantiate
  Parameters inside Functors while doing code extraction.
  See "Extract Constant has no effect on functors":
        https://github.com/coq/coq/issues/4749
 *)
Module Type NetAddr.
(* Needs to be finType because the global state is map from Address ->
   State and _all_ addresses (i.e. need to be able to enumerate them)
   should start with the initial state. *)
Structure Address: Type := mkAddr {
    ip: 'I_2*'I_2*'I_2*'I_2;
    port:'I_2
}.

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

Definition Address_ordMixin := fin_ordMixin [finType of Address].
Canonical Address_ordType := Eval hnf in OrdType Address Address_ordMixin.

End NetAddr.
