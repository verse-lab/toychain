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

Definition half := prod 'I_1 'I_1.
Definition ip := prod half half.
Definition port := half.

Definition Address := prod ip port.
Definition Address_ordMixin := fin_ordMixin [finType of Address].
Canonical Address_ordType := Eval hnf in OrdType Address Address_ordMixin.

End NetAddr.

Module Addr <: NetAddr.
Include NetAddr.
End Addr.