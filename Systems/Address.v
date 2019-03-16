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

Definition Address := 'I_2.
Definition Address_ordMixin := fin_ordMixin [finType of Address].
Canonical Address_ordType := Eval hnf in OrdType Address Address_ordMixin.

End NetAddr.

Module Addr <: NetAddr.
Include NetAddr.
End Addr.