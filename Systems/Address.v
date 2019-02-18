From mathcomp.ssreflect
Require Import fintype.

(* This file exists because currently Coq cannot instantiate
  Parameters inside Functors while doing code extraction.
  See "Extract Constant has no effect on functors":
        https://github.com/coq/coq/issues/4749
 *)
Module Type NetAddr.
(* Address is an IP:port pair or something similar *)
(* Needs to be finType because the global state is map from Address -> State *)
Parameter Address : finType.
End NetAddr.