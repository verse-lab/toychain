From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Protocol.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Network semantics *)
Section PacketEqType.

Fixpoint eqpkt a b :=
  ((src a) == (src b)) && ((dst a) == (dst b)) &&
  match (msg a), (msg b) with
  | NullMsg, NullMsg => true
  | NullMsg, _ => false
  | Addr idA prsA, Addr idB prsB => (idA == idB) && (prsA == prsB)
  | Addr _ _, _ => false
  | Connect idA, Connect idB => (idA == idB)
  | Connect _, _ => false
  end.

Lemma eqpktP : Equality.axiom eqpkt.
Proof.
Admitted.

Canonical Packet_eqMixin := EqMixin eqpktP.
Canonical Packet_eqType := EqType Packet Packet_eqMixin.

End PacketEqType.


Definition PacketSoup := seq Packet.

Definition StateMap := union_map [ordType of nid] State.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
  }.

Print Equality.sort.

Inductive reliable_step (w w' : World) : Prop :=
| step_msg (p : Packet) (st' : State) (ms : ToSend) of
      p \in (inFlightMsgs w) &
      match (find (dst p) (localState w)) with
      | Some(st) => updS st (msg p) = (st', ms)
      | _ => false
      end &

      reliable_step w
        (mkW
           (upd (dst p) st' (localState w))
           (ms ++ rem p (inFlightMsgs w))
        ).
