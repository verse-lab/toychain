From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implementation of PoS protocol as a STS *)
Definition nid := nat.
Definition peers := seq nid.

Inductive Message :=
  | NullMsg
  | Addr of nid & peers
  | Connect of nid.

Definition Transmission := (nid * Message)%type.
Definition NullTransmission : Transmission := pair 0 NullMsg.

Definition ToSend := seq Transmission.
Definition emitZero : ToSend := [:: NullTransmission].
Definition emitOne (trans : Transmission) : ToSend := [:: trans].
Definition emitMany (trsms : ToSend) := trsms.

Definition emitOneToOne (to : nid) (msg : Message) : ToSend := [:: pair to msg].
Definition emitManyToOne (to : nid) (msgs : seq Message) : ToSend :=
  [seq (pair to msg) | msg <- msgs].


Section Node. (* Node behaviour *)

Inductive State :=
  | Await of nid & peers.

Definition Init (n : nid) : State := Await n [:: n].

Definition StepFun := State -> Message -> (State * ToSend).

Definition step : StepFun :=
  fun (st: State) (msg: Message) =>
    match st with
    | Await n prs =>
      match msg with
      | Connect peer => pair (Await n (undup (peer :: prs))) emitZero
      | Addr _ knownPeers =>
        let: newP := [seq x <- knownPeers | x \notin prs] in
        let: connects := [seq pair p (Connect n) | p <- newP] in
          pair (Await n (prs ++ newP)) (emitMany(connects))
      | _ => pair st emitZero
      end
    end.

Compute step (Init 0) (Addr 1 [:: 0; 1; 2; 4]).
Compute step (fst (step (Init 0) (Connect 1))) (Addr 1 [:: 0; 1; 2; 4]).

End Node.
