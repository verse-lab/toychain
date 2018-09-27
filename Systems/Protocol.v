From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From fcsl
Require Import pred prelude ordtype pcm finmap unionmap heap.
From Toychain
Require Import SeqFacts Chains Blocks Forests Canonicals Parameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implementation of PoS protocol as a STS *)
Definition peers_t := seq Address.

Inductive Message :=
  | AddrMsg of peers_t
  | ConnectMsg 
  | BlockMsg of block
  | TxMsg of Transaction
  | InvMsg of seq Hash
  | GetDataMsg of Hash.

Inductive MessageType :=
  | MAddr
  | MConnect
  | MBlock
  | MTx
  | MInv
  | MGetData.

Module MsgTypeEq.
Definition eq_msg_type a b :=
  match a, b with
  | MAddr, MAddr => true
  | MConnect, MConnect => true
  | MBlock, MBlock => true
  | MTx, MTx => true
  | MInv, MInv => true
  | MGetData, MGetData => true
  | _, _ => false
  end.

Lemma eq_msg_typeP : Equality.axiom eq_msg_type.
Proof.
move=>a b; case: a; case: b; rewrite /eq_msg_type/=;
by [constructor 1 | constructor 2].
Qed.

Canonical MsgType_eqMixin := Eval hnf in EqMixin eq_msg_typeP.
Canonical MsgType_eqType := Eval hnf in EqType MessageType MsgType_eqMixin.
End MsgTypeEq.
Export MsgTypeEq.

Definition msg_type (msg : Message) : MessageType :=
  match msg with
  | AddrMsg _ => MAddr
  | ConnectMsg => MConnect
  | BlockMsg _ => MBlock
  | TxMsg _ => MTx
  | InvMsg _ => MInv
  | GetDataMsg _ => MGetData
  end.

Definition msg_block (msg : Message) : block :=
  match msg with
  | BlockMsg b => b
  | _ => GenesisBlock
  end.

Definition msg_hashes (msg : Message) : seq Hash :=
  match msg with
  | InvMsg sh => sh
  | GetDataMsg h => [:: h]
  | _ => [::]
  end.

Inductive InternalTransition :=
  | TxT of Transaction
  | MintT.

Module MsgEq.
Definition eq_msg a b :=
 match a, b with
  | AddrMsg prsA, AddrMsg prsB => (prsA == prsB)
  | AddrMsg _, _ => false
  | ConnectMsg, ConnectMsg => true
  | ConnectMsg, _ => false
  | BlockMsg bA, BlockMsg bB => (bA == bB)
  | BlockMsg _, _ => false
  | TxMsg tA, TxMsg tB => (tA == tB)
  | TxMsg _, _ => false
  | InvMsg hA, InvMsg hB => (hA == hB)
  | InvMsg _, _ => false
  | GetDataMsg hA, GetDataMsg hB => (hA == hB)
  | GetDataMsg _, _ => false
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

(* A lot of duplication in this proof; what can be done about it? *)
Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>[p||b|t|h|h].
- case: mb=>//[p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: ((p == p')).
  - by move/eqP:B=><-; constructor 1.
  by constructor 2; case=>Z; subst p'; rewrite eqxx in B.
- case:mb=>////[p'||b'|t'|h'|h']; do? [by constructor 2|by constructor 1].
- case:mb=>////[p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (b == b'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst b'; rewrite eqxx in B.
- case:mb=>////[p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (t == t'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst t'; rewrite eqxx in B.
- case:mb=>////[p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
- case:mb=>////[p'||b'|t'|h'|h']; do? [by constructor 2].
  case B: (h == h'); [by case/eqP:B=><-; constructor 1|constructor 2].
  by case=>Z; subst h'; rewrite eqxx in B.
Qed.
  
Canonical Msg_eqMixin := Eval hnf in EqMixin eq_msgP.
Canonical Msg_eqType := Eval hnf in EqType Message Msg_eqMixin.
End MsgEq.
Export MsgEq.

Record Packet := mkP {src: Address; dst: Address; msg: Message}.

Module PacketEq.
Definition eq_pkt a b :=
  ((src a) == (src b)) && ((dst a) == (dst b)) && ((msg a) == (msg b)).

Lemma eq_pktP : Equality.axiom eq_pkt.
Proof.
case=>sa da ma [sb] db mb; rewrite/eq_pkt/=.
case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
case P3: (ma == mb)=>/=; last by constructor 2; case=> _ _ /eqP; rewrite P3.
by constructor 1; move/eqP: P1=><-; move/eqP: P2=><-; move/eqP: P3=><-.
Qed.

Canonical Packet_eqMixin := Eval hnf in EqMixin eq_pktP.
Canonical Packet_eqType := Eval hnf in EqType Packet Packet_eqMixin.
End PacketEq.
Export PacketEq.


Definition ToSend := seq Packet.
Definition emitZero : ToSend := [::].
Definition emitOne (packet : Packet) : ToSend := [:: packet].
Definition emitMany (packets : ToSend) := packets.

Definition emitBroadcast (from : Address) (dst : seq Address) (msg : Message) :=
  [seq (mkP from to msg) | to <- dst].

Record State :=
  Node {
    id : Address;
    peers : peers_t;
    blockTree : BlockTree;
    txPool : TxPool;
  }.

Definition Init (n : Address) : State :=
  Node n [:: n] (#GenesisBlock \\-> GenesisBlock) [::].
Lemma peers_uniq_init (n : Address) : uniq [::n]. Proof. by []. Qed.

Definition procMsg (st: State) (from : Address) (msg: Message) (ts: Timestamp) :=
    let: Node n prs bt pool := st in
    match msg with
    | ConnectMsg =>
      let: ownHashes := dom bt ++ [seq hashT t | t <- pool] in
      pair (Node n (undup (from :: prs)) bt pool)
           (emitOne (mkP n from (InvMsg ownHashes)))

    | AddrMsg knownPeers =>
      let: newP := [seq x <- knownPeers | x \notin prs] in
      if newP is [::] then pair st emitZero else
      let: connects := [seq mkP n p ConnectMsg | p <- newP] in
      let: updP := undup (prs ++ newP) in
      pair (Node n updP bt pool) (emitMany connects ++ emitBroadcast n prs (AddrMsg updP))

    | BlockMsg b =>
      let: newBt := btExtend bt b in
      let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
      let: ownHashes := dom newBt ++ [seq hashT t | t <- newPool] in
      pair (Node n prs newBt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | TxMsg tx =>
      let: newPool := tpExtend pool bt tx in
      let: ownHashes := dom bt ++ [seq hashT t | t <- newPool] in
      pair (Node n prs bt newPool) (emitBroadcast n prs (InvMsg ownHashes))

    | InvMsg peerHashes =>
      let: ownHashes := dom bt ++ [seq hashT t | t <- pool] in
      let: newH := [seq h <- peerHashes | h \notin ownHashes] in
      let: gets := [seq mkP n from (GetDataMsg h) | h <- newH] in
      pair st (emitMany gets)

    | GetDataMsg h =>
      (* Do not respond to yourself *)
      if from == n then pair st emitZero else
      let: matchingBlocks := [seq b <- [:: get_block bt h] | b != GenesisBlock] in
      match ohead matchingBlocks with
      | Some b => pair (Node n prs bt pool) (emitOne (mkP n from (BlockMsg b)))
      | None =>
        let: matchingTxs := [seq t <- pool | (hashT t) == h] in
        match ohead matchingTxs with
        | Some tx =>
          pair (Node n prs bt pool) (emitOne (mkP n from (TxMsg tx)))
        | None => pair st emitZero
        end
      end
    end.

Definition procInt (st : State) (tr : InternalTransition) (ts : Timestamp) :=
    let: Node n prs bt pool := st in
    match tr with
    | TxT tx => pair st (emitBroadcast n prs (TxMsg tx))

    (* Assumption: nodes broadcast to themselves as well! => simplifies logic *)
    | MintT =>
      let: bc := btChain bt in
      let: allowedTxs := [seq t <- pool | txValid t bc] in
      match genProof n bc allowedTxs ts with
      | Some (txs, pf) =>
        let: prevBlock := last GenesisBlock bc in
        let: b := mkB (hashB prevBlock) txs pf in
        if valid_chain_block bc b then
          let: newBt := btExtend bt b in
          let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
          let: ownHashes := dom newBt ++ [seq hashT t | t <- newPool] in
          pair (Node n prs newBt newPool) (emitBroadcast n prs (BlockMsg b))
        else
          pair st emitZero
      | None => pair st emitZero
      end
    end.

(* Proofs *)
Lemma procMsg_id_constant (s1 : State) from (m : Message) (ts : Timestamp) :
    id s1 = id (procMsg s1 from m ts).1.
Proof.
case: s1 from m ts=>n1 p1 b1 t1 from []=>//=??; last case:ifP => //=.
- by case filter.
- move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procInt_id_constant : forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    id s1 = id (procInt s1 t ts).1.
Proof.
case=> n1 p1 b1 t1 [] =>// ts; simpl.
case hP: genProof => [[txs pf]|] //.
case tV: (valid_chain_block _ _)=>//.
Qed.

Lemma procMsg_valid :
   forall (s1 : State) from (m : Message) (ts : Timestamp),
    valid (blockTree s1) -> valid (blockTree (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[||b|||];
destruct s1; rewrite/procMsg/=; do?by [|move: (btExtendV blockTree0 b)=><-].
- by case filter.
- case:ifP => //=.
  move/eqP => H_neq; case: ifP; move/eqP => //= H_eq H_v.
  by case ohead.
Qed.

Lemma procInt_valid :
  forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    valid (blockTree s1) = valid (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: genProof => [[txs pf]|]; last done.
case tV: (valid_chain_block _ _)=>//.
by rewrite/blockTree/=; apply btExtendV.
Qed.

Lemma procMsg_validH :
   forall (s1 : State) from  (m : Message) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     validH (blockTree (procMsg s1 from  m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[||b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case: ifP => //=.
- by move=>v vh; case filter.
- by move=>v vh; apply btExtendH.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procInt_validH :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     validH (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: genProof => [[txs pf]|]; last by [].
case tV: (valid_chain_block _ _)=>//.
by rewrite/blockTree/=; apply btExtendH.
Qed.

Lemma procMsg_has_init_block:
   forall (s1 : State) from (m : Message) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     has_init_block (blockTree s1) ->
     has_init_block (blockTree (procMsg s1 from m ts).1).
Proof.
move=> s1 from  m ts.
case Msg: m=>[||b|||];
destruct s1; rewrite/procMsg/=; do? by []; do? by case:ifP.
- by case filter.
- by apply btExtendIB.
- move=>v vh; case: ifP => //=; move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procInt_has_init_block :
   forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
     valid (blockTree s1) -> validH (blockTree s1) ->
     has_init_block (blockTree s1) ->
     has_init_block (blockTree (procInt s1 t ts).1).
Proof.
move=>s1 t ts v vh.
case Int: t; destruct s1; rewrite/procInt/=; first by [].
case: genProof => [[txs pf]|]; last by [].
case tV: (valid_chain_block _ _)=>//.
by apply btExtendIB.
Qed.

Lemma procMsg_peers_uniq :
  forall (s1 : State) from  (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 from m ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
case=> n1 p1 b1 t1 from; case; do? by []; simpl.
- move=>? _ ?; case filter => //.
  by move => ? ?; rewrite undup_uniq.
- move=>_ U; case: ifP=>X; rewrite //= ?undup_uniq//=. 
  rewrite andbC/=; apply/negbT/negP; rewrite mem_undup=>Z.
  by rewrite Z in X.
- move=>s _ U; case: ifP => //=.
  move/eqP => H_eq; case: ifP; move/eqP => //= H_eq'.
  by case ohead.
Qed.

Ltac local_bc_no_change s1 hbc hbc' :=
  (rewrite /procMsg; destruct s1=>/=; rewrite /blockTree in hbc;
   by move=>hbc'; rewrite hbc in hbc'; rewrite hbc'; left).

Lemma procMsg_non_block_nc_blockTree :
  forall (s1 : State) from (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 from m ts).1 in
    (forall b, m != BlockMsg b) ->
    blockTree s1 = blockTree s2.
Proof.
move=>s1 from m ts neq.
case: m neq=>[prs||b|t|sh|h] neq;
  do? by[rewrite/procMsg; destruct s1=>/=].
- by rewrite /procMsg; destruct s1 => /=; case filter.
- by specialize (neq b); contradict neq; rewrite eqxx.
- rewrite/procMsg/=; case: s1=>????/=; case:ifP => //=.
  move/eqP => H_neq; case: ifP; move/eqP => //= H_eq.
  by case ohead.
Qed.

Lemma procMsg_non_block_nc_btChain :
  forall (s1 : State) from (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 from m ts).1 in
    (forall b, m != BlockMsg b) ->
    btChain (blockTree s1) = btChain (blockTree s2).
Proof.
move=>s1 from m ts neq.
by move: (procMsg_non_block_nc_blockTree s1 from ts neq)=><-.
Qed.

Lemma procMsg_known_block_nc_blockTree :
  forall (s1 : State) from (b : block) (ts : Timestamp),
    let: s2 := (procMsg s1 from (BlockMsg b) ts).1 in
    let: bt := blockTree s1 in
    b ∈ bt -> bt = blockTree s2.
Proof.
move=>s1 from  b ts biT; destruct s1=>/=; rewrite/blockTree in biT.
by apply (btExtend_withDup_noEffect biT).
Qed.

Lemma procMsg_known_block_nc_btChain (s1 : State) from (b : block) (ts : Timestamp) :
  let: s2 := (procMsg s1 from (BlockMsg b) ts).1 in
  let: bc := btChain (blockTree s1) in
  valid (blockTree s1) -> has_init_block (blockTree s1) ->
  b \in bc -> bc = btChain (blockTree s2).
Proof.
move=>V H biC.
by move: (procMsg_known_block_nc_blockTree from ts (btChain_mem2 V H biC))=><-.
Qed.

Lemma procMsg_block_btExtend_bt :
  forall (s1 : State) from (b : block) (ts: Timestamp),
  let: s2 := (procMsg s1 from (BlockMsg b) ts).1 in
  blockTree s2 = btExtend (blockTree s1) b.
Proof. by move=>s1 b ts; destruct s1. Qed.

Lemma procMsg_block_btExtend_btChain :
  forall (s1 : State) from (b : block) (ts: Timestamp),
  let: s2 := (procMsg s1 from (BlockMsg b) ts).1 in
  btChain (blockTree s2) = btChain (btExtend (blockTree s1) b).
Proof. by move=>s1 b ts; destruct s1. Qed.

Lemma procInt_peers_uniq :
  forall (s1 : State) (t : InternalTransition) ts, let: s2 := (procInt s1 t ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
move=>s1 t ts; case: s1=>n prs bt txp; rewrite /peers/procInt=>Up.
case: t=>//; case hP: genProof => [[txs pf]|]//.
case tV: (valid_chain_block _ _)=>//.
Qed.

Inductive local_step (s1 s2 : State) : Prop :=
| Idle of s1 = s2
| RcvMsg f m ts of (s2 = (procMsg s1 f m ts).1)
| IntT t ts of (s2 = (procInt s1 t ts).1).

Lemma id_constant :
  forall (s1 s2 : State),
    local_step s1 s2 -> id s1 = id s2.
Proof.
move=> s1 s2.
case.
- by move=> ->.
- by move=> f m ts ->; apply procMsg_id_constant.
- by move=> t ts ->; apply procInt_id_constant.
Qed.

Lemma bt_valid :
  forall (s1 s2 : State),
    local_step s1 s2 -> valid (blockTree s1) -> valid (blockTree s2).
Proof.
move=> s1 s2.
case.
- by move=> ->.
- by move=> f m ts ->; apply procMsg_valid.
- by move=> t ts ->; move: (procInt_valid s1 t ts)=><-.
Qed.

Lemma peers_uniq :
  forall (s1 s2 : State),
    uniq (peers s1) -> local_step s1 s2 -> uniq (peers s2).
Proof.
move=> s1 s2 UniqP1.
case.
- by move=> <-.
- by move=> f m ts ->; apply procMsg_peers_uniq.
- by move=> t ts ->; apply procInt_peers_uniq.
Qed.
