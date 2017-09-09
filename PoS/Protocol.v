From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Require Import Blockchain BlockchainProperties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implementation of PoS protocol as a STS *)
Definition nid := nat.
Definition peers_t := seq nid.

Inductive Message :=
  | NullMsg
  | AddrMsg of nid & peers_t
  | ConnectMsg of nid
  | BlockMsg of Block
  | TxMsg of Transaction
  | InvMsg of nid & seq Hash
  | GetDataMsg of nid & Hash.

Definition msg_block (msg : Message) : Block :=
  match msg with
  | BlockMsg b => b
  | _ => GenesisBlock
  end.

Inductive InternalTransition :=
  | TxT of Transaction
  | MintT.

Module MsgEq.
Definition eq_msg a b :=
 match a, b with
  | NullMsg, NullMsg => true
  | NullMsg, _ => false
  | AddrMsg idA prsA, AddrMsg idB prsB => (idA == idB) && (prsA == prsB)
  | AddrMsg _ _, _ => false
  | ConnectMsg idA, ConnectMsg idB => (idA == idB)
  | ConnectMsg _, _ => false
  | BlockMsg bA, BlockMsg bB => (bA == bB)
  | BlockMsg _, _ => false
  | TxMsg tA, TxMsg tB => (tA == tB)
  | TxMsg _, _ => false
  | InvMsg pA hA, InvMsg pB hB => (pA == pB) && (hA == hB)
  | InvMsg _ _, _ => false
  | GetDataMsg pA hA, GetDataMsg pB hB => (pA == pB) && (hA == hB)
  | GetDataMsg _ _, _ => false
 end.

Ltac simple_tactic mb n n' B :=
  (case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2];
   case B: (n == n'); [by case/eqP:B=><-; constructor 1|constructor 2];
   case=>E; subst n'; rewrite eqxx in B).

(* A lot of duplication in this proof; what can be done about it? *)
Lemma eq_msgP : Equality.axiom eq_msg.
Proof.
move=> ma mb. rewrite/eq_msg.
case: ma=>[|n p|n|b|t|p h|p h].
- case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2]; by constructor 1.
- case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2].
  case B: ((n == n') && (p == p')).
  - by case/andP: B=>/eqP<-/eqP<-; constructor 1.
  by case/Bool.andb_false_elim: B=>B; constructor 2; case; move/eqP: B.

(* TODO: unify this! *)
- by simple_tactic mb n n' B.
- by simple_tactic mb b b' B.
- by simple_tactic mb t t' B.

- case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2].
  case B: ((p == p') && (h == h')).
  - by case/andP: B=>/eqP<-/eqP<-; constructor 1.
  by case/Bool.andb_false_elim: B=>B; constructor 2; case; move/eqP: B.
(* This is literally copy-pasted from directly above; better way to do this? *)
- case: mb=>//[|n' p'|n'|b'|t'|p' h'|p' h']; do? [by constructor 2].
  case B: ((p == p') && (h == h')).
  - by case/andP: B=>/eqP<-/eqP<-; constructor 1.
  by case/Bool.andb_false_elim: B=>B; constructor 2; case; move/eqP: B.
Qed.

Canonical Msg_eqMixin := Eval hnf in EqMixin eq_msgP.
Canonical Msg_eqType := Eval hnf in EqType Message Msg_eqMixin.
End MsgEq.
Export MsgEq.

Record Packet := mkP {src: nid; dst: nid; msg: Message}.
Definition NullPacket := mkP 0 0 NullMsg.

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
Definition emitZero : ToSend := [:: NullPacket].
Definition emitOne (packet : Packet) : ToSend := [:: packet].
Definition emitMany (packets : ToSend) := packets.

Definition emitBroadcast (from : nid) (dst : seq nid) (msg : Message) :=
  [seq (mkP from to msg) | to <- dst].

Record State :=
  Node {
    id : nid;
    peers : peers_t;
    blockTree : BlockTree;
    txPool : TxPool;
  }.

Definition Init (n : nid) : State := Node n [:: n] [:: GenesisBlock] [::].
Lemma peers_uniq_init (n : nid) : uniq [::n]. Proof. done. Qed.

(* Please, explain what happens at each transition *)
Definition procMsg (st: State) (msg: Message) (ts: Timestamp) :=
    let: (Node n prs bt pool) := st in
    match msg with
    | ConnectMsg peer => pair (Node n (undup (peer :: prs)) bt pool) emitZero

    | AddrMsg _ knownPeers =>
      let: newP := [seq x <- knownPeers | x \notin prs] in
      let: connects := [seq mkP n p (ConnectMsg n) | p <- newP] in
      let: updP := undup (prs ++ newP) in
      pair (Node n updP bt pool)
           (emitMany(connects) ++ emitBroadcast n prs (AddrMsg n updP))

    | BlockMsg b =>
      let: newBt := (btExtend bt b) in
      let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
      let: ownHashes := [seq hashB b | b <- newBt] ++ [seq hashT t | t <- newPool] in
      pair (Node n prs newBt newPool) (emitBroadcast n prs (InvMsg n ownHashes))

    | TxMsg tx =>
      let: newPool := tpExtend pool bt tx in
      let: ownHashes := [seq hashB b | b <- bt] ++ [seq hashT t | t <- newPool] in
      pair (Node n prs bt newPool) (emitBroadcast n prs (InvMsg n ownHashes))

    | InvMsg p peerHashes =>
      let: ownHashes := [seq hashB b | b <- bt] ++ [seq hashT t | t <- pool] in
      let: newH := [seq h <- peerHashes | h \notin ownHashes] in
      let: gets := [seq mkP n p (GetDataMsg n h) | h <- newH] in
      pair st (emitMany(gets))

    | GetDataMsg p h =>
      let: matchingBlocks := [seq b <- bt | (hashB b) == h] in
      let: matchingTxs := [seq t <- pool | (hashT t) == h] in
      match ohead matchingBlocks with
      | Some(b) =>
        pair (Node n prs bt pool) (emitOne(mkP n p (BlockMsg b)))
      | _ =>
        match ohead matchingTxs with
        | Some (tx) =>
          pair (Node n prs bt pool) (emitOne(mkP n p (TxMsg tx)))
        | _ => pair st emitZero
        end
      end

    | NullMsg => pair st emitZero
    end.

(* TODO: Please, explain these transitions! *)
Definition procInt (st : State) (tr : InternalTransition) (ts : Timestamp) :=
    let: (Node n prs bt pool) := st in
    match tr with
    | TxT tx => pair st (emitBroadcast n prs (TxMsg tx))

    (* Assumption: nodes broadcast to themselves as well! => simplifies logic *)
    | MintT =>
      let: bc := (btChain bt) in
      let: attempt := genProof(stake n bc) in
      match attempt with
      | Some(pf) =>
          if VAF pf ts bc then
            let: allowedTxs := [seq t <- pool | txValid t bc] in
            let: prevBlock := (last GenesisBlock bc) in
            let: block := mkB (height prevBlock + 1) (hashB prevBlock) allowedTxs pf in

            let: newBt := (btExtend bt block) in
            let: newPool := [seq t <- pool | txValid t (btChain newBt)] in
            let: ownHashes := [seq hashB b | b <- newBt] ++ [seq hashT t | t <- newPool] in
            pair (Node n prs newBt newPool) (emitBroadcast n prs (BlockMsg block))

          else
            pair st emitZero

      | _ => pair st emitZero
      end
    end.

(* Proofs *)
Lemma procMsg_id_constant : forall (s1 : State) (m : Message) (ts : Timestamp),
    id s1 = id (procMsg s1 m ts).1.
Proof.
by case=> n1 p1 b1 t1 []=>//=p h; case exB: (ohead _)=>//; case exT: (ohead _).
Qed.

Lemma procInt_id_constant : forall (s1 : State) (t : InternalTransition) (ts : Timestamp),
    id s1 = id (procInt s1 t ts).1.
Proof.
case=> n1 p1 b1 t1 [] =>//; simpl; case hP: (genProof _)=>ts //; case vP: (VAF _)=>//.
Qed.

Lemma procMsg_peers_uniq :
  forall (s1 : State) (m : Message) (ts : Timestamp), let: s2 := (procMsg s1 m ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
case=> n1 p1 b1 t1 []; do? by [].
- case=> [known | n2 known] ts; move=> UniqP1; by apply undup_uniq.
- simpl. move=> n2 ts UniqP1. case B: (n2 \in p1).
  + by apply undup_uniq.
  + rewrite cons_uniq undup_id.
    * rewrite B. by [].
    * by  [].
move=> p h. simpl. case exB: (ohead _). by [].
case exT: (ohead _); by [].
Qed.

Ltac local_bc_no_change s1 hbc hbc' :=
  (rewrite /procMsg; destruct s1=>/=; rewrite /blockTree in hbc;
   by move=>hbc'; rewrite hbc in hbc'; rewrite hbc'; left).

Lemma procMsg_non_block_nc_blockTree :
  forall (s1 : State) (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 m ts).1 in
    (forall b, m != BlockMsg b) ->
    blockTree s1 = blockTree s2.
Proof.
move=>s1 m ts neq.
case: m neq=>[|p prs|p|b|t|p sh|p h] neq;
  do? by[rewrite/procMsg; destruct s1=>/=].
by specialize (neq b); contradict neq; rewrite eqxx.
rewrite/procMsg=>//; destruct s1.
case: (ohead  _); first by []. case (ohead _); by [].
Qed.

Lemma procMsg_block_in_blockTree
  (s1 : State) (m : Message) (ts : Timestamp):
  {subset blockTree s1 <= blockTree (procMsg s1 m ts).1}.
Proof.
case: m=>[|p prs|p|b|t|p sh|p h];
do? by[rewrite/procMsg; destruct s1=>/=]; last first.
- rewrite -procMsg_non_block_nc_blockTree=>//.
case: s1=>id ps bt' tp/= z. 
(* TODO: implement btExtend!!! *)
admit.
Admitted.

Lemma procMsg_non_block_nc_btChain :
  forall (s1 : State) (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 m ts).1 in
    (forall b, m != BlockMsg b) ->
    btChain (blockTree s1) = btChain (blockTree s2).
Proof.
move=>s1 m ts neq.
by move: (procMsg_non_block_nc_blockTree s1 ts neq)=><-.
Qed.

Lemma procMsg_known_block_nc_blockTree :
  forall (s1 : State) (b : Block) (ts : Timestamp),
    let: s2 := (procMsg s1 (BlockMsg b) ts).1 in
    let: bt := blockTree s1 in
    b \in bt -> bt = blockTree s2.
Proof.
move=>s1 b ts biT; destruct s1=>/=; rewrite/blockTree in biT.
by apply (btExtend_withDup_noEffect biT).
Qed.

Lemma procMsg_known_block_nc_btChain :
  forall (s1 : State) (b : Block) (ts : Timestamp),
    let: s2 := (procMsg s1 (BlockMsg b) ts).1 in
    let: bc := btChain (blockTree s1) in
    b \in bc -> bc = btChain (blockTree s2).
Proof.
move=>s1 b ts biC.
by move: (procMsg_known_block_nc_blockTree ts (btChain_mem2 biC))=><-.
Qed.

(* TODO -- simplication doesn't work when it should *)
Lemma procMsg_block_btExtend :
  forall (s1 : State) (b : Block) (ts: Timestamp),
  let: s2 := (procMsg s1 (BlockMsg b) ts).1 in
  btChain (blockTree s2) = btChain (btExtend (blockTree s1) b).
Proof.
Admitted.

Lemma ohead_filter_some (bt : BlockTree) (b0 : Block) (h0 : Hash):
    ohead [seq b <- bt | hashB b == h0] = Some b0 ->
    h0 = hashB b0.
Proof.
Admitted.

Lemma procMsg_no_block_in_ms :
  forall (s1 : State) req resp b ts,
  let: ms := (procMsg s1 req ts).2 in
  resp \in ms -> msg resp = BlockMsg b ->
  req = GetDataMsg (dst resp) (hashB b).
Proof.
move=>[n prs bt tp] req resp b ts iMs B;
case: req iMs=>[|to knwP|to||||]; rewrite/procMsg.
- by rewrite inE=>Con; contradict Con; rewrite/NullPacket;
     case: resp B=>srcR dstR msgR; rewrite/msg=>->; move/eqP.
- rewrite/emitMany/emitBroadcast mem_cat; move/orP. admit.
- by rewrite inE=>Con; contradict Con; rewrite/NullPacket;
     case: resp B=>srcR dstR msgR; rewrite/msg=>->; move/eqP.
- rewrite/emitBroadcast=>/=. admit.
- rewrite/emitBroadcast=>/=. admit.
- rewrite/emitMany=>/=. admit.
(* This is the interesting case *)
- move=>n0 h0. case X: (ohead _)=>[b0|]; rewrite/emitOne=>/=.
  * rewrite inE; case: resp B=>srcR dstR msgR; rewrite/msg=>->.
    move/eqP=>[] src dst Beq; rewrite/dst.
    by move: (ohead_filter_some X)=>->; rewrite dst Beq.
  * case: (ohead _)=>[tx|];
    by rewrite inE=>Con; contradict Con; rewrite/NullPacket;
     case: resp B=>srcR dstR msgR; rewrite/msg=>->; move/eqP.
Admitted.

Lemma procMsg_bc_prefix_or_fork bc bc':
  forall (s1 : State) (m : Message) (ts : Timestamp),
    let: s2 := (procMsg s1 m ts).1 in
    btChain (blockTree s1) = bc  ->
    btChain (blockTree s2) = bc' ->
    bc = bc' \/ (([bc <<< bc'] \/ fork bc bc') /\ bc' > bc).
Proof.
move=>s1; case =>[|p prs|p|b|t|p sh|p h] ts hbc; do? local_bc_no_change s1 hbc hbc'.
- case: s1 hbc =>/= _ _ bt _ hbc; case B: (b \in bt).
  + move: (btExtend_withDup_noEffect B)=><-<-.
    by rewrite hbc; left.

  move=>hbc'; rewrite -hbc -hbc'.
  (* Extension – note that b is not necessarily the last block in bc' *)
  case E: (prevBlockHash (bcLast bc') == hashB (bcLast bc)).
  + right. split; move/negbT/btChain_mem: B; rewrite hbc=>B;
    rewrite -hbc in B E; move: (btChain_extend B E)=>->; rewrite -cats1 hbc.
    by left; exists (bcLast bc'), [::].
    by apply CFR_ext.

  (* Fork *)
  + right. move: (B)=>B'. move/negbT in B.
    move/negbT/btChain_mem in B'. rewrite hbc in B'. rewrite -hbc' in E.
    move/negbT in E. specialize (btChain_fork hbc B' E)=> F. split. right.
    by rewrite -hbc in F; apply F.
    move: (btExtend_withNew_sameOrBetter B)=><-. rewrite -hbc in B'.
    move: (btExtend_withNew_mem B')=><-. rewrite hbc' in F.
    by rewrite hbc hbc'; move: (bc_fork_neq F).

- destruct s1=>/=. case (ohead _ ). rewrite /blockTree in hbc *=>/=.
  + move=> _ hbc'. rewrite hbc in hbc'.
    by rewrite -hbc'; left.
  + case (ohead _) => [x hbc'|hbc']; rewrite /blockTree in hbc *=>/=;
    by rewrite hbc in hbc'; rewrite -hbc'; left.
Qed.

Lemma procInt_peers_uniq :
  forall (s1 : State) (t : InternalTransition) ts, let: s2 := (procInt s1 t ts).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
move=>s1 t ts; case: s1=>n prs bt txp; rewrite /peers/procInt=>Up.
case: t=>//; case hP: (genProof _)=>//; case vP: (VAF _)=>//.
Qed.

Lemma procInt_bc_same_or_extension :
  forall (s1 : State) (t : InternalTransition) ts,
    let s2 := (procInt s1 t ts).1 in
    let bc := btChain (blockTree s1) in
    let bc' := btChain (blockTree s2) in
    bc = bc' \/ [bc <<< bc'].
Proof.
move=>s1 t ts=>/=; destruct s1; case t=>/=; first by left.
case hP: (genProof _)=>[pf|]; last by left.
case vP: (VAF _)=>/=; last by left. right.
set B :=
  {| height := height (last GenesisBlock (btChain blockTree0)) + 1;
     prevBlockHash := hashB (last GenesisBlock (btChain blockTree0));
     txs := [seq t0 <- txPool0 | txValid t0 (btChain blockTree0)];
     proof := pf
  |}.
(*TODO: this is a trivial statement, but we might need a new axiom *)
assert (B \notin (btChain blockTree0)) by admit.
assert (prevBlockHash B == hashB (bcLast (btChain blockTree0))) by done.
by move: (btChain_extend H H0)->; exists B, [::]; rewrite cats1.
Admitted.

Inductive local_step (s1 s2 : State) : Prop :=
| Idle of s1 = s2
| RcvMsg m ts of (s2 = (procMsg s1 m ts).1)
| IntT t ts of (s2 = (procInt s1 t ts).1).

Lemma id_constant :
  forall (s1 s2 : State),
    local_step s1 s2 -> id s1 = id s2.
Proof.
move=> s1 s2.
case.
- by move=> ->.
- by move=> m ts ->; apply procMsg_id_constant.
- by move=> t ts ->; apply procInt_id_constant.
Qed.

Lemma peers_uniq :
  forall (s1 s2 : State),
    uniq (peers s1) -> local_step s1 s2 -> uniq (peers s2).
Proof.
move=> s1 s2 UniqP1.
case.
- by move=> <-.
- by move=> m ts ->; apply procMsg_peers_uniq.
- by move=> t ts ->; apply procInt_peers_uniq.
Qed.