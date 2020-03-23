theory PETS imports
CryptHOL.CryptHOL
begin
(*NB: the message type must have a size function avaliavle,  can make it more general than bitstrings atm but
for now we leave it like this. Do not think making it more general will effect the proofs.*)

(*Atm we are assuming the batch queries are only (r_0,r_1) where r_0 and r_1 are both batches, not tuples of batches*)


sledgehammer_params[timeout = 1000]

type_synonym ('sender', 'receiver', 'aux') communication = "'sender' \<times> 'receiver' \<times> bool list \<times> 'aux'"

type_synonym ('sender', 'receiver', 'aux') batch = "('sender', 'receiver', 'aux') communication list"

type_synonym ('sender', 'receiver', 'aux') scenerio 
                = "('sender', 'receiver', 'aux') batch list"

type_synonym ('sender', 'receiver', 'aux') simple_challenge 
              = "('sender', 'receiver', 'aux') batch \<times> ('sender', 'receiver', 'aux') batch" 

type_synonym ('sender', 'receiver', 'aux') challenge 
              = "('sender', 'receiver', 'aux') scenerio \<times> ('sender', 'receiver', 'aux') scenerio"

type_synonym ('sender', 'receiver', 'aux', 'adversary_observations') protocol_model 
                = "('sender', 'receiver', 'aux') batch \<Rightarrow> 'adversary_observations'"

locale simple_game = 
  fixes protocol_model :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'adversary_observations spmf" 
    and checks_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  assumes lossless_prot_model: "\<forall> batch. lossless_spmf (protocol_model batch)" 
begin

(*the adversary outputs a r0 and r1 which are both batches. The paper is a little ambiguous as to what is outputted here,
either two batches or two scenerios --- but it is somewhat cleared up by looking at 4/5 of the simple game where it says 
that the challengeer hands the batch rb to the protocol*)

primrec simple_game :: 
          "((('sender, 'receiver, 'aux) batch \<times> ('sender, 'receiver, 'aux) batch) \<times> 'state) spmf 
              \<times> ('adversary_observations \<Rightarrow> 'state \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where "simple_game (\<A>1, \<A>2) = do {
    b \<leftarrow> coin_spmf;
    ((r0,r1), \<sigma>) \<leftarrow> \<A>1;
    _ :: unit \<leftarrow> assert_spmf (checks_batch r0 r1 \<and> (length r0 = length r1));
    c \<leftarrow> protocol_model (if b then r1 else r0);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b = b')}"

definition "advantage \<A> = spmf (simple_game \<A>) True - 1/2"     

end

locale reductions = simple_game protocol_model
  for protocol_model :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'adversary_observations spmf" +
  assumes lossless_prot_model: "\<forall> batch. lossless_spmf (protocol_model batch)" 
begin

definition sender_in_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'sender \<Rightarrow> bool"
  where "sender_in_batch batch user \<equiv> \<exists> (u,u',m,aux) \<in> List.list.set batch. user = u"

definition msg_sender_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'sender \<Rightarrow> bool list \<Rightarrow> bool"
  where "msg_sender_batch batch user msg \<equiv> \<exists> (u,u',m,aux) \<in> List.list.set batch. user = u \<and> msg = m"

lemma msg_sender_batch_imp_sender_in_batch:
  assumes "msg_sender_batch batch user msg"
    shows "sender_in_batch batch user"
  using msg_sender_batch_def sender_in_batch_def assms by fast

definition receiver_in_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver \<Rightarrow> bool"
  where "receiver_in_batch batch receiver \<equiv> \<exists> (u,u',m,aux) \<in> List.list.set batch. receiver = u'"

definition msg_receiver_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver \<Rightarrow> bool list \<Rightarrow> bool"
  where "msg_receiver_batch batch receiver msg \<equiv> \<exists> (u,u',m,aux) \<in> List.list.set batch. receiver = u'"

(*inductive_set receiver_msg_set :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver \<Rightarrow> bool list set"
  for batch0 :: "('sender, 'receiver, 'aux) batch"
    and u' :: 'receiver
  where "m \<in> receiver_msg_set batch0 u'" if "m "*)

lemma msg_receiver_batch_imp_receiver_in_batch:
  assumes "msg_receiver_batch batch user msg"
    shows "receiver_in_batch batch user"
  using msg_receiver_batch_def receiver_in_batch_def assms by fast

subsection\<open>Simple properties\<close>

definition M_card :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "M_card r0 r1 \<equiv> (\<forall> (s0,r0,m0,aux0) \<in> List.list.set r0. \<forall> (s1,r1,m1,aux1) \<in> List.list.set r1. size m0 = size m1)"

definition ES :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "ES r0 r1 \<equiv> (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                                fst (snd com0) = fst (snd com1) \<and> fst (snd (snd com0)) = fst (snd (snd com1)) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

definition ER :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "ER r0 r1 = (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                                fst com0 = fst com1 \<and> fst (snd (snd com0)) = fst (snd (snd com1)) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

definition EM :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "EM r0 r1 = (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                                fst com0 = fst com1 \<and> fst (snd com0) = fst (snd com1) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

definition ESM :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "ESM r0 r1 = (\<forall> (s0,r0,m0,aux0) \<in> List.list.set r0. \<forall> (s1,r1,m1,aux1) \<in> List.list.set r1. r0 = r1 \<and> aux0 = aux1)"

definition ERM :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "ERM r0 r1 = (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                           fst com0 = fst com1 \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

definition ESR :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "ESR r0 r1 \<equiv> (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                             fst (snd (snd com0)) = fst (snd (snd com1)) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

inductive_set user_msg_link :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender \<times> bool list) set"
  for batch :: "('sender, 'receiver, 'aux) batch"
  where "\<exists> u u' m a. (u,u',m,a) \<in> List.list.set batch \<Longrightarrow> (u,m) \<in> user_msg_link batch"

inductive_set receiver_msg_link :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> bool list) set"
  for batch :: "('sender, 'receiver, 'aux) batch"
  where "\<exists> u u' m a. (u,u',m,a) \<in> List.list.set batch \<Longrightarrow> (u',m) \<in> receiver_msg_link batch"

inductive_set receiver_msg_link' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> bool list) set"
  for batch :: "('sender, 'receiver, 'aux) batch"
  where " (u,u',m,a) \<in> List.list.set batch \<Longrightarrow> (u',m) \<in> receiver_msg_link' batch"

thm receiver_msg_link.simps receiver_msg_link'.simps 

lemma assumes "(u,m) \<in> receiver_msg_link' batch"
  shows "(\<exists>u' m'. u = u' \<and> m = m' \<and> (\<exists>u u' m a. (u, u', m, a) \<in> set batch))"
  using assms by(auto simp add:receiver_msg_link'.simps receiver_msg_link.simps)

inductive_simps receiver_msg_link_simp [simp]:
  "(u',m) \<in> receiver_msg_link batch"

definition Lb :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender \<times> bool list set) set"
  where "Lb b batch0 batch1 = {(u,M)| u M. \<forall> m \<in> M. (u,m) \<in> user_msg_link (if b then batch1 else batch0)}"

definition Lb' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> bool list set) set"
  where "Lb' b batch0 batch1 = {(u,M)| u M. \<forall> m \<in> M. (u,m) \<in> receiver_msg_link (if b then batch1 else batch0)}"

(*inductive_set Lb :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender \<times> bool list set) set"
  for b :: bool
    and batch0 :: "('sender, 'receiver, 'aux) batch"
    and batch1 :: "('sender, 'receiver, 'aux) batch"
  where "(u,M) \<in> Lb b batch0 batch1" if "(\<forall> m \<in> M. user_msg_link (if b then batch1 else batch0))"*)

(*inductive_set Lb' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> bool list set) set"
  for b :: bool
    and batch0 :: "('sender, 'receiver, 'aux) batch"
    and batch1 :: "('sender, 'receiver, 'aux) batch"
  where "(u,M) \<in> Lb' b batch0 batch1" if "(\<forall> m \<in> M. msg_receiver_batch (if b then batch1 else batch0) u m)"*)

definition Ub :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> 'sender set"
  where "Ub b batch0 batch1 = {u| u M. (u, M) \<in> Lb b batch0 batch1}"

definition Ub' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver set"
  where "Ub' b batch0 batch1 = {u'| u' M. (u', M) \<in> Lb' b batch0 batch1}"

inductive_set Ub'' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver set"
  for b :: bool
    and batch0 :: "('sender, 'receiver, 'aux) batch"
    and batch1 :: "('sender, 'receiver, 'aux) batch"
  where "u \<in> Ub'' b batch0 batch1" if "\<exists> M. (u,M) \<in> Lb' b batch0 batch1"

lemma "Ub' b b0 b1 = Ub'' b b0 b1"
  by(simp add: Ub'_def Ub''.simps Ub''_def Ub''p.simps Lb'_def)

definition U :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "U batch0 batch1 \<equiv> Ub True batch0 batch1 = Ub False batch0 batch1"

definition U' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "U' batch0 batch1 \<equiv> Ub' True batch0 batch1 = Ub' False batch0 batch1"

definition Qb :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender \<times> nat) set"
  where "Qb b batch0 batch1 = {(u, n)| u M n. (u, M) \<in> Lb b batch0 batch1 \<and> card M = n}"

definition Qb' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> nat) set"
  where "Qb' b batch0 batch1 = {(u', n)| u' M n. (u', M) \<in> Lb' b batch0 batch1 \<and> card M = n}"

inductive_set Qb'' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> nat) set"
  for b :: bool
    and batch0 :: "('sender, 'receiver, 'aux) batch"
    and batch1 :: "('sender, 'receiver, 'aux) batch"
  where "(u,n) \<in> Qb'' b batch0 batch1" if "\<exists> M. (u,M) \<in> Lb' b batch0 batch1 \<and> card M = n"

definition Q' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "Q' batch0 batch1 \<equiv> Qb' True batch0 batch1 = Qb' False batch0 batch1" 

definition Q'' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "Q'' batch0 batch1 \<equiv> Qb'' True batch0 batch1 = Qb'' False batch0 batch1" 

definition Q :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "Q batch0 batch1 \<equiv> Qb True batch0 batch1 = Qb False batch0 batch1"

definition card_U :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "card_U batch0 batch1 \<equiv> card (Ub True batch0 batch1) = card (Ub False batch0 batch1)"

definition card_U' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  where "card_U' batch0 batch1 \<equiv> card (Ub' True batch0 batch1) = card (Ub' False batch0 batch1)"

text\<open>Message partitions and historgrams.\<close>

definition MbI :: "nat \<Rightarrow> bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool list set" 
  where "MbI k b  batch0 batch1 \<equiv> \<Union>{M| u M. (u, M) \<in> Lb b batch0 batch1}"


subsection\<open>Check batches\<close>

text\<open>We consider these in the same order as PETs paper.\<close>

definition checks_batch_MO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_MO r0 r1 = EM r0 r1"

definition checks_batch_MO_cardM :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_MO_cardM r0 r1 \<equiv> EM r0 r1 \<and> M_card r0 r1"

definition checks_batch_MOML :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_MOML r0 r1 \<equiv> Q r0 r1 \<and> Q' r0 r1"

definition checks_batch_O where "checks_batch_O r0 r1 = True"

definition checks_batch_SO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO r0 r1 = ES r0 r1"

definition checks_batch_SO_cardU :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_cardU r0 r1 = (ES r0 r1 \<and> card_U r0 r1)"

definition checks_batch_SFL :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SFL r0 r1 = (ES r0 r1 \<and> U r0 r1)"

definition checks_batch_SML :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SML r0 r1 = (ES r0 r1 \<and> Q r0 r1)"

definition checks_batch_RO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO r0 r1 = ER r0 r1"

definition checks_batch_RO_cardU' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_cardU' r0 r1 = (ER r0 r1 \<and> card_U' r0 r1)"

definition checks_batch_RFL :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RFL r0 r1 = (ER r0 r1 \<and> U' r0 r1)"

definition checks_batch_RML :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RML r0 r1 = (ER r0 r1 \<and> Q' r0 r1)"

definition checks_batch_SOMO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SOMO r0 r1 \<equiv> ESM r0 r1"

definition checks_batch_ROMO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_ROMO r0 r1 \<equiv> (ERM r0 r1)"

definition checks_batch_SOMO_M :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SOMO_M r0 r1 \<equiv> (ESM r0 r1 \<and> M_card r0 r1)"

definition checks_batch_ROMO_M :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_ROMO_M r0 r1 \<equiv> (ERM r0 r1 \<and> M_card r0 r1)"

(*section 3 from table 2 in PETs paper*)

definition checks_batch_SO_brRObr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRObr r0 r1 = True"

definition checks_batch_SO_brRO_U_card'br :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRO_U_card'br r0 r1 = (card_U' r0 r1)"

definition checks_batch_SO_brRFLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRFLbr r0 r1 = (U' r0 r1)"

definition checks_batch_SO_brRMLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRMLbr r0 r1 = (Q' r0 r1)"

definition checks_batch_SO_brRMLbr' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRMLbr' r0 r1 = (Q'' r0 r1)"

definition checks_batch_RO_brSObr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSObr r0 r1 = True"

definition checks_batch_RO_brSO_U_cardbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSO_U_cardbr r0 r1 = (card_U r0 r1)"

definition checks_batch_RO_brSFLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSFLbr r0 r1 = (U r0 r1)"

definition checks_batch_RO_brSMLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSMLbr r0 r1 = (Q r0 r1)"

lemma Q_imp_U:
  assumes "Q batch0 batch1"
  shows "U batch0 batch1"
  using assms unfolding Q_def Qb_def U_def Ub_def by blast

text\<open>Construct the sublocales for the hierarchy\<close>

text\<open>Section 1 from table 2 in PETs paper\<close>

sublocale MO: simple_game protocol_model checks_batch_MO
  by(simp add: simple_game_axioms)

sublocale MO_cardM: simple_game protocol_model checks_batch_MO_cardM
  by(simp add: simple_game_axioms)

sublocale MOML: simple_game protocol_model checks_batch_MOML
  by(simp add: simple_game_axioms)

sublocale O: simple_game protocol_model checks_batch_O
  by(simp add: simple_game_axioms)


text\<open>Section 2 from table 2 in PETs paper\<close>

sublocale SO: simple_game protocol_model checks_batch_SO
  by(simp add: simple_game_axioms)

sublocale SO_cardU: simple_game protocol_model checks_batch_SO_cardU
  by(simp add: simple_game_axioms)

sublocale SFL: simple_game protocol_model checks_batch_SFL
  by(simp add: simple_game_axioms)

sublocale SML: simple_game protocol_model checks_batch_SML
  by(simp add: simple_game_axioms)

sublocale RO: simple_game protocol_model checks_batch_RO
  by(simp add: simple_game_axioms)

sublocale RO_cardU': simple_game protocol_model checks_batch_RO_cardU'
  by(simp add: simple_game_axioms)

sublocale RFL: simple_game protocol_model checks_batch_RFL
  by(simp add: simple_game_axioms)

sublocale RML: simple_game protocol_model checks_batch_RML
  by(simp add: simple_game_axioms)

text\<open>Section 3 from table 2 in PETs paper\<close>

sublocale SOMO: simple_game protocol_model checks_batch_SOMO
  by(simp add: simple_game_axioms)

sublocale SOMO_M: simple_game protocol_model checks_batch_SOMO_M
  by(simp add: simple_game_axioms)

sublocale ROMO: simple_game protocol_model checks_batch_ROMO
  by(simp add: simple_game_axioms)

sublocale ROMO_M: simple_game protocol_model checks_batch_ROMO_M
  by(simp add: simple_game_axioms)

text\<open>Section 4 from table 2 in PETs paper\<close>

sublocale SO_brRObr: simple_game protocol_model checks_batch_SO_brRObr
  by(simp add: simple_game_axioms)

sublocale SO_brRO_U_card'br: simple_game protocol_model checks_batch_SO_brRO_U_card'br
  by(simp add: simple_game_axioms)

sublocale SO_brRFLbr: simple_game protocol_model checks_batch_SO_brRFLbr
  by(simp add: simple_game_axioms)

sublocale SO_brRMLbr: simple_game protocol_model checks_batch_SO_brRMLbr
  by(simp add: simple_game_axioms)

sublocale RO_brSObr: simple_game protocol_model checks_batch_RO_brSObr
  by(simp add: simple_game_axioms)

sublocale RO_brSO_U_cardbr: simple_game protocol_model checks_batch_RO_brSO_U_cardbr
  by(simp add: simple_game_axioms)

sublocale RO_brSMLbr: simple_game protocol_model checks_batch_RO_brSMLbr
  by(simp add: simple_game_axioms)

sublocale RO_brSFLbr: simple_game protocol_model checks_batch_RO_brSFLbr
  by(simp add: simple_game_axioms)

text\<open>We now prove the hierarchy.\<close>

lemma O_imp_SO_brRO_U_card'br: shows "O.advantage \<A> \<ge> SO_brRO_U_card'br.advantage \<A>"
proof-
  have "spmf (O.simple_game \<A>) True \<ge> spmf (SO_brRO_U_card'br.simple_game \<A>) True"
    apply(simp add: O.simple_game_def SO_brRO_U_card'br.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_O_def checks_batch_SO_brRO_U_card'br_def) 
  thus ?thesis by (simp add: O.advantage_def SO_brRO_U_card'br.advantage_def)
qed

lemma O_imp_RO_brSO_U_cardbr: shows "O.advantage \<A> \<ge> RO_brSO_U_cardbr.advantage \<A>"
proof-
  have "spmf (O.simple_game \<A>) True \<ge> spmf (RO_brSO_U_cardbr.simple_game \<A>) True"
    apply(simp add: O.simple_game_def RO_brSO_U_cardbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_O_def checks_batch_SO_brRO_U_card'br_def) 
  thus ?thesis by (simp add: O.advantage_def RO_brSO_U_cardbr.advantage_def)
qed

lemma SO_brRO_Ucard'br_imp_SO_brRFLbr: shows "SO_brRO_U_card'br.advantage \<A> \<ge> SO_brRFLbr.advantage \<A>"
proof-
  have "spmf (SO_brRO_U_card'br.simple_game \<A>) True \<ge> spmf (SO_brRFLbr.simple_game \<A>) True"
    apply(simp add: SO_brRFLbr.simple_game_def SO_brRO_U_card'br.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_brRFLbr_def checks_batch_SO_brRO_U_card'br_def U'_def card_U'_def) 
  thus ?thesis by (simp add: SO_brRFLbr.advantage_def SO_brRO_U_card'br.advantage_def)
qed

lemma RO_brSO_Ucardbr_imp_RO_brSFLbr: shows "RO_brSO_U_cardbr.advantage \<A> \<ge> RO_brSFLbr.advantage \<A>"
proof-
  have "spmf (RO_brSO_U_cardbr.simple_game \<A>) True \<ge> spmf (RO_brSFLbr.simple_game \<A>) True"
    apply(simp add: RO_brSO_U_cardbr.simple_game_def RO_brSFLbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_RO_brSFLbr_def checks_batch_RO_brSO_U_cardbr_def U_def card_U_def) 
  thus ?thesis by (simp add: RO_brSFLbr.advantage_def RO_brSO_U_cardbr.advantage_def)
qed

lemma SO_brRFLbr_imp_SO_brRMLbr: shows "SO_brRFLbr.advantage \<A> \<ge> SO_brRMLbr.advantage \<A>"
proof-
  have "spmf (SO_brRFLbr.simple_game \<A>) True \<ge> spmf (SO_brRMLbr.simple_game \<A>) True"
    apply(simp add: SO_brRFLbr.simple_game_def SO_brRMLbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_brRFLbr_def checks_batch_SO_brRMLbr_def Q'_def U'_def Qb'_def Ub'_def Lb'_def) 
  thus ?thesis by (simp add: SO_brRFLbr.advantage_def SO_brRMLbr.advantage_def)
qed

lemma RO_brSFLbr_imp_RO_brSMLbr: shows "RO_brSFLbr.advantage \<A> \<ge> RO_brSMLbr.advantage \<A>"
proof-
  have "spmf (RO_brSFLbr.simple_game \<A>) True \<ge> spmf (RO_brSMLbr.simple_game \<A>) True"
    apply(simp add: RO_brSFLbr.simple_game_def RO_brSMLbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_RO_brSFLbr_def checks_batch_RO_brSMLbr_def Q'_def U_def Qb_def Lb_def Ub_def) 
  thus ?thesis by (simp add: RO_brSFLbr.advantage_def RO_brSMLbr.advantage_def)
qed

lemma SO_brRMLbr_imp_MOML: shows "MOML.advantage \<A> \<le> SO_brRMLbr.advantage \<A>"
proof-
  have "spmf (MOML.simple_game \<A>) True \<le> spmf (SO_brRMLbr.simple_game \<A>) True"
    apply(simp add: SO_brRMLbr.simple_game_def MOML.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_MOML_def checks_batch_SO_brRMLbr_def ESM_def ES_def M_card_def)
  thus ?thesis by (simp add: SO_brRMLbr.advantage_def MOML.advantage_def)
qed

lemma RO_brSMLbr_imp_MOML: shows "MOML.advantage \<A> \<le> RO_brSMLbr.advantage \<A>"
proof-
  have "spmf (MOML.simple_game \<A>) True \<le> spmf (RO_brSMLbr.simple_game \<A>) True"
    apply(simp add: RO_brSMLbr.simple_game_def MOML.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_MOML_def checks_batch_RO_brSMLbr_def ESM_def ES_def M_card_def)
  thus ?thesis by (simp add: RO_brSMLbr.advantage_def MOML.advantage_def)
qed

lemma SOMO_imp_MO: shows "MO.advantage \<A> \<le> SOMO.advantage \<A>"
proof-
  have "spmf (MO.simple_game \<A>) True \<le> spmf (SOMO.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def MO.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SOMO_def checks_batch_MO_def ESM_def ES_def EM_def)
  thus ?thesis by (simp add: MO.advantage_def SOMO.advantage_def)
qed

lemma ROMO_imp_MO: shows "MO.advantage \<A> \<le> ROMO.advantage \<A>"
proof-
  have "spmf (MO.simple_game \<A>) True \<le> spmf (ROMO.simple_game \<A>) True"
    apply(simp add: ROMO.simple_game_def MO.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_ROMO_def checks_batch_MO_def ERM_def ES_def EM_def)
  thus ?thesis by (simp add: MO.advantage_def ROMO.advantage_def)
qed

lemma SOMO_imp_SOMO_M: shows "SOMO.advantage \<A> \<ge> SOMO_M.advantage \<A>"
proof-
  have "spmf (SOMO_M.simple_game \<A>) True \<le> spmf (SOMO.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def SOMO_M.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SOMO_def checks_batch_SOMO_M_def) 
  thus ?thesis by (simp add: SOMO.advantage_def SOMO_M.advantage_def)
qed

lemma ROMO_imp_ROMO_M: shows "ROMO.advantage \<A> \<ge> ROMO_M.advantage \<A>"
proof-
  have "spmf (ROMO_M.simple_game \<A>) True \<le> spmf (ROMO.simple_game \<A>) True"
    apply(simp add: ROMO.simple_game_def ROMO_M.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_ROMO_def checks_batch_ROMO_M_def) 
  thus ?thesis by (simp add: ROMO.advantage_def ROMO_M.advantage_def)
qed

lemma SOMO_imp_MO_M: shows "SOMO.advantage \<A> \<ge> MO_cardM.advantage \<A>"
proof-
  have "spmf (MO_cardM.simple_game \<A>) True \<le> spmf (SOMO.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def MO_cardM.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SOMO_def checks_batch_MO_cardM_def EM_def M_card_def ESM_def) 
  thus ?thesis by (simp add: SOMO.advantage_def MO_cardM.advantage_def)
qed

lemma ROMO_imp_MO_M: shows "ROMO.advantage \<A> \<ge> MO_cardM.advantage \<A>"
proof-
  have "spmf (MO_cardM.simple_game \<A>) True \<le> spmf (ROMO.simple_game \<A>) True"
    apply(simp add: ROMO.simple_game_def MO_cardM.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_ROMO_def checks_batch_MO_cardM_def EM_def M_card_def ERM_def) 
  thus ?thesis by (simp add: ROMO.advantage_def MO_cardM.advantage_def)
qed

lemma MO_imp_MO_cardM: shows "MO_cardM.advantage \<A> \<le> MO.advantage \<A>"
proof-
  have "spmf (MO_cardM.simple_game \<A>) True \<le> spmf (MO.simple_game \<A>) True"
    apply(simp add: MO_cardM.simple_game_def MO.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_MO_cardM_def checks_batch_MO_def EM_def M_card_def)
  thus ?thesis by (simp add: MO.advantage_def MO_cardM.advantage_def)
qed

lemma SOMO_M_imp_SO: shows "SO.advantage \<A> \<le> SOMO_M.advantage \<A>"
proof-
  have "spmf (SOMO_M.simple_game \<A>) True \<ge> spmf (SO.simple_game \<A>) True"
    apply(simp add: SO.simple_game_def SOMO_M.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_def checks_batch_SOMO_M_def ESM_def ES_def M_card_def)
  thus ?thesis by (simp add: SO.advantage_def SOMO_M.advantage_def)
qed

lemma ROMO_M_imp_RO: shows "RO.advantage \<A> \<le> ROMO_M.advantage \<A>"
proof-
  have "spmf (ROMO_M.simple_game \<A>) True \<ge> spmf (RO.simple_game \<A>) True"
    apply(simp add: RO.simple_game_def ROMO_M.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_RO_def checks_batch_ROMO_M_def ERM_def ER_def M_card_def)
  thus ?thesis by (simp add: RO.advantage_def ROMO_M.advantage_def)
qed

lemma SO_imp_SO_cardU: shows "SO_cardU.advantage \<A> \<le> SO.advantage \<A>"
proof-
  have "spmf (SO_cardU.simple_game \<A>) True \<le> spmf (SO.simple_game \<A>) True"
    apply(simp add: SO.simple_game_def SO_cardU.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_def checks_batch_SO_cardU_def ERM_def ER_def M_card_def)
  thus ?thesis by (simp add: SO.advantage_def SO_cardU.advantage_def)
qed

lemma RO_imp_RO_cardU': shows "RO_cardU'.advantage \<A> \<le> RO.advantage \<A>"
proof-
  have "spmf (RO_cardU'.simple_game \<A>) True \<le> spmf (RO.simple_game \<A>) True"
    apply(simp add: RO.simple_game_def RO_cardU'.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_RO_def checks_batch_RO_cardU'_def ERM_def ER_def M_card_def)
  thus ?thesis by (simp add: RO.advantage_def RO_cardU'.advantage_def)
qed

lemma SO_cardU_imp_SFL: shows "SFL.advantage \<A> \<le> SO_cardU.advantage \<A>"
proof-
  have "spmf (SFL.simple_game \<A>) True \<le> spmf (SO_cardU.simple_game \<A>) True"
    apply(simp add: SFL.simple_game_def SO_cardU.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SFL_def checks_batch_SO_cardU_def U_def card_U_def)
  thus ?thesis by (simp add: SFL.advantage_def SO_cardU.advantage_def)
qed

lemma RO_cardU_imp_RFL: shows "RFL.advantage \<A> \<le> RO_cardU'.advantage \<A>"
proof-
  have "spmf (RFL.simple_game \<A>) True \<le> spmf (RO_cardU'.simple_game \<A>) True"
    apply(simp add: RFL.simple_game_def RO_cardU'.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_RFL_def checks_batch_RO_cardU'_def U'_def card_U'_def)
  thus ?thesis by (simp add: RFL.advantage_def RO_cardU'.advantage_def)
qed

lemma EM_imp_ESM:
  assumes "EM b0 b1"
  shows "ESM b0  b1"
  using assms by(simp add: ESM_def EM_def split_def)

lemma EM_imp_ERM:
  assumes "EM b0 b1"
  shows "ERM b0  b1"
  using assms by(simp add: ERM_def EM_def split_def)

lemma ESM_imp_Q':
  assumes "ESM batch0 batch1" 
    and "length batch0 = length batch1"
  shows "Q' batch0 batch1"
  using assms 
  apply(auto simp add: ESM_def Q'_def Qb'_def Lb'_def msg_receiver_batch_def receiver_msg_link.simps split_def)
   by (metis assms(2) length_pos_if_in_set nth_mem prod_cases4)+

lemma EM_imp_Q':
  assumes "EM batch0 batch1" 
    and "length batch0 = length batch1"
  shows "Q' batch0 batch1"
  using EM_imp_ESM ESM_imp_Q' assms by blast

lemma ERM_imp_Q:
  assumes "ERM batch0 batch1" 
    and "length batch0 = length batch1"
  shows "Q batch0 batch1"
  using assms 
  apply(auto simp add: ESM_def Q_def Qb_def Lb_def user_msg_link.simps receiver_msg_link.simps split_def)
   by (metis assms(2) length_pos_if_in_set nth_mem prod_cases4)+

lemma EM_imp_Q:
  assumes "EM batch0 batch1" 
    and "length batch0 = length batch1"
  shows "Q batch0 batch1"
  using EM_imp_ERM ERM_imp_Q assms by blast

lemma MOML_imp_MO: shows "MO.advantage \<A> \<le> MOML.advantage \<A>"
proof-
  have "spmf (MO.simple_game \<A>) True \<le> spmf (MOML.simple_game \<A>) True"
    apply(simp add: MO.simple_game_def MOML.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_MOML_def checks_batch_MO_def EM_imp_Q' EM_imp_Q)
  thus ?thesis by(simp add: MO.advantage_def MOML.advantage_def)
qed

lemma SO_brRMLbr_imp_SOMO: shows "SOMO.advantage \<A> \<le> SO_brRMLbr.advantage \<A>"
proof-
  have "spmf (SOMO.simple_game \<A>) True \<le> spmf (SO_brRMLbr.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def SO_brRMLbr.simple_game_def split_def)
    apply(rule  ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def ESM_imp_Q' checks_batch_SOMO_def checks_batch_SO_brRMLbr_def)
  thus ?thesis 
    by(simp add: SOMO.advantage_def SO_brRMLbr.advantage_def )
qed

lemma RO_brSMLbr_imp_ROMO: shows "ROMO.advantage \<A> \<le> RO_brSMLbr.advantage \<A>"
proof-
  have "spmf (ROMO.simple_game \<A>) True \<le> spmf (RO_brSMLbr.simple_game \<A>) True"
    apply(simp add: ROMO.simple_game_def RO_brSMLbr.simple_game_def split_def)
    apply(rule  ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def ERM_imp_Q checks_batch_ROMO_def checks_batch_RO_brSMLbr_def)
  thus ?thesis 
    by(simp add: ROMO.advantage_def RO_brSMLbr.advantage_def)
qed




