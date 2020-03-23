theory Privacy_Notions_2 imports
CryptHOL.CryptHOL
begin
(*NB: the message type must have a size function avaliavle,  can make it more general than bitstrings atm but
for now we leave it like this. Do not think making it more general will effect the proofs.*)

(*Atm we are assuming the batch queries are only (r_0,r_1) where r_0 and r_1 are both batches, not tuples of batches*)

sledgehammer_params[timeout = 1000]

type_synonym ('sender', 'receiver', 'aux') communication = "'sender' \<times> 'receiver' \<times> bool list \<times> 'aux'"

type_synonym ('sender', 'receiver', 'aux') batch = "('sender', 'receiver', 'aux') communication list"

type_synonym ('sender', 'receiver', 'aux', 'adversary_observations') protocol_model 
                = "('sender', 'receiver', 'aux') batch \<Rightarrow> 'adversary_observations'"

type_synonym ('sender', 'receiver', 'aux') scenerio = "('sender', 'receiver', 'aux') batch list"

type_synonym ('sender', 'receiver', 'aux') challenge 
              = "('sender', 'receiver', 'aux') scenerio \<times> ('sender', 'receiver', 'aux') scenerio"

locale simple_game = 
  fixes protocol_model :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'adversary_observations spmf" 
    and checks_batch :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool"
  assumes lossless_prot_model: "\<forall> batch. lossless_spmf (protocol_model batch)" 
begin

primrec simple_game :: 
          "((('sender, 'receiver, 'aux) batch \<times> ('sender, 'receiver, 'aux) batch) \<times> 'state) spmf 
              \<times> ('adversary_observations \<Rightarrow> 'state \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where "simple_game (\<A>1, \<A>2) = do {
    b \<leftarrow> coin_spmf;
    ((r0,r1), \<sigma>) \<leftarrow> \<A>1;
    _ :: unit \<leftarrow> assert_spmf (checks_batch r0 r1);
    c \<leftarrow> protocol_model (if b then r1 else r0);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b = b')}"

definition "advantage \<A> = spmf (simple_game \<A>) True - 1/2"

(*primrec simple_game :: 
          "('aux_info \<Rightarrow> ((('sender, 'receiver, 'aux) batch \<times> ('sender, 'receiver, 'aux) batch) \<times> 'state) spmf )
              \<times> ('adversary_observations \<Rightarrow> 'state \<Rightarrow> bool spmf) \<Rightarrow> 'aux_info  \<Rightarrow> bool spmf"
  where "simple_game (\<A>1, \<A>2) aux = do {
    b \<leftarrow> coin_spmf;
    ((r0,r1), \<sigma>) \<leftarrow> \<A>1 aux;
    _ :: unit \<leftarrow> assert_spmf (checks_batch r0 r1);
    c \<leftarrow> protocol_model (if b then r1 else r0);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b = b')}"

definition "advantage \<A> aux = spmf (simple_game \<A> aux) True - 1/2"*)

end 

locale reductions = simple_game protocol_model
  for protocol_model :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'adversary_observations spmf" +
  assumes lossless_prot_model: "\<forall> batch. lossless_spmf (protocol_model batch)" 
begin


(*TODO: look at the definitions of L_b and L_b', think they need changing slightly, think this may be okay*)

definition user_messages :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'sender \<Rightarrow> bool list set"
  where "user_messages b u \<equiv> {m. \<exists> com \<in> set b. fst com = u \<and> fst (snd (snd com)) = m}"

lemma assumes "b = [(s0,r0,m0,a0), (s1,r1,m1,a1)]" and "s0 \<noteq> u2 \<and> s1 \<noteq> u2"
  shows "user_messages b u2 = {}"
  by(auto simp add: user_messages_def assms)

definition L_b :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> ('sender \<times> bool list set) set"
  where "L_b S i \<equiv> {(user,M). \<exists> com \<in> set (nth S i). fst com = user \<and> M = user_messages (nth S i) user}"

lemma assumes "S = [[(s0,r0,m0,a0), (s1,r1,m1,a1)], [(s3,r3,m3,a3), (s4,r4,m4,a4)]]"
  and "s0 \<noteq> s1"
  shows "L_b S 0 = {(s0,{m0}), (s1,{m1})}"
  apply(auto simp add: L_b_def assms user_messages_def)
  using assms by auto 

definition receiver_messages :: "('sender, 'receiver, 'aux) batch \<Rightarrow> 'receiver \<Rightarrow> bool list set"
  where "receiver_messages b r \<equiv> {m. \<exists> com \<in> set b. fst (snd com) = r \<and> fst (snd (snd com)) = m}"

definition L_b' :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> ('receiver \<times> bool list set) set"
  where "L_b' S i \<equiv> {(receiver,M). \<exists> com \<in> set (nth S i). fst (snd com) = receiver 
                       \<and> M = receiver_messages (nth S i) receiver}"

(*definition L_b :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender \<times> bool list set) set"
  where "L_b b batch0 batch1 \<equiv> {(s, M). \<forall> m \<in> M. \<exists> batch \<in> set (if b then batch1 else batch0). fst batch = s \<and> fst (snd (snd batch)) = m}"

definition L_b' :: "bool \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> ('receiver \<times> bool list set) set"
  where "L_b' b batch0 batch1 \<equiv> {(s, M). \<forall> m \<in> M. \<exists> batch \<in> set (if b then batch1 else batch0). fst (snd batch) = s \<and> fst (snd (snd batch)) = m}"*)

definition U_b :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> 'sender set"
  where "U_b S i = {u. \<forall> M. (u,M) \<in> L_b S i}"

definition U_b' :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> 'receiver set"
  where "U_b' S i = {u. \<forall> M. (u,M) \<in> L_b' S i}"

definition Q_b :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> ('sender \<times> nat) set"
  where "Q_b S i = {(u,n). \<forall> M. (u,M) \<in> L_b S i \<and> (\<forall> m \<in> M. length m = n)}"

definition Q_b' :: "('sender, 'receiver, 'aux) scenerio \<Rightarrow> nat \<Rightarrow> ('receiver \<times> nat) set"
  where "Q_b' S i = {(u,n). \<forall> M. (u,M) \<in> L_b' S i \<and> (\<forall> m \<in> M. length m = n)}"

definition U :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "U C k \<equiv> (U_b (fst C) k  = U_b (snd C) k)" 

definition U' :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "U' C k \<equiv> (U_b' (fst C) k  = U_b' (snd C) k)" 

definition Q :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "Q C k \<equiv> (Q_b (fst C) k = Q_b (snd C) k)"

definition Q' :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "Q' C k \<equiv> (Q_b' (fst C) k = Q_b' (snd C) k)"

definition U_card :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "U_card C k \<equiv> (card (U_b (fst C) k) = card (U_b (snd C) k))" 

definition U_card' :: "('sender, 'receiver, 'aux) challenge \<Rightarrow> nat \<Rightarrow> bool"
  where "U_card' C k \<equiv> (card (U_b' (fst C) k) = card (U_b' (snd C) k))" 

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

definition checks_batch_O where "checks_batch_O r0 r1 = True"

definition  checks_batch_RO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO r0 r1 = ER r0 r1"

definition  checks_batch_SO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO r0 r1 = ES r0 r1"

definition  checks_batch_SO_cardU :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_cardU r0 r1 = (ES r0 r1 \<and> U_card r0 r1)"

definition  checks_batch_RO_cardU' :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_cardU' r0 r1 = (ER r0 r1 \<and> U_card' r0 r1)"

definition  checks_batch_SML :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SML r0 r1 = (ES r0 r1 \<and> Q r0 r1)"

definition  checks_batch_RML :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RML r0 r1 = (ER r0 r1 \<and> Q' r0 r1)"

definition  checks_batch_SFL :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SFL r0 r1 = (ES r0 r1 \<and> U r0 r1)"

definition  checks_batch_RFL :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RFL r0 r1 = (ER r0 r1 \<and> U' r0 r1)"

definition  checks_batch_SOMO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SOMO r0 r1 \<equiv> (ESM r0 r1)"

definition  checks_batch_ROMO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_ROMO r0 r1 \<equiv> (ERM r0 r1)"

definition  checks_batch_SOMO_M :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SOMO_M r0 r1 \<equiv> (ESM r0 r1 \<and> M_card r0 r1)"

definition  checks_batch_ROMO_M :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_ROMO_M r0 r1 \<equiv> (ESM r0 r1 \<and> M_card r0 r1)"

definition  checks_batch_SO_RO :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_RO r0 r1 = ES r0 r1"

definition checks_batch_RO_brSO_U_cardbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSO_U_cardbr r0 r1 = (U_card r0 r1)"

definition checks_batch_SO_brRO_U_card'br :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRO_U_card'br r0 r1 = (U_card' r0 r1)"

definition checks_batch_SO_brRFLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRFLbr r0 r1 = (U' r0 r1)"

definition checks_batch_RO_brSFLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSFLbr r0 r1 = (U r0 r1)"

definition checks_batch_SO_brRMLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_SO_brRMLbr r0 r1 = (Q' r0 r1)"

definition checks_batch_RO_brSMLbr :: "('sender, 'receiver, 'aux) batch \<Rightarrow> ('sender, 'receiver, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO_brSMLbr r0 r1 = (Q r0 r1)"

lemma Q_imp_U:
  assumes "Q batch0 batch1" 
  shows "U batch0 batch1"
  using assms by(simp add: Q_def U_def Q_b_def U_b_def; blast) 

sublocale O: simple_game protocol_model checks_batch_O
  by(simp add: simple_game_axioms)

sublocale RO: simple_game protocol_model checks_batch_RO
  by(simp add: simple_game_axioms)

sublocale SO: simple_game protocol_model checks_batch_SO
  by(simp add: simple_game_axioms)

sublocale SO_cardU: simple_game protocol_model checks_batch_SO_cardU
  by(simp add: simple_game_axioms)

sublocale SFL: simple_game protocol_model checks_batch_SFL
  by(simp add: simple_game_axioms)

sublocale SML: simple_game protocol_model checks_batch_SML
  by(simp add: simple_game_axioms)

sublocale SOMO_M: simple_game protocol_model checks_batch_SOMO_M
  by(simp add: simple_game_axioms)

sublocale SOMO: simple_game protocol_model checks_batch_SOMO
  by(simp add: simple_game_axioms)

sublocale RO_brSMLbr: simple_game protocol_model checks_batch_RO_brSMLbr
  by(simp add: simple_game_axioms)

sublocale SO_brRMLbr: simple_game protocol_model checks_batch_SO_brRMLbr
  by(simp add: simple_game_axioms)

sublocale RO_brSFLbr: simple_game protocol_model checks_batch_RO_brSFLbr
  by(simp add: simple_game_axioms)

sublocale SO_brRFLbr: simple_game protocol_model checks_batch_SO_brRFLbr
  by(simp add: simple_game_axioms)

sublocale SO_brRO_U_card'br: simple_game protocol_model checks_batch_SO_brRO_U_card'br
  by(simp add: simple_game_axioms)

sublocale RO_brSO_U_cardbr: simple_game protocol_model checks_batch_RO_brSO_U_cardbr
  by(simp add: simple_game_axioms)

lemma ESM_imp_L_b'_True_eq_False:
  assumes "(\<forall> (s0,r0,m0,aux0) \<in> List.list.set batch0. \<forall> (s1,r1,m1,aux1) \<in> List.list.set batch1. r0 = r1 \<and> aux0 = aux1)"
  shows "L_b' True batch0 batch1 = L_b' False batch0 batch1"
  using assms L_b'_def oops
lemma ESM_imp_Q_b'_unfold:
  assumes "(\<forall> (s0,r0,m0,aux0) \<in> List.list.set batch0. \<forall> (s1,r1,m1,aux1) \<in> List.list.set batch1. r0 = r1 \<and> aux0 = aux1)"
  shows "Q_b' True batch0 batch1 = Q_b' False batch0 batch1"
  using ESM_imp_L_b'_True_eq_False Q_b'_def assms by simp
(*proof
  show "Q_b' True batch0 batch1 \<subseteq> Q_b' False batch0 batch1"
  proof
    fix x 
    assume asm: "x \<in> Q_b' True batch0 batch1"
    then obtain u M where uM: "(u,M) = x" 
      using Q_b'_def by auto
    hence "(u,M) \<in> Q_b' True batch0 batch1" 
      using asm by simp
    hence "(u,M) \<in> {(u,n). \<exists> M. (u,M) \<in> L_b' True batch0 batch1 \<and> card M = n}"
      using Q_b'_def by simp
    hence "(u,M) \<in> {(u,n). \<exists> M. (u,M) \<in> L_b' False batch0 batch1 \<and> card M = n}"
      using ESM_imp_L_b'_True_eq_False assms by simp
    thus "x \<in> Q_b' False batch0 batch1" 
      by (simp add: uM Q_b'_def)
  qed
next 
  show "Q_b' False batch0 batch1 \<subseteq> Q_b' True batch0 batch1"
    sorry
qed*)

lemma Q'_imp_ESM: assumes "ESM r0 r1" shows "Q' r0 r1"
using ESM_imp_Q_b'_unfold assms ESM_def Q'_def by simp

lemma SO_brRMLbr_imp_SOMO: shows "SOMO.advantage \<A> \<le> SO_brRMLbr.advantage \<A>"
proof-
  have "spmf (SO_brRMLbr.simple_game \<A>) True \<ge> spmf (SOMO.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def SO_brRMLbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: checks_batch_SOMO_def checks_batch_SO_brRMLbr_def assert_spmf_def Q'_imp_ESM)
  thus ?thesis by (simp add: SOMO.advantage_def SO_brRMLbr.advantage_def)
qed

lemma SOMO_imp_SOMO_M: shows "SOMO.advantage \<A> \<ge> SOMO_M.advantage \<A>"
proof-
  have "spmf (SOMO_M.simple_game \<A>) True \<le> spmf (SOMO.simple_game \<A>) True"
    apply(simp add: SOMO.simple_game_def SOMO_M.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SOMO_def checks_batch_SOMO_M_def ESM_def ES_def M_card_def)
  thus ?thesis by (simp add: SOMO.advantage_def SOMO_M.advantage_def)
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

lemma SO_imp_SO_cardU: shows "SO_cardU.advantage \<A> \<le> SO.advantage \<A>"
proof-
  have "spmf (SO.simple_game \<A>) True \<ge> spmf (SO_cardU.simple_game \<A>) True"
    apply(simp add: SO.simple_game_def SO_cardU.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_def checks_batch_SO_cardU_def)
  thus ?thesis by (simp add: SO.advantage_def SO_cardU.advantage_def)
qed

lemma SO_cardU_imp_SFL: shows "SO_cardU.advantage \<A> \<ge> SFL.advantage \<A>"
proof-
  have "spmf (SFL.simple_game \<A>) True \<le> spmf (SO_cardU.simple_game \<A>) True"
    apply(simp add: SFL.simple_game_def SO_cardU.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SFL_def checks_batch_SO_cardU_def U_card_def U_def)
  thus ?thesis by (simp add: SFL.advantage_def SO_cardU.advantage_def)
qed

lemma SFL_imp_SML: shows "SML.advantage \<A> \<le> SFL.advantage \<A>"
proof-
  have "spmf (SFL.simple_game \<A>) True \<ge> spmf (SML.simple_game \<A>) True"
    apply(simp add: SFL.simple_game_def SML.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SFL_def checks_batch_SML_def Q_def U_def U_b_def Q_b_def)
  thus ?thesis by (simp add: SFL.advantage_def SML.advantage_def)
qed

lemma O_imp_RO: shows "O.advantage \<A> \<ge> RO.advantage \<A>"
proof-
  have "spmf (O.simple_game \<A>) True \<ge> spmf (RO.simple_game \<A>) True"
    apply(simp add: O.simple_game_def RO.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def  lossless_prot_model checks_batch_RO_def checks_batch_O_def)
  thus ?thesis by (simp add: O.advantage_def RO.advantage_def)
qed

lemma O_imp_SO_brRO_U_card'br: shows "O.advantage \<A> \<ge> SO_brRO_U_card'br.advantage \<A>"
proof-
  have "spmf (O.simple_game \<A>) True \<ge> spmf (SO_brRO_U_card'br.simple_game \<A>) True"
    apply(simp add: O.simple_game_def SO_brRO_U_card'br.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def  lossless_prot_model checks_batch_RO_def checks_batch_O_def)
  thus ?thesis by (simp add: O.advantage_def SO_brRO_U_card'br.advantage_def)
qed

lemma SO_brRO_U_card'br_imp_SO_brRFLbr: shows "SO_brRFLbr.advantage \<A> \<le> SO_brRO_U_card'br.advantage \<A>"
proof-
  have "spmf (SO_brRFLbr.simple_game \<A>) True \<le> spmf (SO_brRO_U_card'br.simple_game \<A>) True"
    apply(simp add: SO_brRFLbr.simple_game_def SO_brRO_U_card'br.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def  checks_batch_SO_brRO_U_card'br_def checks_batch_SO_brRFLbr_def U'_def U_card'_def)
  thus ?thesis by (simp add: SO_brRFLbr.advantage_def SO_brRO_U_card'br.advantage_def)
qed

lemma SO_brRFLbr_imp_SO_brRMLbr: shows "SO_brRFLbr.advantage \<A> \<ge> SO_brRMLbr.advantage \<A>"
proof-
  have "spmf (SO_brRFLbr.simple_game \<A>) True \<ge> spmf (SO_brRMLbr.simple_game \<A>) True"
    apply(simp add: SO_brRFLbr.simple_game_def SO_brRMLbr.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def checks_batch_SO_brRMLbr_def checks_batch_SO_brRFLbr_def U_b'_def U'_def Q'_def Q_b'_def)
  thus ?thesis by (simp add: SO_brRFLbr.advantage_def SO_brRMLbr.advantage_def)
qed

lemma O_imp_SO: shows "O.advantage \<A> \<ge> SO.advantage \<A>"
proof-
  have "spmf (O.simple_game \<A>) True \<ge> spmf (SO.simple_game \<A>) True"
    apply(simp add: O.simple_game_def SO.simple_game_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(auto simp add: assert_spmf_def  lossless_prot_model checks_batch_SO_def checks_batch_O_def)
  thus ?thesis by (simp add: O.advantage_def SO.advantage_def)
qed

end 

locale simple_game_O =
  fixes protocol_model :: "('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> 'adversary_observations spmf" 
begin

(*test proof, not in proper locale form. Have not worked out which is best yet*)

fun checks_batch_O where "checks_batch_O r0 r1 = True"

fun  checks_batch_RO :: "('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> ('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch_RO r0 r1 = (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                                fst com0 = fst com1 \<and> fst (snd (snd com0)) = fst (snd (snd com1)) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

primrec simple_game_O :: 
          "((('sender, 'receiver, bool list, 'aux) batch \<times> ('sender, 'receiver, bool list, 'aux) batch) \<times> 'state) spmf 
              \<times> ('adversary_observations \<Rightarrow> 'state \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where "simple_game_O (\<A>1, \<A>2) = do {
    b \<leftarrow> coin_spmf;
    ((r0,r1), \<sigma>) \<leftarrow> \<A>1;
    _ :: unit \<leftarrow> assert_spmf (checks_batch_O r0 r1);
    c \<leftarrow> protocol_model (if b then r1 else r0);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b = b')}"

primrec simple_game_RO :: 
          "((('sender, 'receiver, bool list, 'aux) batch \<times> ('sender, 'receiver, bool list, 'aux) batch) \<times> 'state) spmf 
              \<times> ('adversary_observations \<Rightarrow> 'state \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where "simple_game_RO (\<A>1, \<A>2) = do {
    b \<leftarrow> coin_spmf;
    ((r0,r1), \<sigma>) \<leftarrow> \<A>1;
    _ :: unit \<leftarrow> assert_spmf (checks_batch_RO r0 r1);
    c \<leftarrow> protocol_model (if b then r1 else r0);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b = b')}"

definition "advantage_O \<A> = spmf (simple_game_O \<A>) True - 1/2"

definition "advantage_RO \<A> = spmf (simple_game_RO \<A>) True - 1/2"

lemma 
  assumes "spmf (simple_game_O \<A>) True \<ge> 1/2" 
    and "spmf (simple_game_RO \<A>) True > 1/2"
  shows 
    "advantage_O \<A> \<ge> advantage_RO \<A>"
proof-
  have "spmf (simple_game_O \<A>) True \<ge> spmf (simple_game_RO \<A>) True"
    apply(simp add: simple_game_O_def simple_game_RO_def split_def)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(simp add: assert_spmf_def)
  thus ?thesis 
    using assms by (simp add: simple_game_O.advantage_O_def simple_game_O.advantage_RO_def)
qed


end 

locale simple_game_RO =
  fixes protocol_model :: "('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> 'adversary_observations spmf" 
begin
(*everything same except receivers is the same*)

lemma 
  "fst (a1,a2,a3,a4) = a1" 
  "fst (snd (a1,a2,a3,a4)) = a2"
  "fst (snd (snd (a1,a2,a3,a4))) = a3" 
  "snd (snd (snd (a1,a2,a3,a4))) = a4" 
  by auto

fun  checks_batch :: "('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> ('sender, 'receiver, bool list, 'aux) batch \<Rightarrow> bool" 
  where "checks_batch r0 r1 = (\<forall> com0 \<in> List.list.set r0. \<forall> com1 \<in> List.list.set r1. 
                                fst com0 = fst com1 \<and> fst (snd (snd com0)) = fst (snd (snd com1)) 
                                  \<and> snd (snd (snd com0)) = snd (snd (snd com1)))"

sublocale simple_game_R0: simple_game protocol_model checks_batch .


