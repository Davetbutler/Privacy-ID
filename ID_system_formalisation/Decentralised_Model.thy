theory Decentralised_Model imports
  CryptHOL.CryptHOL
begin

type_synonym ('token_pub', 'token_sec') token = "('token_pub' \<times> 'token_sec')"

type_synonym ('user', 'query_out') query = "'user' \<Rightarrow> 'query_out'"

type_synonym ('store_non_sens_attrs', 'store_sens_attrs') govt_store_data = "'store_non_sens_attrs' set \<times> 'store_sens_attrs' set"

locale decentralised_id = 
  fixes reg :: "'user \<Rightarrow> (('token_pub, 'token_sec) token \<times> ('store_non_sens_attrs, 'store_sens_attrs) govt_store_data) spmf"
    and auth :: "('token_pub, 'token_sec) token \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> 'query_out spmf"
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_query :: "('user, 'query_out) query \<Rightarrow> bool"
  assumes lossless_reg: "lossless_spmf (reg user)"
begin

definition correct_game :: "'user \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> bool spmf"
  where 
    "correct_game user query = do {
      (token, govt_output) \<leftarrow> reg user;
      result \<leftarrow> auth token query;
      return_spmf (result = query user)}"

definition "correct \<longleftrightarrow> (\<forall> user query. valid_user user \<longrightarrow> valid_query query 
                            \<longrightarrow> spmf (correct_game user query) True = 1)"

primrec sens_attrs_hiding_game :: "((('user \<times> 'user) \<times> 'state) spmf \<times> ('state \<Rightarrow> 'store_sens_attrs set \<Rightarrow> bool spmf)) \<Rightarrow> bool spmf"
  where 
    "sens_attrs_hiding_game (\<A>1, \<A>2) = TRY do { 
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);      
      b \<leftarrow> coin_spmf;
      (card, (non_sens_attrs, sens_attrs)) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> sens_attrs;
      return_spmf (b' = b)} ELSE coin_spmf"

definition "sens_attrs_hiding_advantage \<A> = \<bar>spmf (sens_attrs_hiding_game \<A>) True - 1/2\<bar>"

definition "perfect_sens_attrs_hiding \<A> \<longleftrightarrow> sens_attrs_hiding_advantage \<A> = 0"

lemma no_sens_attrs_imp_perfect_sens_attrs_hiding:
  assumes "\<forall> user token store_non_sens_attr store_sens_attr. (token, store_non_sens_attr, store_sens_attr) \<in> set_spmf (reg user) \<longrightarrow> store_sens_attr = {}"
  shows "perfect_sens_attrs_hiding \<A>"
proof-
  note [simp] = Let_def split_def 
  have "\<bar>spmf (sens_attrs_hiding_game \<A>) True - 1/2\<bar> = 0"
  proof-
    obtain \<A>1 and \<A>2 where \<A> [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
    have "sens_attrs_hiding_game (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      (card, (store_non_sens_attrs, store_sens_attrs)) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> store_sens_attrs;
      return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: sens_attrs_hiding_game_def)
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      (card, (store_non_sens_attrs, store_sens_attrs)) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> {};
      return_spmf (b' = b)} ELSE coin_spmf"
      apply auto
      apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
      using assms by blast
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b' \<leftarrow> \<A>2 \<sigma> {};
      map_spmf((=) b') coin_spmf} ELSE coin_spmf"
      including monad_normalisation
      by(simp add: bind_spmf_const lossless_reg lossless_weight_spmfD map_spmf_conv_bind_spmf)
    also have "... = coin_spmf" 
      by(auto simp add: bind_spmf_const map_eq_const_coin_spmf try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
    ultimately show ?thesis  
      by(simp add: spmf_of_set)
  qed
  thus ?thesis 
    by(simp add: perfect_sens_attrs_hiding_def sens_attrs_hiding_advantage_def)
qed

primrec token_sec_hiding_game :: "((('user \<times> 'user) \<times> 'state) spmf) \<times> ('state \<Rightarrow> 'token_sec \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where 
    "token_sec_hiding_game (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      b \<leftarrow> coin_spmf;
      ((token_pubb, token_secb), govt_storeb) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> token_secb;
      return_spmf (b' = b)} ELSE coin_spmf"

definition "token_sec_hiding_advantage \<A> = \<bar>spmf (token_sec_hiding_game \<A>) True - 1/2\<bar>"

definition "perfect_token_sec_hiding \<A> \<longleftrightarrow> token_sec_hiding_advantage \<A> = 0"


end 

end
      