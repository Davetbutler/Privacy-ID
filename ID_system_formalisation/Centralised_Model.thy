theory Centralised_Model imports
  CryptHOL.CryptHOL
begin

sledgehammer_params[timeout = 1000]

type_synonym ('user', 'query_out') query = "'user' \<Rightarrow> 'query_out'"

type_synonym ('store_non_sens_sttrs', 'store_sens_attrs') govt_store_data = "'store_non_sens_sttrs' set \<times> 'store_sens_attrs' set"

locale centralised_id = 
  fixes reg :: "'user \<Rightarrow> ('token \<times> ('store_non_sens_sttrs, 'store_sens_attrs) govt_store_data) spmf"
    and auth :: "'user \<Rightarrow> 'token \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> 'auth_token spmf"
    and ver :: "'auth_token \<Rightarrow> 'query_out spmf"
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_token :: "'token \<Rightarrow> bool"
    and valid_query :: "('user, 'query_out) query \<Rightarrow> bool"
    and users_attr_creation :: "'user \<Rightarrow> ('non_sens_attrs set \<times> 'sens_atrrs set)"    
    and valid_non_sens_attrs :: "'non_sens_attrs set \<Rightarrow> bool"
    and valid_sens_attrs :: "'sens_atrrs set \<Rightarrow> bool"
  assumes lossless_reg_user: "lossless_spmf (reg user)"
begin
    
definition correct_game :: "'user \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> bool spmf"
  where 
    "correct_game user query = do {
      (token, govt_output) \<leftarrow> reg user;
      auth_token \<leftarrow> auth user token query;
      result \<leftarrow> ver auth_token;
      return_spmf (result = query user)}"

definition "correct \<longleftrightarrow> (\<forall> user query. valid_user user \<longrightarrow> valid_query query 
                            \<longrightarrow> spmf (correct_game user query) True = 1)"

primrec sens_attrs_hiding_game :: "((('user \<times> 'user) \<times> 'state) spmf \<times> ('state \<Rightarrow> 'store_sens_attrs set \<Rightarrow> bool spmf)) \<Rightarrow> bool spmf"
  where 
    "sens_attrs_hiding_game (\<A>1, \<A>2) = TRY do { 
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);      
      b \<leftarrow> coin_spmf;
      (token, (non_sens_attrs, sens_attrs)) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> sens_attrs;
      return_spmf (b' = b)} ELSE coin_spmf"

definition "sens_attrs_hiding_advantage \<A> = \<bar>spmf (sens_attrs_hiding_game \<A>) True - 1/2\<bar>"

definition "perfect_sens_attrs_hiding \<A> \<longleftrightarrow> sens_attrs_hiding_advantage \<A> = 0"

lemma no_sens_attrs_imp_perfect_sens_attrs_hiding:
  assumes "\<forall> user output. output \<in> set_spmf (reg user) \<longrightarrow> snd (snd (output)) = {}"
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
      using assms by auto
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b' \<leftarrow> \<A>2 \<sigma> {};
      map_spmf((=) b') coin_spmf} ELSE coin_spmf"
      including monad_normalisation
      apply(simp add: bind_spmf_const lossless_reg_user lossless_weight_spmfD) 
      by(simp add: map_spmf_conv_bind_spmf)
    also have "... = coin_spmf" 
      by(auto simp add: bind_spmf_const map_eq_const_coin_spmf try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
    ultimately show ?thesis  
      by(simp add: spmf_of_set)
  qed
  thus ?thesis 
    by(simp add: perfect_sens_attrs_hiding_def sens_attrs_hiding_advantage_def)
qed

definition token_hiding_game :: "('user, 'query_out) query \<Rightarrow> (((('user \<times> 'user) \<times> 'state) spmf) \<times> ('state \<Rightarrow> 'token \<Rightarrow> bool spmf)) \<Rightarrow> bool spmf"
  where 
    "token_hiding_game query \<A> = TRY do {
      let (\<A>1, \<A>2) = \<A>;
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b \<leftarrow> coin_spmf;
      (token, (non_sens_attrs, sens_attrs)) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> token;  
      return_spmf (b = b')} ELSE coin_spmf"

definition "token_hiding_advantage query \<A> = (\<bar>spmf (token_hiding_game query \<A>) True - 1/2\<bar>)"

definition "perfect_token_hiding \<A> \<longleftrightarrow> (\<forall> query. valid_query query \<longrightarrow> token_hiding_advantage query \<A> = 0)"

(*this property does not mean much*)

(*primrec auth_token_hiding_game :: "('user, 'query_out) query \<Rightarrow> (('token \<times> 'token) \<times> 's) spmf \<times> ('s \<Rightarrow> 'auth_token \<Rightarrow> bool spmf) \<Rightarrow> bool spmf"
  where 
    "auth_token_hiding_game query (\<A>1, \<A>2) = TRY do {
      ((token0, token1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_token (token0 :: 'token) \<and> valid_token (token1 :: 'token));
      b :: bool \<leftarrow> coin_spmf;
      auth_token :: 'auth_token \<leftarrow> auth (if b then token0 else token1) query;
      b' :: bool \<leftarrow> \<A>2 \<sigma> auth_token;  
      return_spmf (b = b')} ELSE coin_spmf"

definition "auth_token_hiding_advantage \<A> query = \<bar>spmf (auth_token_hiding_game query \<A>) True - 1/2\<bar>"

definition "auth_token_perfect_hiding \<A> \<longleftrightarrow> (\<forall> query. auth_token_hiding_advantage \<A> query = 0)"*)

definition user_binding_game :: "'user \<Rightarrow> ('user, 'query_out) query \<Rightarrow> ('token \<Rightarrow> 'token spmf) \<Rightarrow> bool spmf"
  where 
    "user_binding_game user query \<A> = TRY do {
      (token1, govt_output) \<leftarrow> reg user;
      token2 \<leftarrow> \<A> token1;
      _ :: unit \<leftarrow> assert_spmf (valid_token token2);
      auth_token1 :: 'auth_token \<leftarrow> auth user token1 query;
      auth_token2 :: 'auth_token \<leftarrow> auth user token2 query;
      result1 :: 'query_out \<leftarrow> ver auth_token1;      
      result2 \<leftarrow> ver auth_token2;
      return_spmf (result1 \<noteq> result2)} ELSE return_spmf False"

definition "user_binding_advantage user query \<A> = spmf (user_binding_game user query \<A>) True"

definition "peferfect_user_binding \<A> \<longleftrightarrow> (\<forall> user query. user_binding_advantage user query \<A> = 0)"

primrec query_output_hiding_game :: "('user, 'query_out) query \<Rightarrow> ((('user \<times> 'user) \<times> 'state) spmf \<times> ('state \<Rightarrow> 'query_out \<Rightarrow> bool spmf))  \<Rightarrow> bool spmf"
  where 
    "query_output_hiding_game query (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      (token, govt_output) \<leftarrow> reg (if b then user0 else user1);
      auth_token :: 'auth_token \<leftarrow> auth (if b then user0 else user1) token query;
      result :: 'query_out \<leftarrow> ver auth_token;   
      b' \<leftarrow> \<A>2 \<sigma> result;
      return_spmf (b = b')} ELSE return_spmf False"

definition "query_output_hiding_advantage query \<A> = spmf (query_output_hiding_game query \<A>) True"

definition "perfect_query_output_hiding \<A> \<longleftrightarrow> (\<forall> query. valid_query query \<longrightarrow> query_output_hiding_advantage query \<A> = 0)"

end 

end





(*locale centralised_id = 
  fixes user_enc_reg_phase :: "'sens_atrrs set \<Rightarrow> 'enc_sens_atrrs set spmf"
  fixes govt_reg_phase :: "'attrs set \<Rightarrow> 'enc_sens_atrrs set \<Rightarrow> ('token \<times> ('store_non_sens_attrs, 'store_sens_attrs) govt_store_data) spmf"
    and auth :: "'token \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> 'auth_token spmf"
    and ver :: "'auth_token \<Rightarrow> 'query_out spmf"
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_query :: "('user, 'query_out) query \<Rightarrow> bool"
    and users_attr_creation :: "'user \<Rightarrow> ('attrs set \<times> 'sens_atrrs set)"
begin

definition reg :: "'user \<Rightarrow> ('token \<times> ('store_non_sens_attrs, 'store_sens_attrs) govt_store_data) spmf"
  where "reg user = do {
    let (non_sens_attrs, sens_attrs) = users_attr_creation user;
    enc_sens_attr \<leftarrow> user_enc_reg_phase sens_attrs;
    
definition correct_game :: "'user \<Rightarrow> ('user, 'query_out) query  \<Rightarrow> bool spmf"
  where 
    "correct_game user query = do {
      (token, govt_output) \<leftarrow> reg user;
      auth_token \<leftarrow> auth token query;
      result \<leftarrow> ver auth_token;
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

definition "no_sens_attr \<longleftrightarrow> (\<forall> user. snd (users_attr_creation user) = {})"

lemma 
  assumes "no_sens_attr"
  shows "perfect_sens_attrs_hiding' \<A>"
  including monad_normalisation
proof-
  note [simp] = Let_def split_def 
  have "\<bar>spmf (sens_attrs_hiding_game' \<A>) True - 1/2\<bar> = 0"
  proof-
    obtain \<A>1 and \<A>2 where \<A> [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
    have "sens_attrs_hiding_game' (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      let (attrs, sens_attrs) = users_attr_creation (if b then user0 else user1);
      enc_attrs \<leftarrow> reg_enc_sens_attrs sens_attrs;
      (S, \<sigma>') \<leftarrow> reg_govt_shares attrs enc_attrs;
      b' \<leftarrow> \<A>2 \<sigma> S;
      return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: sens_attrs_hiding_game_def reg_def bind_spmf_const lossless_reg_govt_token lossless_weight_spmfD)
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      let (attrs, sens_attrs) = users_attr_creation (if b then user0 else user1);
      enc_attrs \<leftarrow> reg_enc_sens_attrs {};
      (S, \<sigma>') \<leftarrow> reg_govt_shares attrs enc_attrs;
      b' \<leftarrow> \<A>2 \<sigma> S;
      return_spmf (b' = b)} ELSE coin_spmf"
      using assms[unfolded no_sens_attr_def] 
      by simp
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      let (attrs, sens_attrs) = users_attr_creation (if b then user0 else user1);
      enc_attrs \<leftarrow> reg_enc_sens_attrs {};
      (S, \<sigma>') \<leftarrow> reg_govt_shares attrs enc_attrs;
      b' \<leftarrow> \<A>2 \<sigma> S;
      return_spmf (b' = b)} ELSE coin_spmf"

    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      enc_attrs_b \<leftarrow> reg_enc_sens_attrs {};
      b' :: bool \<leftarrow> \<A>2 \<sigma> enc_attrs_b;
      return_spmf (b' = b)} ELSE coin_spmf"
      using assms[unfolded no_sens_attr_def] 
      by simp
    also have "... = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      enc_attrs_b \<leftarrow> reg_enc_sens_attrs {};
      b' :: bool \<leftarrow> \<A>2 \<sigma> enc_attrs_b;
      map_spmf((=) b') coin_spmf} ELSE coin_spmf"
      by(simp add: map_spmf_conv_bind_spmf)
    also have "... = coin_spmf" 
      by(auto simp add: bind_spmf_const map_eq_const_coin_spmf try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
    ultimately show ?thesis  
      by(simp add: spmf_of_set)
  qed
  thus ?thesis 
    by(simp add: perfect_sens_attrs_hiding_def sens_attrs_hiding_advantage_def)
qed


end *)
