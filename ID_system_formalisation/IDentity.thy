theory IDentity imports
  CryptHOL.CryptHOL
  Game_Based_Crypto.Game_Based_Crypto
begin

sledgehammer_params[timeout = 1000]

type_synonym ('share1', 'share2', 'share3') share_user_record = "'share1' \<times> 'share2' \<times> 'share3'"

type_synonym ('attrs', 'sens_atrrs', 'result') query = "('attrs' set \<times> 'sens_atrrs' set) \<Rightarrow> 'result'"

type_synonym ('attrs', 'sens_atrrs') user_attrs = "('attrs' set \<times> 'sens_atrrs' set)" 

type_synonym ('user', 'state_attr_hid', 'enc_attrs') attr_hiding_adversary
  = "(('user' \<times> 'user') \<times> 'state_attr_hid') spmf \<times> ('state_attr_hid' \<Rightarrow> 'enc_attrs' \<Rightarrow> bool spmf)"

type_synonym ('user', 'state_attr_hid', 'share1', 'share2', 'share3') attr_hiding_adversary'
  = "(('user' \<times> 'user') \<times> 'state_attr_hid') spmf \<times> ('state_attr_hid' \<Rightarrow> ('share1', 'share2', 'share3') share_user_record \<Rightarrow> bool spmf)"

type_synonym ('token', 'state',  'auth_token') hiding_adversary = "(('token' \<times> 'token') \<times> 'state') spmf \<times> ('state' \<Rightarrow> 'auth_token' \<Rightarrow> bool spmf)"

type_synonym 'token' soundness_adversary = "'token' \<Rightarrow> 'token' spmf"

locale identity_system =
  fixes reg_enc_sens_attrs :: "'sens_atrrs set \<Rightarrow> 'enc_attrs spmf" \<comment> \<open>The user encrypts their attributes before sending them to the government.\<close> 
    and reg_govt_shares :: "'attrs set \<Rightarrow> 'enc_attrs \<Rightarrow> (('share1, 'share2, 'share3) share_user_record \<times> 'state_govt) spmf"
    and reg_govt_token :: "'state_govt \<Rightarrow> ('share1, 'share2, 'share3) share_user_record \<Rightarrow> 'token spmf"
    \<comment> \<open>The government first produces the shares of the user record and then a token to be sent back to the user.\<close>
    and auth :: "'token \<Rightarrow> ('attrs, 'sens_atrrs, 'result) query \<Rightarrow> 'auth_token spmf" 
    \<comment> \<open>Authentication is run between a user and a service provider. 
    The user inputs their token, the service provider their desired query and an authorised token is returned. This is sent to the government.\<close>
    and ver :: "'auth_token \<Rightarrow> 'result spmf"
    \<comment> \<open>The government uses the authorised token to determine the response to the query.\<close>
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_attrs :: "('attrs set \<times> 'sens_atrrs set) \<Rightarrow> bool" 
    and valid_token :: "'token \<Rightarrow> bool"
    and valid_query :: "('attrs, 'sens_atrrs, 'result) query \<Rightarrow> bool"
    and user_set :: "'user set"
    and attrs_set :: "('attrs set \<times> 'sens_atrrs set) set"
    and users_attr_creation :: "'user \<Rightarrow> ('attrs set \<times> 'sens_atrrs set)"
  assumes users_are_valid: "user \<in> user_set \<longrightarrow> valid_user user"
    and atrrs_are_valid: "attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"
    and user_set_not_empty: "user_set \<noteq> {}"
    and attrs_set_not_empty: "attrs_set \<noteq> {}"
    and bij_betw_users_attrs: "bij_betw users_attr_creation user_set attrs_set"
    and lossless_reg_govt_token: "lossless_spmf (reg_govt_token \<sigma> S)"
begin

lemma all_users_valid: "\<forall> user. user \<in> user_set \<longrightarrow> valid_user user"   
  using users_are_valid by simp

lemma all_attrs_valid: "\<forall> attrs. attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"   
  using atrrs_are_valid by simp

text\<open>We define the registration phase using the fixes parameters for the user and government.\<close>

definition reg :: "'user \<Rightarrow> ('token \<times> ('share1, 'share2, 'share3) share_user_record) spmf" 
  where "reg user = do {
   let (attrs, sens_attrs) = users_attr_creation user;
   enc_attrs \<leftarrow> reg_enc_sens_attrs sens_attrs;
   (S, \<sigma>) \<leftarrow> reg_govt_shares attrs enc_attrs;
   token \<leftarrow> reg_govt_token \<sigma> S;
   return_spmf (token, S)}"

subsection\<open>Functional Properties\<close>

lemma obtain_user_from_attrs:
  fixes attrs
  assumes "attrs \<in> attrs_set"
  obtains user where "user \<in> user_set" and "users_attr_creation user = attrs"
  using bij_betw_users_attrs[unfolded bij_betw_def] assms
  by auto 

lemma obtain_attrs_from_user:
  fixes user
  assumes "user \<in> user_set"
  obtains attrs where "attrs \<in> attrs_set" "users_attr_creation user = attrs"
  using bij_betw_users_attrs[unfolded bij_betw_def] assms by blast

text\<open>We require that that no two users, with different attributes, will yield the same tokens upon registration. This must be a property of the registration phase the attributes.\<close>

definition "unique_users = (\<forall> user1 user2. user1 \<in> user_set \<longrightarrow> user2 \<in> user_set \<longrightarrow> user1 \<noteq> user2 \<longrightarrow> reg user1 \<noteq> reg user2)"

text \<open>The correctness property ensures if the IDentity system is carried out honestly the correct query result is returned.\<close>

definition correct_game :: "'user \<Rightarrow> ('attrs, 'sens_atrrs, 'result) query \<Rightarrow> bool spmf"
  where "correct_game user query = do {
        let attrs = users_attr_creation user;
        (token, enc_user_record) \<leftarrow> reg user;
        auth_token \<leftarrow> auth token query;
        b \<leftarrow> ver auth_token;
        return_spmf (b = query attrs)}"  

definition "correct \<longleftrightarrow> (\<forall> user query. valid_user user \<longrightarrow> valid_query query \<longrightarrow> spmf (correct_game user query) True = 1)"

(*the output given to the adversary should be from after the registration phase, in particular the 
second output from the reg phase as this is what the government sees.*)

primrec sens_attrs_hiding_game :: "('user, 'state_attr_hid, 'enc_attrs) attr_hiding_adversary \<Rightarrow> bool spmf"
  where 
    "sens_attrs_hiding_game (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b \<leftarrow> coin_spmf;
      let (attrsb, sens_attrsb) = users_attr_creation (if b then user0 else user1);
      enc_attrs_b \<leftarrow> reg_enc_sens_attrs sens_attrsb;
      b' \<leftarrow> \<A>2 \<sigma> enc_attrs_b;
      return_spmf (b' = b)} ELSE coin_spmf"

primrec sens_attrs_hiding_game' :: "('user, 'state_attr_hid, 'share1, 'share2, 'share3) attr_hiding_adversary' \<Rightarrow> bool spmf"
  where 
    "sens_attrs_hiding_game' (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b :: bool \<leftarrow> coin_spmf;
      (token, S) \<leftarrow> reg (if b then user0 else user1);
      b' \<leftarrow> \<A>2 \<sigma> S;
      return_spmf (b' = b)} ELSE coin_spmf"

definition "sens_attrs_hiding_advantage \<A> = \<bar>spmf (sens_attrs_hiding_game \<A>) True - 1/2\<bar>"

definition "sens_attrs_hiding_advantage' \<A> = \<bar>spmf (sens_attrs_hiding_game' \<A>) True - 1/2\<bar>"

definition "perfect_sens_attrs_hiding \<A> \<longleftrightarrow> sens_attrs_hiding_advantage \<A> = 0"

definition "perfect_sens_attrs_hiding' \<A> \<longleftrightarrow> sens_attrs_hiding_advantage' \<A> = 0"

definition "no_sens_attr \<longleftrightarrow> (\<forall> user. snd (users_attr_creation user) = {})"

lemma 
  assumes "no_sens_attr"
  shows "perfect_sens_attrs_hiding \<A>"
  including monad_normalisation
proof-
  note [simp] = Let_def split_def 
  have "\<bar>spmf (sens_attrs_hiding_game \<A>) True - 1/2\<bar> = 0"
  proof-
    obtain \<A>1 and \<A>2 where \<A> [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
    have "sens_attrs_hiding_game (\<A>1, \<A>2) = TRY do {
      ((user0, user1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_user user0 \<and> valid_user user1);
      b \<leftarrow> coin_spmf;
      let (attrsb, sens_attrsb) = users_attr_creation (if b then user0 else user1);
      enc_attrs_b \<leftarrow> reg_enc_sens_attrs sens_attrsb;
      b' \<leftarrow> \<A>2 \<sigma> enc_attrs_b;
      return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: sens_attrs_hiding_game_def)
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

definition token_hiding_game :: "('attrs, 'sens_atrrs, 'result) query \<Rightarrow> ('token, 'state,  'auth_token) hiding_adversary \<Rightarrow> bool spmf"
  where 
    "token_hiding_game query \<A> = do {
      let (\<A>1, \<A>2) = \<A>;
      ((token0, token1), \<sigma>) \<leftarrow> \<A>1;
      _ :: unit \<leftarrow> assert_spmf (valid_token token0 \<and> valid_token token1);
      b \<leftarrow> coin_spmf;
      auth_token \<leftarrow> auth (if b then token1 else token0) query;
      b' \<leftarrow> \<A>2 \<sigma> auth_token;  
      return_spmf (b = b')}"

definition "token_hiding_advantage query \<A> = (\<bar>spmf (token_hiding_game query \<A>) True - 1/2\<bar>)"

definition "perfect_hiding \<A> \<longleftrightarrow> (\<forall> query. valid_query query \<longrightarrow> token_hiding_advantage query \<A> = 0)" 

definition user_binding_game :: "'user \<Rightarrow> ('attrs, 'sens_atrrs, 'result) query \<Rightarrow> 'token soundness_adversary \<Rightarrow> bool spmf"
  where 
    "user_binding_game user query \<A> = do {
      (token1, enc_user_record) \<leftarrow> reg user;
      token2 \<leftarrow> \<A> token1;
      _ :: unit \<leftarrow> assert_spmf (valid_token token2);
      auth_token1 \<leftarrow> auth token1 query;
      auth_token2 \<leftarrow> auth token2 query;
      b :: 'result \<leftarrow> ver auth_token1;
      b' \<leftarrow> ver auth_token2;
      return_spmf (b \<noteq> b')}"

definition "user_binding_advantage user query \<A> = \<bar>spmf (user_binding_game user query \<A>) True\<bar>"

definition "perfect_soundness \<A> \<longleftrightarrow> (\<forall> user query. valid_user user \<longrightarrow> valid_query query \<longrightarrow> user_binding_advantage user query \<A> = 0)"

end

locale identity_ind_cpa_base = enc: ind_cpa key_gen encrypt decrypt valid_plains 
  for key_gen :: "('pk \<times> 'sk) spmf"
    and encrypt :: "'pk \<Rightarrow> 'sens_atrrs set \<Rightarrow> 'enc_attrs spmf"
    and decrypt :: "'sk \<Rightarrow> 'enc_attrs \<Rightarrow> 'sens_atrrs set option"
    and valid_plains :: "'sens_atrrs set \<Rightarrow> 'sens_atrrs set \<Rightarrow> bool"
begin

definition reg_enc_sens_attrs :: "'sens_atrrs set \<Rightarrow> 'enc_attrs spmf"
  where 
    "reg_enc_sens_attrs sens_attrs = do {
      (pk,sk) \<leftarrow> key_gen;
      encrypt pk sens_attrs}"   

end 

locale id_ind_cpa = identity_ind_cpa_base + 
  id_sys: identity_system reg_enc_sens_attrs reg_govt_shares reg_govt_token auth ver valid_user valid_attrs valid_token valid_query user_set attrs_set users_attr_creation
  for reg_govt_shares reg_govt_token auth ver valid_user valid_attrs valid_token valid_query user_set attrs_set users_attr_creation
    + 
  assumes valid_user_valid_plains: "\<forall> u0 u1. valid_user u0 \<and> valid_user u1  \<longleftrightarrow> valid_plains (snd (users_attr_creation u0)) (snd (users_attr_creation u1))"
begin


definition sens_hiding_adversary1 :: "(('m \<times> 'm) \<times> 'n) spmf \<Rightarrow> 'a \<Rightarrow> (('c set \<times> 'c set) \<times> 'n) spmf"
  where "sens_hiding_adversary1 \<A>1 pk = do {
    ((u0,u1), \<sigma>) \<leftarrow> \<A>1;
    _ :: unit \<leftarrow> assert_spmf (valid_user u0 \<and> valid_user u1);
    let sens_set0 = snd (users_attr_creation u0);
    let sens_set1 = snd (users_attr_creation u1);
    return_spmf ((sens_set0, sens_set1), \<sigma>)}"

definition sens_hiding_adversary2 :: "('n \<Rightarrow> 'd \<Rightarrow> bool spmf) \<Rightarrow> 'd \<Rightarrow> 'n \<Rightarrow> bool spmf"
  where "sens_hiding_adversary2 \<A>2 enc \<sigma> = \<A>2 \<sigma> enc"

fun sens_hiding_adversary:: "(('m \<times> 'm) \<times> 'n) spmf \<times> ('n \<Rightarrow> 'd \<Rightarrow> bool spmf) \<Rightarrow> ('a \<Rightarrow> (('c set \<times> 'c set) \<times> 'n) spmf) \<times> ('d \<Rightarrow> 'n \<Rightarrow> bool spmf)"
  where "sens_hiding_adversary (\<A>1, \<A>2) = (sens_hiding_adversary1 \<A>1, sens_hiding_adversary2 \<A>2)"

lemma if_cases_sens_hiding_attrs:
  shows "(if b then fst (fst ((snd (users_attr_creation (fst (fst y))), snd (users_attr_creation (snd (fst y)))), snd y))
             else snd (fst ((snd (users_attr_creation (fst (fst y))), snd (users_attr_creation (snd (fst y)))), snd y))) =
                 snd (users_attr_creation (if b then fst (fst y) else snd (fst y)))"
  by(cases b; auto)
declare[[show_types]]
term "enc.advantage"
term "id_sys.sens_attrs_hiding_advantage"
lemma sens_attrs_hiding_reduce_to_ind_cpa:
  shows "id_sys.sens_attrs_hiding_advantage \<A> = enc.advantage (sens_hiding_adversary \<A>)"
  unfolding id_sys.reg_def id_sys.sens_attrs_hiding_advantage_def enc.advantage_def enc.ind_cpa_def id_sys.sens_attrs_hiding_game_def reg_enc_sens_attrs_def
  including monad_normalisation
proof-
  note [simp] = split_def Let_def
  obtain \<A>1 and \<A>2 where \<A> [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  have "id_sys.sens_attrs_hiding_advantage (\<A>1, \<A>2) = enc.advantage (sens_hiding_adversary1 \<A>1, sens_hiding_adversary2 \<A>2)"
  proof-
    have "TRY coin_spmf \<bind>
           (\<lambda>b. key_gen \<bind>
                 (\<lambda>y. \<A>1 \<bind>
                       (\<lambda>p. encrypt (fst y) (snd (users_attr_creation (if b then fst (fst p) else snd (fst p)))) \<bind>
                             (\<lambda>enc_attrs_b.
                                 \<A>2 (snd p) enc_attrs_b \<bind> (\<lambda>b'. assert_spmf (valid_user (fst (fst p)) \<and> valid_user (snd (fst p))) 
                                     \<bind> (\<lambda>_ :: unit. return_spmf (b' = b))))))) ELSE coin_spmf = 
          TRY coin_spmf \<bind>
                     (\<lambda>b. key_gen \<bind>
                           (\<lambda>p. \<A>1 \<bind>
                                 (\<lambda>y. encrypt (fst p) (snd (users_attr_creation (if b then fst (fst y) else snd (fst y)))) \<bind>
                                       (\<lambda>cipher.
                                           \<A>2 (snd y) cipher \<bind>
                                           (\<lambda>b'. assert_spmf (valid_user (fst (fst y)) \<and> valid_user (snd (fst y))) \<bind>
                                                  (\<lambda>ya :: unit. assert_spmf (valid_plains (snd (users_attr_creation (fst (fst y)))) (snd (users_attr_creation (snd (fst y))))) \<bind>
                                                         (\<lambda>_ :: unit. return_spmf (b = b')))))))) ELSE coin_spmf"
      apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ using valid_user_valid_plains by force
    thus ?thesis
      unfolding id_sys.sens_attrs_hiding_advantage_def enc.advantage_def id_sys.sens_attrs_hiding_game_def 
        enc.ind_cpa_def reg_enc_sens_attrs_def sens_hiding_adversary1_def sens_hiding_adversary2_def
      by(auto simp add: if_cases_sens_hiding_attrs) 
  qed
  then show ?thesis by auto
qed

corollary perfect_sens_attrs_hiding:
  "id_sys.perfect_sens_attrs_hiding \<A>" if "enc.advantage (sens_hiding_adversary \<A>) = 0"
  unfolding id_sys.perfect_sens_attrs_hiding_def
  by (simp add: sens_attrs_hiding_reduce_to_ind_cpa that)

end

(*To consider token hiding we need to define the token value that is returned to the user in the registration phase as being an encrypted value*)

end