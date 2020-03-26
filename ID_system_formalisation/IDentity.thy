theory IDentity imports
  CryptHOL.CryptHOL
  Game_Based_Crypto.Game_Based_Crypto
begin

sledgehammer_params[timeout = 1000]

type_synonym ('share1', 'share2', 'share3') share_user_record = "'share1' \<times> 'share2' \<times> 'share3'"

type_synonym 'attrs' query = "'attrs' \<Rightarrow> bool"

type_synonym ('attrs', 'state_attr_hid',  'enc_attrs') attr_hiding_adversary = "(('attrs' \<times> 'attrs') \<times> 'state_attr_hid') spmf \<times> ('state_attr_hid' \<Rightarrow> 'enc_attrs' \<Rightarrow> bool spmf)"

type_synonym ('token', 'state',  'auth_token') hiding_adversary = "(('token' \<times> 'token') \<times> 'state') spmf \<times> ('state' \<Rightarrow> 'auth_token' \<Rightarrow> bool spmf)"

type_synonym 'token' soundness_adversary = "'token' \<Rightarrow> 'token' spmf"

locale identity =
  fixes reg_user :: "'attrs \<Rightarrow> 'enc_attrs spmf" \<comment> \<open>The user encrypts their attributes before sending them to the government.\<close> 
    and reg_govt_shares :: "'enc_attrs \<Rightarrow> (('share1, 'share2, 'share3) share_user_record \<times> 'state_govt) spmf"
    and reg_govt_token :: "'state_govt \<Rightarrow> ('share1, 'share2, 'share3) share_user_record \<Rightarrow> 'token spmf"
\<comment> \<open>The government first produces the shares of the user record and then a token to be sent back to the user.\<close>
    and auth :: "'token \<Rightarrow> 'attrs query \<Rightarrow> 'auth_token spmf" 
\<comment> \<open>Authentication is run between a user and a service provider. 
    The user inputs their token, the service provider their desired query and an authorised token is returned. This is sent to the government.\<close>
    and ver :: "'auth_token \<Rightarrow> bool spmf"
\<comment> \<open>The government uses the authorised token to determine the response to the query.\<close>
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_attrs :: "'attrs \<Rightarrow> bool" 
    and valid_token :: "'token \<Rightarrow> bool"
    and valid_query :: "'attrs query \<Rightarrow> bool"
    and user_set :: "'user set"
    and attrs_set :: "'attrs set"
    and users_to_attributes :: "'user \<Rightarrow> 'attrs"
  assumes users_are_valid: "user \<in> user_set \<longrightarrow> valid_user user"
    and atrrs_are_valid: "attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"
    and user_set_not_empty: "user_set \<noteq> {}"
    and attrs_set_not_empty: "attrs_set \<noteq> {}"
    and bij_betw_users_attrs: "bij_betw users_to_attributes user_set attrs_set"
    (*and service_providers :: "'providers set"
    and fed_govt :: "'dept set" *)
(*user sets can be parameters of the system, what assumptions need to be made on them?*)
begin

lemma all_users_valid: "\<forall> user. user \<in> user_set \<longrightarrow> valid_user user"   
  using users_are_valid by simp

lemma all_attrs_valid: "\<forall> attrs. attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"   
  using atrrs_are_valid by simp

text\<open>We define the registration phase using the fixes parameters for the user and government.\<close>

definition reg :: "'user \<Rightarrow> ('token \<times> ('share1, 'share2, 'share3) share_user_record) spmf" 
  where "reg user = do {
   let attrs = users_to_attributes user;
   enc_attrs \<leftarrow> reg_user attrs;
   (S, \<sigma>) \<leftarrow> reg_govt_shares enc_attrs;
   token \<leftarrow> reg_govt_token \<sigma> S;
   return_spmf (token, S)}"

subsection\<open>Functional Properties\<close>

lemma obtain_user_from_attrs:
  fixes attrs
  assumes "attrs \<in> attrs_set"
  obtains user where "user \<in> user_set" and "users_to_attributes user = attrs"
  using bij_betw_users_attrs[unfolded bij_betw_def] assms
  by auto 

lemma obtain_attrs_from_user:
  fixes user
  assumes "user \<in> user_set"
  obtains attrs where "attrs \<in> attrs_set" "users_to_attributes user = attrs"
  using bij_betw_users_attrs[unfolded bij_betw_def] assms
  by auto 

text\<open>We require that that no two users, with different attributes, will yield the same tokens upon registration. This must be a property of the registration phase the attributes.\<close>

definition "unique_users = (\<forall> user1 user2. user1 \<in> user_set \<longrightarrow> user2 \<in> user_set \<longrightarrow> user1 \<noteq> user2 \<longrightarrow> reg user1 \<noteq> reg user2)"

text \<open>The correctness property ensures if the IDentity system is carried out honestly the correct query result is returned.\<close>

definition correct_game :: "'user \<Rightarrow> 'attrs query \<Rightarrow> bool spmf"
  where "correct_game user query = do {
        let attrs = users_to_attributes user;
        (token, enc_user_record) \<leftarrow> reg user;
        auth_token \<leftarrow> auth token query;
        b \<leftarrow> ver auth_token;
        return_spmf (b = query attrs)}"  

definition "correct \<longleftrightarrow> (\<forall> user query. valid_user user \<longrightarrow> valid_query query \<longrightarrow> spmf (correct_game user query) True = 1)"

primrec reg_attrs_hiding_game :: "('attrs, 'state_attr_hid,  'enc_attrs) attr_hiding_adversary \<Rightarrow> bool spmf"
  where 
    "reg_attrs_hiding_game (\<A>1, \<A>2) = do {
      ((attrs0, attrs1), \<sigma>) \<leftarrow> \<A>1;
      b \<leftarrow> coin_spmf;
      enc_attrs_b \<leftarrow> reg_user (if b then attrs1 else attrs0);
      b' \<leftarrow> \<A>2 \<sigma> enc_attrs_b;
      return_spmf (b = b')}" 

definition "reg_attrs_hiding_advantage \<A> = \<bar>spmf (reg_attrs_hiding_game \<A>) True - 1/2\<bar>"

definition "perfect_reg_attrs_hiding \<A> \<longleftrightarrow> reg_attrs_hiding_advantage \<A> = 0"

definition hiding_game :: "'attrs query \<Rightarrow> ('token, 'state,  'auth_token) hiding_adversary \<Rightarrow> bool spmf"
  where "hiding_game query \<A> = do {
        let (\<A>1, \<A>2) = \<A>;
        ((token0, token1), \<sigma>) \<leftarrow> \<A>1;
        _ :: unit \<leftarrow> assert_spmf (valid_token token0 \<and> valid_token token1);
        b \<leftarrow> coin_spmf;
        auth_token \<leftarrow> auth (if b then token1 else token0) query;
        b' \<leftarrow> \<A>2 \<sigma> auth_token;  
        return_spmf (b = b')}"

definition "hiding_advantage query \<A> = (\<bar>spmf (hiding_game query \<A>) True - 1/2\<bar>)"

definition "perfect_hiding \<A> \<longleftrightarrow> (\<forall> query. valid_query query \<longrightarrow> hiding_advantage query \<A> = 0)" 

definition soundness_game :: "'attrs \<Rightarrow> 'attrs query \<Rightarrow> 'token soundness_adversary \<Rightarrow> bool spmf"
  where "soundness_game attrs query \<A> = do {
        (token1, enc_user_record) \<leftarrow> reg attrs;
        token2 \<leftarrow> \<A> token1;
        _ :: unit \<leftarrow> assert_spmf (valid_token token2);
        auth_token1 \<leftarrow> auth token1 query;
        auth_token2 \<leftarrow> auth token2 query;
        b :: bool \<leftarrow> ver auth_token1;
        b' \<leftarrow> ver auth_token2;
        return_spmf (b \<noteq> b')}"

definition "soundness_advantage attrs query \<A> = \<bar>spmf (soundness_game attrs query \<A>) True\<bar>"

definition "perfect_soundness \<A> \<longleftrightarrow> (\<forall> attrs query. valid_attrs attrs \<longrightarrow> valid_query query \<longrightarrow> soundness_advantage attrs query \<A> = 0)"

end