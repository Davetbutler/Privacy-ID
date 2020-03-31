theory Shared_Centralised_Instance imports 
  Centralised_Model
  Game_Based_Crypto.Game_Based_Crypto
begin

sledgehammer_params[timeout = 1000]

type_synonym ('share1_sens', 'share2_sens', 'share3_sens') share_user_record = "('share1_sens' \<times> 'share2_sens' \<times> 'share3_sens') set"

type_synonym ('user', 'result') query = "'user' \<Rightarrow> 'result'"

type_synonym ('attrs', 'sens_atrrs') user_attrs = "('attrs' set \<times> 'sens_atrrs' set)" 

type_synonym ('user', 'state_attr_hid', 'enc_attrs') attr_hiding_adversary
  = "(('user' \<times> 'user') \<times> 'state_attr_hid') spmf \<times> ('state_attr_hid' \<Rightarrow> 'enc_attrs' \<Rightarrow> bool spmf)"

type_synonym ('user', 'state_attr_hid', 'share1_sens', 'share2_sens', 'share3_sens') attr_hiding_adversary'
  = "(('user' \<times> 'user') \<times> 'state_attr_hid') spmf \<times> ('state_attr_hid' \<Rightarrow> ('share1_sens', 'share2_sens', 'share3_sens') share_user_record \<Rightarrow> bool spmf)"

type_synonym ('token', 'state',  'auth_token') hiding_adversary = "(('token' \<times> 'token') \<times> 'state') spmf \<times> ('state' \<Rightarrow> 'auth_token' \<Rightarrow> bool spmf)"

type_synonym 'token' soundness_adversary = "'token' \<Rightarrow> 'token' spmf"

locale identity_system =
  fixes reg_enc_sens_attrs :: "'sens_atrrs set \<Rightarrow> ('enc_attrs set) spmf" \<comment> \<open>The user encrypts their attributes before sending them to the government.\<close> 
    and reg_govt_shares :: "'enc_attrs set \<Rightarrow> (('share1_sens, 'share2_sens, 'share3_sens) share_user_record \<times> 'state_govt) spmf"
    and reg_govt_token :: "'state_govt \<Rightarrow> ('share1_sens, 'share2_sens, 'share3_sens) share_user_record \<Rightarrow> 'token spmf"
    \<comment> \<open>The government first produces the shares of the user record and then a token to be sent back to the user.\<close>
    and auth :: "'token \<Rightarrow> ('user, 'result) query \<Rightarrow> 'auth_token spmf" 
    \<comment> \<open>Authentication is run between a user and a service provider. 
    The user inputs their token, the service provider their desired query and an authorised token is returned. This is sent to the government.\<close>
    and ver :: "'auth_token \<Rightarrow> 'result spmf"
    \<comment> \<open>The government uses the authorised token to determine the response to the query.\<close>
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_attrs :: "('attrs set \<times> 'sens_atrrs set) \<Rightarrow> bool" 
    and valid_token :: "'token \<Rightarrow> bool"
    and valid_query :: "('user, 'result) query \<Rightarrow> bool"
    and user_set :: "'user set"
    and attrs_set :: "('attrs set \<times> 'sens_atrrs set) set"
    and users_attr_creation :: "'user \<Rightarrow> ('attrs set \<times> 'sens_atrrs set)"
  assumes users_are_valid: "user \<in> user_set \<longrightarrow> valid_user user"
    and atrrs_are_valid: "attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"
    and user_set_not_empty: "user_set \<noteq> {}"
    and attrs_set_not_empty: "attrs_set \<noteq> {}"
    and bij_betw_users_attrs: "bij_betw users_attr_creation user_set attrs_set"
    and lossless_reg_govt_token: "lossless_spmf (reg_govt_token \<sigma> S)"
    and lossless_reg_govt_shares: "lossless_spmf (reg_govt_shares enc_attrs)"
    and lossless_reg_enc_sens_attrs: "lossless_spmf (reg_enc_sens_attrs sens_attrs)"
    and reg_enc_sens_attrs_empty_set: "enc_attrs_set = set_spmf (reg_enc_sens_attrs {}) \<longrightarrow> enc_attrs_set = {}"
    and reg_govt_shares_empty_set: "A \<in> (set_spmf (reg_govt_shares {})) \<longrightarrow> fst A = {}"
begin

lemma all_users_valid: "\<forall> user. user \<in> user_set \<longrightarrow> valid_user user"   
  using users_are_valid by simp

lemma all_attrs_valid: "\<forall> attrs. attrs \<in> attrs_set \<longrightarrow> valid_attrs attrs"   
  using atrrs_are_valid by simp

text\<open>We define the registration phase using the fixes parameters for the user and government.\<close>

definition reg :: "'user \<Rightarrow> ('token \<times> ('share1_sens, 'share2_sens, 'share3_sens) share_user_record) spmf" 
  where "reg user = do {
   let (attrs, sens_attrs) = users_attr_creation user;
   enc_attrs \<leftarrow> reg_enc_sens_attrs sens_attrs;
   (S, \<sigma>) \<leftarrow> reg_govt_shares enc_attrs;
   token \<leftarrow> reg_govt_token \<sigma> S;
   return_spmf (token, S)}"

sublocale shared_centralised_id: centralised_id reg auth ver valid_user valid_query 
  unfolding centralised_id_def reg_def
  by(simp add: split_def Let_def bind_spmf_const lossless_reg_govt_token lossless_reg_govt_shares lossless_reg_enc_sens_attrs)

definition "no_sens_attr \<longleftrightarrow> (\<forall> user. snd (users_attr_creation user) = {})"

lemma 
  assumes "no_sens_attr"
  shows "shared_centralised_id.perfect_sens_attrs_hiding \<A>"
proof(rule shared_centralised_id.no_sens_attrs_imp_perfect_sens_attrs_hiding)
  show "\<forall>user token store_non_sens_attr store_sens_attr. (token, store_sens_attr) \<in> set_spmf (reg user) \<longrightarrow> store_sens_attr = {}"
    unfolding reg_def using assms[unfolded no_sens_attr_def] reg_enc_sens_attrs_empty_set reg_govt_shares_empty_set 
    by(auto simp add: Let_def split_def)  
qed

end

locale identity_ind_cpa_base = enc: ind_cpa key_gen encrypt decrypt valid_plains 
  for key_gen :: "('pk \<times> 'sk) spmf"
    and encrypt :: "'pk \<Rightarrow> 'sens_atrrs set \<Rightarrow> ('enc_attrs set) spmf"
    and decrypt :: "'sk \<Rightarrow> 'enc_attrs set \<Rightarrow> 'sens_atrrs set option"
    and valid_plains :: "'sens_atrrs set \<Rightarrow> 'sens_atrrs set \<Rightarrow> bool"
begin

definition reg_enc_sens_attrs :: "'sens_atrrs set \<Rightarrow> ('enc_attrs set) spmf"
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
term "id_sys.reg"
sublocale shared_id: centralised_id id_sys.reg auth ver valid_user valid_query 
  using id_sys.shared_centralised_id.centralised_id_axioms by simp 

definition sens_hiding_adversary1 :: "(('j \<times> 'j) \<times> 'n) spmf \<Rightarrow> 'a \<Rightarrow> (('c set \<times> 'c set) \<times> 'n) spmf"
  where "sens_hiding_adversary1 \<A>1 pk = do {
    ((u0,u1), \<sigma>) \<leftarrow> \<A>1;
    \<comment> \<open>_ :: unit \<leftarrow> assert_spmf (valid_user u0 \<and> valid_user u1);\<close>
    let sens_set0 = snd (users_attr_creation u0);
    let sens_set1 = snd (users_attr_creation u1);
    return_spmf ((sens_set0, sens_set1), \<sigma>)}"

definition sens_hiding_adversary2 :: "('n \<Rightarrow> ('e \<times> 'f \<times> 'g) set \<Rightarrow> bool spmf) \<Rightarrow> 'd set \<Rightarrow> 'n \<Rightarrow> bool spmf"
  where "sens_hiding_adversary2 \<A>2 enc \<sigma> = do {
          (S, \<sigma>g) \<leftarrow> reg_govt_shares enc;
          \<A>2 \<sigma> S}"

fun sens_hiding_adversary:: "(('j \<times> 'j) \<times> 'n) spmf \<times> ('n \<Rightarrow> ('e \<times> 'f \<times> 'g) set \<Rightarrow> bool spmf) \<Rightarrow> ('a \<Rightarrow> (('c set \<times> 'c set) \<times> 'n) spmf) \<times> ('d set \<Rightarrow> 'n \<Rightarrow> bool spmf)"
  where "sens_hiding_adversary (\<A>1, \<A>2) = (sens_hiding_adversary1 \<A>1, sens_hiding_adversary2 \<A>2)"

lemma if_cases_sens_hiding_attrs:
  shows "(if b then fst (fst ((snd (users_attr_creation (fst (fst y))), snd (users_attr_creation (snd (fst y)))), snd y))
             else snd (fst ((snd (users_attr_creation (fst (fst y))), snd (users_attr_creation (snd (fst y)))), snd y))) =
                 snd (users_attr_creation (if b then fst (fst y) else snd (fst y)))"
  by(cases b; auto)

lemma sens_attrs_hiding_reduce_to_ind_cpa:
  shows "id_sys.shared_centralised_id.sens_attrs_hiding_advantage (\<A>1, \<A>2) = enc.advantage (sens_hiding_adversary (\<A>1, \<A>2))"
  including monad_normalisation
  unfolding  id_sys.shared_centralised_id.sens_attrs_hiding_advantage_def id_sys.shared_centralised_id.sens_attrs_hiding_game_def id_sys.reg_def reg_enc_sens_attrs_def  enc.advantage_def enc.ind_cpa_def
  apply(simp add: split_def Let_def eq_commute)
  unfolding sens_hiding_adversary1_def sens_hiding_adversary2_def
  by(auto simp add: valid_user_valid_plains if_cases_sens_hiding_attrs Let_def bind_spmf_const id_sys.lossless_reg_govt_token lossless_weight_spmfD split_def)

corollary perfect_sens_attrs_hiding:
  "id_sys.shared_centralised_id.perfect_sens_attrs_hiding (\<A>1, \<A>2)" if "enc.advantage (sens_hiding_adversary (\<A>1, \<A>2)) = 0"
  unfolding id_sys.shared_centralised_id.perfect_sens_attrs_hiding_def 
  using sens_attrs_hiding_reduce_to_ind_cpa that 
  by (simp add: sens_attrs_hiding_reduce_to_ind_cpa)

end 

end
