theory Germany imports
  Decentralised_Model
begin

locale germany =
  fixes gen_card :: "'user \<Rightarrow> ('card \<times> 'chip) spmf"
    and auth :: "('card \<times> 'chip) \<Rightarrow> ('user, 'query_out) query \<Rightarrow> 'query_out spmf"
    and valid_user :: "'user \<Rightarrow> bool"
    and valid_query :: "('user, 'query_out) query \<Rightarrow> bool"
  assumes lossless_gen_card: "lossless_spmf (gen_card user)"
begin

definition register :: "'user \<Rightarrow> (('card \<times> 'chip) \<times> (unit, unit) govt_store_data) spmf"
  where 
    "register user = do {
      (card, chip) \<leftarrow> gen_card user;
      return_spmf ((card, chip), ({}, {}))}"

sublocale germany_id: decentralised_id register auth valid_user valid_query 
  unfolding decentralised_id_def by(simp add: register_def lossless_gen_card)

lemma "germany_id.perfect_sens_attrs_hiding \<A>"
proof(rule germany_id.no_sens_attrs_imp_perfect_sens_attrs_hiding)
  show " \<forall>user token store_non_sens_attr store_sens_attr. (token, store_non_sens_attr, store_sens_attr) \<in> set_spmf (register user) \<longrightarrow> store_sens_attr = {}"
    by(simp add: register_def)
qed

