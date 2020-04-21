theory DuAtallah imports
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
  Semi_Honest
  Uniform_Sampling
begin
sledgehammer_params[timeout = 1000]
locale du_atallah_base =
  fixes q :: nat
  assumes q_gt_0 [simp]: "q > 0"
begin

(*definition funct_set :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) set"
  where "funct_set a b = {(s_a,s_b,s_c). (s_a + s_b + s_c) mod q = (a * b) mod q}"

fun funct :: "nat list \<Rightarrow> (nat list) spmf"
  where 
   "funct [a,b] = do {
       (s_a,s_b,s_c) \<leftarrow> spmf_of_set (funct_set a b);
       return_spmf [s_a,s_b,s_c]}"*)

fun reconstruct :: "nat list \<Rightarrow> nat spmf"
  where "reconstruct [s_a,s_b,s_c] = return_spmf ((s_a + s_b + s_c) mod q)"
    
fun funct :: "nat list \<Rightarrow> (nat list) spmf"
  where 
    "funct [a,b] = do {
      a1 \<leftarrow> sample_uniform q;
      a2 \<leftarrow> sample_uniform q;
      let s_a = (q - (a1 * (b + a2)) mod q) mod q;
      let s_b = (b * (a + a1)) mod q;
      let s_c = (a1 * a2) mod q;
      return_spmf [s_a,s_b,s_c]}"

fun protocol :: "nat list \<Rightarrow> (nat list) spmf"
  where 
    "protocol [a,b] = do {
      a1 \<leftarrow> sample_uniform q;
      a2 \<leftarrow> sample_uniform q;
      let s_a = (q - (a1 * (b + a2)) mod q) mod q;
      let s_b = (b * (a + a1)) mod q;
      let s_c = (a1 * a2) mod q;
      return_spmf [s_a,s_b,s_c]}"

(*lemma correct_sum: 
  assumes "a < q" and "b < q" and "a1 < q" and "a2 < q" and "a \<noteq> 0" and "b \<noteq> 0"
  shows
    "(q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q) mod q = (a * b) mod q"
proof(cases "a1 = 0")
  case True
  then show ?thesis 
    by (simp add: semiring_normalization_rules(7))
next
  case False
  have *: "[(b * (a + a1) + (a1 * a2)) mod q = (a1 * (b + a2)) mod q + (a * b) mod q] (mod q)" 
  proof -
    have "b * (a + a1) + a1 * a2 = a1 * b + (a * b + a2 * a1)"
      using left_add_mult_distrib by auto
    then have "b * (a + a1) + a1 * a2 = b * a1 + (a2 * a1 + b * a)"
      by auto
    then show ?thesis
      by (metis (no_types) cong_def cong_mod_left left_add_mult_distrib mod_add_eq semiring_normalization_rules(7))
  qed
  have q_sq [simp]: "q * q \<ge> q" using q_gt_0 
    using le_square by blast
  have "[q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q 
            = q - (a1 * (b + a2)) mod q + (b * (a + a1) + (a1 * a2)) mod q] (mod q)"
    using cong_def assms mod_add_right_eq 
    by (metis (mono_tags, lifting) add.assoc mod_add_eq)
  hence "[q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q + (a1 * (b + a2)) mod q
            = q + (b * (a + a1) + (a1 * a2)) mod q] (mod q)"
    by (smt add.assoc add.commute cong_def le_add_diff_inverse2 mod_add_left_eq mod_le_divisor q_gt_0)
  hence "[q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q + (a1 * (b + a2)) mod q
            = q + (a1 * (b + a2)) mod q + (a * b) mod q] (mod q)" using * cong_def 
    by (simp add: \<open>\<And>c b a. [b = c] (mod a) = (b mod a = c mod a)\<close> add.assoc)
  hence "[q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q
            = (a * b) mod q] (mod q)" 
    by (smt "*" \<open>[q - a1 * (b + a2) mod q + b * (a + a1) mod q + a1 * a2 mod q + a1 * (b + a2) mod q = q + (b * (a + a1) + a1 * a2) mod q] (mod q)\<close> add.assoc cong_add_lcancel_nat cong_mod_right cong_trans linordered_field_class.sign_simps(2) linordered_field_class.sign_simps(3) mod_add_right_eq mod_add_self1)
  hence "[q - (a1 * (b + a2)) mod q + b * (a + a1) mod q + (a1 * a2) mod q
            = (a * b)] (mod q)"  
    using cong_def by simp
  thus ?thesis 
    using cong_def by blast
qed
*)

(*lemma 1:  assumes "a < q" and "b < q" and "y < q" and "ya < q" 
  shows "((a * b + (q - y) + (q - ya)) mod q + y + ya) mod q = ((q - (y * (b + ya)) mod q) mod q + b * (a + y) mod q + y * ya mod q) mod q"
(is "?lhs = ?rhs")
proof-
  have *: "(y + ya + (q - y) + (q - ya)) mod q = 0" 
    using assms by auto
  have "?lhs = (a * b) mod q" 
  proof-
    have "?lhs = (a * b + (q - y) + (q - ya) + y + ya) mod q" 
      by (metis mod_add_left_eq)
    also have "... = (a * b + (y + ya + (q - y) + (q - ya)) mod q) mod q"
      by (simp add:  Groups.add_ac(2) mod_add_right_eq semiring_normalization_rules(22))
    ultimately show ?thesis using * by simp
  qed
  moreover have "?rhs = (a * b) mod q" 
  proof-
    have "?rhs = (b * (a + y) mod q + y * ya mod q + q - (y * (b + ya)) mod q mod q) mod q" 
    proof -
      have "b * (a + y) mod q + y * ya mod q + q - y * (b + ya) mod q mod q = q - y * (b + ya) mod q + (b * (a + y) mod q + y * ya mod q)"
        by (simp add: linordered_field_class.sign_simps(2))
      then show ?thesis
        by (metis (no_types) linordered_field_class.sign_simps(1) mod_add_left_eq)
    qed
    hence *: "?rhs = (b * (a + y) + y * ya + q - (y * (b + ya)) mod q) mod q" 
      by (smt cong_def Nat.add_diff_assoc mod_add_eq mod_le_divisor mod_mod_trivial q_gt_0)
    hence *: "?rhs = (y * (b + ya) + b * a + q - (y * (b + ya)) mod q) mod q" 
      by (smt add.commute left_add_mult_distrib mult.commute)
    hence *: "?rhs = (b * a + q + y * (b + ya) - (y * (b + ya)) mod q) mod q" 
      by (simp add: add.assoc add.commute)
    hence *: "?rhs = (b * a + q + (y * (b + ya)) mod q - (y * (b + ya)) mod q) mod q" 
    proof -
      have f1: "\<forall>n na. q + na - n mod q = q - n mod q + na"
        using Nat.add_diff_assoc2 mod_le_divisor q_gt_0 by presburger
      have "(b * a + (q - y * (b + ya) mod q + y * (b + ya) mod q)) mod q = (b * a + (q - y * (b + ya) mod q + y * (b + ya))) mod q"
        by (metis mod_add_right_eq)
      then show ?thesis
        using f1 by (metis (no_types) "*" add.assoc add.left_commute)
    qed
    hence *: "?rhs = (b * a + q) mod q" 
      by simp
    thus ?thesis 
      by (simp add: mult.commute)
  qed
  ultimately show ?thesis by auto
qed
*)

lemma  
  shows "funct [a,b] \<bind> (\<lambda> shares. reconstruct shares) = protocol [a,b] \<bind> (\<lambda> shares. reconstruct shares)"
  by auto

(*Party 1 secruity*)

definition "randomness_1 = sample_uniform q"

fun real_view_msgs_1 :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) spmf" 
  where "real_view_msgs_1 [a,b,c] a1 = do {
          a2 :: nat \<leftarrow> sample_uniform q;
          let msg = (b + a2) mod q;
          return_spmf (a, a1, msg)}"

fun outputs_1 :: "nat list \<Rightarrow> nat \<Rightarrow> (nat list) spmf"
  where "outputs_1 [a,b,c] a1 = do {
          a2 :: nat \<leftarrow> sample_uniform q;
          let s_a = (q - (a1 * (b + a2)) mod q) mod q;
          let s_b = (b * (a + a1)) mod q;
          let s_c = (a1 * a2) mod q;
          return_spmf [s_a,s_b,s_c]}"

definition sim1 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) spmf"
  where "sim1 a out1 = do {
           a2 :: nat \<leftarrow> sample_uniform q;  
          return_spmf (a, a2, out1)}"

fun valid_inputs where "valid_inputs [a,b,c] = (a < q \<and> b < q)"

sublocale sec_party1: semi_honest_prob 0 funct protocol outputs_1 randomness_1 real_view_msgs_1 sim1 valid_inputs .

notepad 
begin
  fix a b c a1 :: nat
  have "sec_party1.real_view [a,b,c] = do {
    a1 \<leftarrow> randomness_1;
    view :: (nat \<times> nat \<times> nat) \<leftarrow> real_view_msgs_1 [a,b,c] a1;
    outputs \<leftarrow> outputs_1 [a,b,c] a1;
    return_spmf (view, outputs)}"  
    by(simp add: sec_party1.real_view_def)
  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let msg = (b + a2) mod q;
    let view = (a, a1, msg);
    outputs \<leftarrow> funct [a,b];
    return_spmf (view, outputs)}"
    apply(auto simp add: randomness_1_def )

    apply(intro bind_spmf_cong[OF refl])

    using randomness_1_def
    by auto
  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform q;
    msg :: nat \<leftarrow> map_spmf (\<lambda> a2. (b + a2) mod q) (sample_uniform q);
    let view = (a, a1, msg);
    outputs \<leftarrow> funct [a,b,c];
    return_spmf (view, outputs)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform q;
    msg :: nat \<leftarrow> sample_uniform q;
    let view = (a, a1, msg);
    outputs \<leftarrow> funct [a,b,c];
    return_spmf (view, outputs)}"
    by(simp add: samp_uni_plus_one_time_pad)



lemma "sec_party1.real_view inputs = sec_party1.ideal_view inputs"
  unfolding sec_party1.real_view_def sec_party1.ideal_view_def randomness_1_def funct_def