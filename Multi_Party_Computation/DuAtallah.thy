theory DuAtallah imports
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
  Number_Theory_Aux
  Semi_Honest
  Uniform_Sampling
begin

locale du_atallah_base =
  fixes q :: nat
  assumes q_gt_0 [simp]: "q > 0"
    and prime_q: "prime q"
begin

fun valid_inputs where "valid_inputs [a,b] \<longleftrightarrow> (a < q \<and> b < q)"

fun reconstruct :: "nat list \<Rightarrow> nat spmf"
  where "reconstruct [s_a,s_b,s_c] = return_spmf ((s_a + s_b + s_c) mod q)"
    
fun funct :: "nat list \<Rightarrow> (nat list) spmf"
  where 
    "funct [a,b] = do {
      a1 \<leftarrow> sample_uniform_units q;
      a2 \<leftarrow> sample_uniform q;
      let s_a = (q - (a1 * (b + a2)) mod q) mod q;
      let s_b = (b * (a + a1)) mod q;
      let s_c = (a1 * a2) mod q;
      return_spmf [s_a,s_b,s_c]}"

lemma 
  assumes "msg1 = (b + a2) mod q" and "b < q" and "a < q" and "a2 < q"
  shows "a2 = (msg1 + q - b) mod q"
proof-
  have "[msg1 + q = b + a2] (mod q)" 
    using assms cong_def by force
  hence "[msg1 + q - b = a2] (mod q)"
  proof-
    have "msg1 + q - b > 0" 
      using assms(2) by linarith
    thus ?thesis 
      by (metis \<open>[msg1 + q = b + a2] (mod q)\<close> assms(2) cong_add_lcancel_nat le_add_diff_inverse le_less trans_le_add2)
  qed
  thus ?thesis  
    by(metis mod_if assms(4) cong_def)
qed

fun R1 :: "nat list \<Rightarrow> (nat \<times> nat \<times> nat) spmf"
  where "R1 [a,b] = do {
    a1 \<leftarrow> sample_uniform_units q;
    a2 \<leftarrow> sample_uniform q;
    let msg1 = (b + a2) mod q;
    return_spmf (a, a1, msg1)}"

fun outputs1 :: "nat list \<Rightarrow> (nat \<times> nat \<times> nat) \<Rightarrow> (nat list) spmf"
  where "outputs1 [a,b] view = do {
    let (a, a1, msg1) = view;
    let s_a = (q - (a1 * msg1) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * ((msg1 + q - b) mod q)) mod q; 
    let outputs = [s_a,s_b,s_c];
    return_spmf outputs}"  

fun protocol :: "nat list \<Rightarrow> (nat list) spmf"
  where 
    "protocol [a,b] = do {
      a1 \<leftarrow> sample_uniform_units q;
      a2 \<leftarrow> sample_uniform q;
      let s_a = (q - (a1 * (b + a2)) mod q) mod q;
      let s_b = (b * (a + a1)) mod q;
      let s_c = (a1 * a2) mod q;
      return_spmf [s_a,s_b,s_c]}"

sublocale party1: semi_honest_prob 0 funct outputs1 R1 S1 valid_inputs .

lemma R1_s_a_rewrite:
  assumes "s_a = (q - (a1 * (b + a2)) mod q) mod q" and "a1 < q" and "b < q" and "a2 < q" and "a1 \<noteq> 0"
  shows "(b + a2) mod q = nat (q - (s_a * fst (bezw a1 q)) mod q) mod q"
proof-
  have gcd: "gcd a1 q = 1" 
    using assms prime_field prime_q by presburger
  have "[s_a = q - (a1 * (b + a2)) mod q] (mod q)" using assms(1) cong_def by force
  hence "[int s_a = int q - (int a1 * (int b + int a2)) mod q] (mod q)" 
    by (metis (full_types) cong_int_iff int_ops(7) int_ops(9) mod_le_divisor of_nat_add of_nat_diff q_gt_0)
  hence "[int s_a = - (int a1 * (int b + int a2))] (mod q)" 
    by (metis ab_group_add_class.ab_diff_conv_add_uminus cong_mod_right mod_add_self1 mod_minus_eq)
  hence "[int s_a * fst (bezw a1 q) = - (int a1 * (int b + int a2) * fst (bezw a1 q))] (mod q)" 
    using cong_scalar_right by fastforce
  hence "[int s_a * fst (bezw a1 q) = - ((int a1 * fst (bezw a1 q)) * (int b + int a2))] (mod q)" 
    by (simp add: Groups.mult_ac(2) Groups.mult_ac(3))
  hence "[int s_a * fst (bezw a1 q) = - (1 * (int b + int a2))] (mod q)"  
    by (meson cong_minus_minus_iff cong_scalar_right cong_trans q_gt_0 gcd inverse)
  hence "[- (int s_a * fst (bezw a1 q)) = int b + int a2] (mod q)" 
    using cong_minus_minus_iff by fastforce
  hence "[q - (int s_a * fst (bezw a1 q)) mod q = int b + int a2] (mod q)" 
    by (simp add: cong_def mod_minus_eq)
  hence "(b + a2) mod q = (q - (int s_a * fst (bezw a1 q)) mod q) mod q"
    by (simp add: cong_def int_ops(9))
  thus ?thesis  
    by (smt Euclidean_Division.pos_mod_bound nat_int nat_mod_distrib of_nat_0_less_iff q_gt_0)
qed

notepad 
begin
  fix a b
  assume "valid_inputs [a,b]"
  hence a: "a < q" and b: "b < q" by auto
  have "party1.real_view [a,b] = do {
    a1 \<leftarrow> sample_uniform_units q;
    a2 \<leftarrow> sample_uniform q;
    let msg1 = (b + a2) mod q;
    let view = (a, a1, msg1);
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * (((b + a2) + q - b) mod q)) mod q; 
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"
    apply(simp add: party1.real_view_def Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp)+ 
    using a b   apply auto
    apply (simp add: mod_mult_right_eq)
  proof -
    fix x :: nat and xa :: nat
    assume a1: "b < q"
    assume a2: "xa < q"
    have f3: "\<forall>n. q + n - b = q - b + n"
      using a1 by (metis Nat.add_diff_assoc2 mod_if mod_le_divisor q_gt_0)
    have "\<not> q < b"
      using a1 by linarith
    then show "x * (((b + xa) mod q + q - b) mod q) mod q = x * xa mod q"
      using f3 a2 by (metis Groups.add_ac(2) Groups.add_ac(3) add_diff_inverse_nat mod_add_right_eq mod_add_self1 mod_if)
  qed
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    a2 \<leftarrow> sample_uniform q;
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * (((b + a2) + q - b) mod q)) mod q; 
    let msg1 = nat (q - (s_a * fst (bezw a1 q)) mod q) mod q;
    let view = (a, a1, msg1);
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"
    apply(simp add: Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp)+ 
    using a b R1_s_a_rewrite 
    by blast
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    a2 \<leftarrow> sample_uniform q;
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * (((b + a2) + q - b) mod q)) mod q; 
    let msg1 = nat (q - (s_a * fst (bezw a1 q)) mod q) mod q;
    let view = (a, a1, msg1);
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"




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



lemma *:
  assumes "msg = (b + a2) mod q" and "b < q" and "a2 < q"
  shows "a2 = (msg + (q - b)) mod q"
proof -
  have "\<forall>n. (a2 + (b + n)) mod q = (n + msg) mod q"
    using assms(1) by presburger
  then show ?thesis
    by (metis (no_types) add.commute add_diff_inverse_nat assms(2) assms(3) le_simps(1) mod_add_self1 mod_less not_less)
qed

lemma funct_outputs_eq :assumes "b < q"
  shows "funct [a,b] = sample_uniform_units q \<bind> (\<lambda> a1. real_view_msgs_1 [a,b,c] a1 \<bind> (\<lambda> view. outputs_1 [a,b,c] view))"
    apply(simp add: Let_def)
  apply(intro bind_spmf_cong[OF refl]; clarify?)+
  using * assms by simp

definition sim1 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) spmf"
  where "sim1 a out1 = do {
           a2 :: nat \<leftarrow> sample_uniform q;  
          return_spmf (a, a2, out1)}"

fun valid_inputs where "valid_inputs [a,b,c] = (a < q \<and> b < q)"

sublocale sec_party1: semi_honest_prob 0 funct protocol outputs_1 randomness_1 real_view_msgs_1 sim1 valid_inputs .

lemma b_rewrite:
  assumes "s_a = (q - (a1 * (b + a2)) mod q) mod q" and "a1 \<noteq> 0" and "a1 < q" and "a2 < q" and b_lt_q: "b < q"
  shows "b = ((q - s_a) * (fst (bezw a1 q)) + (q - a2)) mod q"
proof-
  have coprime: "gcd a1 q = 1" 
    using prime_q assms(2) assms(3) prime_field by simp 
  have *: "[- int a2 = (q - a2)] (mod q)" 
    using assms cong_def int_ops(6) by fastforce
  have s_a_lt_q: "s_a < q" using assms by simp
  have "[s_a = (q - (a1 * (b + a2)) mod q)] (mod q)" 
    using assms cong_def by simp
  hence "[s_a + (a1 * (b + a2)) mod q = q] (mod q)"
    by (metis (mono_tags, lifting) cong_def le_add_diff_inverse2 mod_add_left_eq mod_le_divisor q_gt_0)
  hence "[(a1 * (b + a2)) mod q = q - s_a] (mod q)"
    using s_a_lt_q   
    by (metis cong_add_lcancel_nat le_add_diff_inverse le_simps(1))
  hence "[a1 * (b + a2) = q - s_a] (mod q)"
    using cong_mod_left by blast
  hence "[(b + a2) * a1 = q - s_a] (mod q)"
    by (simp add: mult.commute)
  hence "[(b + a2) * a1 * (fst (bezw a1 q)) = (q - s_a) * (fst (bezw a1 q))] (mod q)"
    using cong_int_iff cong_scalar_right by blast
  hence "[(b + a2) * (a1 * (fst (bezw a1 q))) = (q - s_a) * (fst (bezw a1 q))] (mod q)"
    by (simp add: mult.assoc)
  hence "[(b + a2) * 1 = (q - s_a) * (fst (bezw a1 q))] (mod q)"
    using inverse coprime q_gt_0 
    by (smt Num.of_nat_simps(2) Num.of_nat_simps(5) cong_cong_mod_int cong_def cong_scalar_right mult.commute)
  hence **: "[(int b + int a2) = int (q - s_a) * (fst (bezw a1 q))] (mod q)"
    by simp
  hence "[int b = (q - s_a) * (fst (bezw a1 q)) - int a2] (mod q)" 
    by (smt cong_diff_iff_cong_0)
  hence "[b = (q - s_a) * (fst (bezw a1 q)) + (q - a2)] (mod q)" 
    using * ** cong_add by fastforce
  thus ?thesis 
    using b_lt_q by (simp add: cong_def)
qed



notepad 
begin
  fix a b c :: nat
  assume b_lt_q: "b < q"
  have "sec_party1.real_view [a,b,c] = do {
    rand \<leftarrow> randomness_1;
    view :: (nat \<times> nat \<times> nat)  \<leftarrow> real_view_msgs_1 [a,b,c] rand;
    outputs \<leftarrow> outputs_1 [a,b,c] view;
    return_spmf (view, outputs)}"
    by(simp add: sec_party1.real_view_def)
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    view :: (nat \<times> nat \<times> nat)  \<leftarrow> real_view_msgs_1 [a,b,c] a1;
    outputs \<leftarrow> outputs_1 [a,b,c] view;
    return_spmf (view, outputs)}"


  have "sec_party1.real_view [a,b,c] = do {
    rand \<leftarrow> randomness_1;
    view :: (nat \<times> nat \<times> nat)  \<leftarrow> real_view_msgs_1 [a,b,c] rand;
    outputs \<leftarrow> outputs_1 [a,b,c] rand;
    return_spmf (view, outputs)}"
    by(simp add: sec_party1.real_view_def)
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    outputs \<leftarrow> outputs_1 [a,b,c] a1;
    view :: (nat \<times> nat \<times> nat)  \<leftarrow> real_view_msgs_1 [a,b,c] a1;
    return_spmf (view, outputs)}"
    including monad_normalisation
    by(simp add: randomness_1_def)
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    outputs \<leftarrow> outputs_1 [a,b,c] a1;
    msg :: nat \<leftarrow> map_spmf (\<lambda> a2. (b + a2) mod q) (sample_uniform q);
    let view = (a, a1, msg);
    return_spmf (view, outputs)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    a1 \<leftarrow> sample_uniform_units q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * a2) mod q;
    let outputs = [s_a,s_b,s_c];
    msg :: nat \<leftarrow> sample_uniform q;
    let view = (a, a1, msg);
    return_spmf (view, outputs)}"
    by(simp add: samp_uni_plus_one_time_pad)


  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform_units q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let msg = (b + a2) mod q;
    let view = (a, a1, msg);
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * a2) mod q;
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"
    apply(auto simp add: randomness_1_def)
  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform_units q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let msg = nat (((q - s_a) * (fst (bezw a1 q)) + (q - a2)) mod q + a2) mod q;
    let view = (a, a1, msg);
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * a2) mod q;
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"
    apply(simp add: Let_def)
    apply(intro bind_spmf_cong[OF refl]; clarify?)+
    apply auto
    by (metis b_rewrite b_lt_q nat_int_add neq0_conv)
  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform_units q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let s_a = (q - (a1 * (b + a2)) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * a2) mod q;
    let outputs = [s_a,s_b,s_c];
    let msg = nat (((q - s_a) * (fst (bezw a1 q)) + (q - a2)) mod q + a2) mod q;
    let view = (a, a1, msg);
    return_spmf (view, outputs)}"


  also have "... = do {
    a1 :: nat \<leftarrow> sample_uniform q;
    a2 :: nat \<leftarrow> sample_uniform q;
    let msg = (b + a2) mod q;
    let view = (a, a1, msg);
    let s_a = (q - (a1 * msg) mod q) mod q;
    let s_b = (b * (a + a1)) mod q;
    let s_c = (a1 * a2) mod q;
    let outputs = [s_a,s_b,s_c];
    return_spmf (view, outputs)}"
    apply(simp add: Let_def)

    apply(intro bind_spmf_cong[OF refl]; clarify?)+
    apply auto
    by (simp add: mod_mult_right_eq)

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