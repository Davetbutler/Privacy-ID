theory Bidding_Prot imports
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
  OT_Functionalities
  Semi_Honest
  Uniform_Sampling
begin

locale bidding_prot_base =
  fixes q :: nat
  assumes q_gt_0: "q > 0"
begin

fun valid_inputs_ot12 :: "nat inputs_ot12 list \<Rightarrow> bool"
  where "valid_inputs_ot12 [M2 (b0, b1), C1 \<sigma>] = True" 

lemma 1:
  assumes "rb' = (wb + rd') mod q" 
    and "wb < q" 
    and "rd' < q"
  shows "(rb' + (q - wb)) mod q = rd'"
proof-
  have "[rb' + q = wb + rd'] (mod q)"
    using assms cong_def by force
  hence "[rb' + q - wb = rd'] (mod q)"
  proof-
    have "rb' + q - wb > 0" using assms q_gt_0 by simp
    thus ?thesis 
      by (metis (full_types) \<open>[rb' + q = wb + rd'] (mod q)\<close> add_diff_inverse_nat cong_add_lcancel_nat diff_is_0_eq le_simps(1) not_gr_zero)
  qed
  thus ?thesis using cong_def assms 
    by (metis Nat.add_diff_assoc less_or_eq_imp_le mod_if)
qed

lemma 11:
  assumes "wb < q" 
    and "rd' < q"
  shows "((wb + rd') mod q + (q - wb)) mod q = rd'"
  using assms 1 by blast


text\<open>The overall functionality for bidding.\<close>

fun funct_bid :: "nat list \<Rightarrow> ((nat \<times> bool) list) spmf"
  where "funct_bid [s, b, d] = do {
        _ :: unit \<leftarrow> assert_spmf (Max {b,d} \<ge> s);
        let out = (Max {b,d}, (b \<ge> d));
        return_spmf ([out, out, out])}"

fun valid_inputs_f_bid :: "nat list \<Rightarrow> bool"
  where "valid_inputs_f_bid [s, b, d] = (s < q \<and> b < q \<and> d < q)"

lemma 
  assumes "valid_inputs_f_bid [s, b, d]" 
  shows "s < q" "b < q" "d < q"
  using assms by auto

lemma b_wins:
  assumes b_ge_d: "b \<ge> d"
    and b_ge_s: "b \<ge> s"
    and asm: "[(wb_s, w_s), (wb_b, w_b), (wb_d, w_d)] \<in> set_spmf (funct_bid [s, b, d])"
  shows "wb_s = b" "wb_d = b" "wb_b = b"
  using assms by(auto simp add: Let_def max.absorb1) 

lemma d_wins:
  assumes b_ge_d: "d > b"
    and b_ge_s: "d \<ge> s"
    and asm: "[(wb_s, w_s), (wb_b, w_b), (wb_d, w_d)] \<in> set_spmf (funct_bid [s, b, d])"
  shows "wb_s = d" "wb_d = d" "wb_b = d"
  using assms by(auto simp add: Let_def max.absorb2)  

definition funct_MPC1_ideal :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (bool \<times> bool) spmf"
  where "funct_MPC1_ideal s W = do {
    let (wb, w) = W;
    a \<leftarrow> coin_spmf;
    return_spmf (w \<oplus> a, a)}"

fun f_MPC1  :: "nat list \<Rightarrow> (bool list) spmf"
  where "f_MPC1 [b,d] = do {
    a \<leftarrow> coin_spmf;
    let xb = (if b \<ge> d then True else False);
    return_spmf ([xb \<oplus> a,a])}"

fun valid_inputs_mpc1 :: "nat list \<Rightarrow> bool"
  where "valid_inputs_mpc1 [b,d] = (b < q \<and> d < q)"

lemma f_MPC1_contr_b_lt_d:
  assumes "[True, True] \<in> set_spmf (f_MPC1 [b, d]) \<or> [False, False] \<in> set_spmf (f_MPC1 [b, d])"
  shows "\<not> b \<ge> d"
  using assms by auto

lemma f_MPC1_contr_b_ge_d:
  assumes "[False, True] \<in> set_spmf (f_MPC1 [b, d]) \<or> [True, False] \<in> set_spmf (f_MPC1 [b, d])"
  shows "\<not> b < d"
  using assms by auto

lemma b_ge_d_f_MPC1_out:
  assumes "b \<ge> d"
  shows "[False, True] \<in> set_spmf (f_MPC1 [b, d]) \<or> [True, False] \<in> set_spmf (f_MPC1 [b, d])"
  using assms by auto

lemma b_lt_d_f_MPC1_out:
  assumes "d > b"
  shows "[False, False] \<in> set_spmf (f_MPC1 [b, d]) \<or> [True, True] \<in> set_spmf (f_MPC1 [b, d])"
  using assms  by auto

lemma b_lt_d_f_MPC1:
  assumes "b < d" 
    and "[xb ,xd] \<in> set_spmf (f_MPC1 [b, d])"
  shows "xb \<oplus> xd = False"
  using assms by(simp add: Let_def)

datatype inputs_mpc2 = D_mpc2 "(bool \<times> nat)" | S_mpc2 "(nat \<times> bool \<times> nat)"

fun f_MPC2 :: "inputs_mpc2 list \<Rightarrow> bool list spmf"
  where "f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = do {
    let out = (if (yb + (q - yd)) mod q \<ge> s then True else False);
    return_spmf [out, out]}"

lemma "f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = do {
    let out = (if ((yb + (q - yd)) mod q \<ge> s) then True else False);
    return_spmf [out, out]}"
  by auto

fun valid_inputs_mpc2 :: "inputs_mpc2 list \<Rightarrow> bool"
  where "valid_inputs_mpc2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = (yd < q \<and> yb < q \<and> s < q)"

end 

locale bidding_prot = bidding_prot_base 
  +  mpc1_1: semi_honest_prob 0 f_MPC1 protocol_MPC1 outputs_mpc1 randomness mpc1_view_1 S1_MPC1 valid_inputs_mpc1
  +  mpc1_2: semi_honest_prob 1 f_MPC1 protocol_MPC1 outputs_mpc2 randomness mpc1_view_2 S2_MPC1 valid_inputs_mpc1 
  + mpc2: semi_honest_det_correctness f_MPC2 protocol_MPC2 valid_inputs_mpc2
  + mpc2_1: semi_honest_det_security protocol_MPC2 f_MPC2 valid_inputs_mpc2 0 R1_MPC2 S1_MPC2  
  + mpc2_2: semi_honest_det_security protocol_MPC2 f_MPC2 valid_inputs_mpc2 1 R2_MPC2 S2_MPC2 
  + ot12: semi_honest_det_correctness f_ot12 protocol_OT12 valid_inputs_ot12
  + ot12_1: semi_honest_det_security protocol_OT12 f_ot12 valid_inputs_ot12 0 R1_OT12_1 S1_OT12_1 
  + ot12_2: semi_honest_det_security protocol_OT12 f_ot12 valid_inputs_ot12 1 R2_OT12_1 S2_OT12_1 
  for  "protocol_MPC1" 
    and "mpc1_view_1"
    and "S1_MPC1" 
    and "mpc1_view_2" 
    and "S2_MPC1" 
    and protocol_MPC2 
    and "R1_MPC2"
    and S1_MPC2  
    and R2_MPC2 
    and S2_MPC2 protocol_OT12
    and "R1_OT12_1" 
    and  R2_OT12_1
    and S1_OT12_1 S2_OT12_1  
    and outputs_mpc1 
    and randomness 
    and outputs_mpc2
    +  
  assumes MPC1_correct: "protocol_MPC1 [b, d] = f_MPC1 [b, d]"
    and MPC2_correct: "mpc2.correctness [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)]"
    and OT12_correct: "ot12.correctness [M2 msgs, C1 \<sigma>]"
    and MPC1_1: "mpc1_1.perfect_security [m1, m2]"
    and MPC1_2: "mpc1_2.perfect_security [m1, m2]"
    and OT12_sec_P1: "ot12_1.perfect_security [M2 msgs, C1 \<sigma>]"
    and OT12_sec_P2: "ot12_2.perfect_security [M2 msgs, C1 \<sigma>]"
    and MPC2_sec_P1: "mpc2_1.perfect_security [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)]"
    and MPC2_sec_P2: "mpc2_2.perfect_security [D_mpc2 (xd,yd), S_mpc2(s,xb,yb)]"
begin
 

lemma MPC2_correct_unfold: "\<forall> xd yd s xb yb. valid_inputs_mpc2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] \<longrightarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)]"
  using MPC2_correct[unfolded mpc2.correctness_def] by simp

lemma OT12_1_1: 
  assumes "valid_inputs_ot12 [M2 (m0,m1), C1 \<sigma>]" 
  shows "R1_OT12_1 [M2 (m0,m1), C1 \<sigma>] = f_ot12 [M2 (m0,m1), C1 \<sigma>] \<bind> (\<lambda> outputs. S1_OT12_1 (M2 (m0,m1)) (nth outputs 0))"
  using OT12_sec_P1[unfolded ot12_1.perfect_security_def] assms by fastforce

lemma OT12_2_1: 
  assumes "valid_inputs_ot12 [M2 (m0,m1), C1 \<sigma>]" 
  shows "R2_OT12_1 [M2 (m0,m1), C1 \<sigma>] = f_ot12 [M2 (m0,m1), C1 \<sigma>] \<bind> (\<lambda> outputs. S2_OT12_1 (C1 \<sigma>) (nth outputs 1))"
  using OT12_sec_P2[unfolded ot12_2.perfect_security_def] assms by(auto simp add: split_def)

lemma MPC2_1: 
  assumes "valid_inputs_mpc2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)]"
  shows "R1_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] \<bind> (\<lambda> outputs. S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs 0))"
  using MPC2_sec_P1[unfolded mpc2_1.perfect_security_def] assms by simp

lemma MPC2_2:
  assumes "valid_inputs_mpc2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)]"
  shows "R2_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] \<bind> (\<lambda> outputs. S2_MPC2 (S_mpc2 (s,xb,yb)) (nth outputs 1))"
  using MPC2_sec_P2[unfolded mpc2_2.perfect_security_def] assms by simp

lemma MPC2_2_all:
  shows "\<forall> xd yd s xb yb. valid_inputs_mpc2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] \<longrightarrow> R2_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] = f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)] \<bind> (\<lambda> outputs. S2_MPC2 (S_mpc2 (s,xb,yb)) (nth outputs 1))"
  using MPC2_sec_P2[unfolded mpc2_2.perfect_security_def] valid_inputs_mpc2.simps by simp

lemma OT12_2_sec_all : 
  assumes "valid_inputs_ot12 [M2 (m0,m1), C1 \<sigma>]" 
  shows "R2_OT12_1 [M2 (m0,m1), C1 \<sigma>] = f_ot12 [M2 (m0,m1), C1 \<sigma>] \<bind> (\<lambda> outputs. S2_OT12_1 (C1 \<sigma>) (nth outputs 1))"
  using OT12_2_1 assms by fastforce

lemma perfect_1_MPC1_unfold:
  assumes "valid_inputs_mpc1 [b,d]"
  shows "mpc1_1.real_view [b, d] = mpc1_1.ideal_view [b, d]"
  using MPC1_1[unfolded mpc1_1.perfect_security_def] assms by simp

lemma perfect_2_MPC1_unfold:
  assumes "valid_inputs_mpc1 [b,d]"
  shows "mpc1_2.real_view [b, d]  = mpc1_2.ideal_view [b, d]"
  using MPC1_2[unfolded mpc1_2.perfect_security_def] assms by simp

lemma OT12_correct_all: "\<forall> m0 m1 \<sigma>. valid_inputs_ot12 [M2 (m0,m1), C1 \<sigma>] \<longrightarrow> protocol_OT12 [M2 (m0,m1), C1 \<sigma>] = f_ot12 [M2 (m0,m1), C1 \<sigma>]" 
  using OT12_correct[unfolded ot12.correctness_def] 
  by fastforce

lemma OT12_1_unfold: 
  assumes "valid_inputs_ot12 [M2 (m0,m1), C1 \<sigma>]"
  shows "R1_OT12_1 [M2 (m0,m1), C1 \<sigma>] = S1_OT12_1 (M2 (m0,m1)) (U_ot12 ())" 
  using OT12_1_1 assms by fastforce

fun protocol_bid :: "nat list \<Rightarrow> ((nat \<times> bool) list) spmf"
  where "protocol_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> protocol_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> protocol_OT12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> protocol_OT12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);    
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf ([out, out, out])}"

fun R_S_bid :: "nat list \<Rightarrow> (nat \<times> bool \<times> nat \<times> 'e \<times> bool \<times> nat) spmf"
  where "R_S_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> protocol_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> protocol_OT12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> protocol_OT12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);   
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    view  \<leftarrow> R2_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}" 

definition S_S_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> bool \<times> nat \<times> 'e \<times> bool \<times> nat) spmf"
  where "S_S_bid s W = do {
    let (wb,w) = W;
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - wb)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"

sublocale bid_prot_correct: semi_honest_det_correctness funct_bid protocol_bid valid_inputs_f_bid .

sublocale bid_prot_S: semi_honest_det_security _ funct_bid valid_inputs_f_bid 0 R_S_bid S_S_bid   .

lemma 44:
  assumes "xa < q" and "xb < q" and "wb < q" 
  shows "((xa + xb) mod q + (q - ((xa + (q - wb)) mod q + xb) mod q)) mod q = wb"
proof(cases "wb = 0")
  case True
  then show ?thesis 
    by (metis (no_types, lifting) add.commute diff_zero le_add_diff_inverse2 mod_add_left_eq mod_add_self2 mod_le_divisor mod_self q_gt_0)
next
  case False
  let ?y = "(xa + xb) mod q + (q - ((xa + (q - wb)) mod q + xb) mod q)"
  have "[?y = (xa + xb) mod q + (q + q - ((xa + (q - wb)) mod q + xb) mod q)] (mod q)"
    by (metis (no_types, lifting) Nat.add_diff_assoc2 add.assoc cong_def mod_add_self2 mod_le_divisor q_gt_0)
  hence "[?y = (xa + xb) mod q + (q + q - ((xa + (q - wb)) mod q + xb))] (mod q)"
  proof-
    have "(q + q - ((xa + (q - wb)) mod q + xb)) > 0" 
      by (simp add: add_less_mono assms(2) q_gt_0)
    thus ?thesis 
      using add_mono_thms_linordered_semiring(1) assms(2) cong_add_lcancel_nat cong_def cong_diff_nat cong_mod_right less_or_eq_imp_le mod_add_self1 mod_le_divisor q_gt_0 
      by smt
  qed
  hence "[?y = (xa + xb) + (q + q - ((xa + (q - wb)) mod q + xb))] (mod q)"
    by (metis cong_def mod_add_left_eq)
  hence "[?y = xa + xb + (q + q - ((xa + (q - wb)) mod q + xb))] (mod q)"
    by blast
  hence "[?y = xa + (q + q - ((xa + (q - wb)) mod q))] (mod q)"
    by (simp add: add.assoc add_mono_thms_linordered_semiring(1) assms(2) le_simps(1) q_gt_0)
  hence "[?y = xa + (q + q - ((xa + (q - wb))))] (mod q)"
  proof-
    have "xa + (q + q - ((xa + (q - wb)))) > 0"
      using q_gt_0 by linarith
    thus ?thesis 
    proof -
      { assume "[(xa + q) mod q = (wb + (xa + (q - wb))) mod q] (mod q)"
        moreover
        { assume "[(xa + q) mod q = (wb + (xa + (q - wb)) mod q) mod q] (mod q) \<and> (xa + (q - wb)) mod q \<le> q"
          moreover
          { assume "\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (wb + n) mod q] (mod q)"
            then have "(\<exists>n. q + n \<noteq> xa + (q - xa + n)) \<or> (\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (wb + (xa + (q - xa + n))) mod q] (mod q))"
              by (metis (full_types) add.left_commute mod_add_self1)
            moreover
            { assume "\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (wb + (xa + (q - xa + n))) mod q] (mod q)"
              then have "\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (xa + (wb + (q - xa) + n)) mod q] (mod q)"
                by (simp add: ab_semigroup_add_class.add_ac(1) add.left_commute)
              moreover
              { assume "\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (xa + (q + (q - xa) - (q - wb) + n)) mod q] (mod q)"
                moreover
                { assume "\<exists>n. [(xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q = (xa + (q + q - xa - (q - wb) + n)) mod q] (mod q)"
                  then have "\<exists>n. [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q + n) = xa + (q + q - xa - (q - wb) + n)] (mod q)"
                    by (metis (no_types) ab_semigroup_add_class.add_ac(1) cong_cong_mod_nat mod_add_left_eq)
                  then have "[(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
                    by (metis (no_types) ab_semigroup_add_class.add_ac(1) cong_add_rcancel_nat) }
                ultimately have "q \<le> xa \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
                  by (metis (full_types) Nat.diff_add_assoc nat_le_linear) }
              ultimately have "q \<le> xa \<or> q \<le> wb \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
                by (metis (no_types) Nat.add_diff_assoc2 diff_diff_cancel diff_le_self nat_le_linear) }
            ultimately have "q \<le> xa \<or> q \<le> wb \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
              by (metis (no_types) ab_semigroup_add_class.add_ac(1) add_diff_inverse_nat less_or_eq_imp_le)
            then have "q \<le> wb \<or> (\<exists>n na. (n::nat) < na \<and> 0 = na - n) \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
              by (metis (no_types) assms(1) diff_is_0_eq') }
          moreover
          { assume "\<exists>n. (xa + (q - (xa + (q - wb)) mod q + n)) mod q \<noteq> (xa + (xb + (q - (xa + (xb + (q - wb))) mod q + n))) mod q"
            then have "(xa + (q - (xa + (q - wb)) mod q)) mod q \<noteq> ((xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q)) mod q"
              by (metis (no_types) ab_semigroup_add_class.add_ac(1) mod_add_left_eq)
            then have "[(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) \<noteq> q + (xa + (q - (xa + (q - wb)) mod q))] (mod q)"
              by (metis (no_types) cong_def mod_add_self1)
            then have "\<exists>n na. na + q - n mod q \<noteq> na + (q - n mod q)"
              by (metis (no_types) \<open>[(xa + xb) mod q + (q - ((xa + (q - wb)) mod q + xb) mod q) = xa + (q + q - (xa + (q - wb)) mod q)] (mod q)\<close> add.left_commute linordered_field_class.sign_simps(2) mod_add_left_eq)
            then have "\<exists>n. \<not> n mod q \<le> q"
              by (meson Nat.diff_add_assoc) }
          ultimately have "(\<exists>n. \<not> n mod q \<le> q) \<or> q \<le> wb \<or> (\<exists>n na. (n::nat) < na \<and> 0 = na - n) \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
            by (metis (no_types) le_add_diff_inverse2) }
        ultimately have "q \<le> wb \<or> (\<exists>n na. (n::nat) < na \<and> 0 = na - n) \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
          by (metis (no_types) mod_add_right_eq mod_le_divisor q_gt_0) }
      then have "q \<le> wb \<or> (\<exists>n na. (n::nat) < na \<and> 0 = na - n) \<or> [(xa + xb) mod q + (q - (xa + (xb + (q - wb))) mod q) = xa + (q + q - xa - (q - wb))] (mod q)"
        by (metis add.left_commute add_diff_inverse_nat cong_refl less_or_eq_imp_le)
      then show ?thesis
        by (metis (no_types) add.left_commute assms(3) diff_diff_add diff_is_0_eq' linordered_field_class.sign_simps(2) mod_add_left_eq zero_less_diff zero_less_iff_neq_zero)
    qed
  qed
  hence "[?y = xa + q + q - (xa + (q - wb))] (mod q)" 
    by (simp add: add_mono_thms_linordered_semiring(1) assms(1) le_simps(1))
  hence "[?y = wb] (mod q)"  
    by (smt Nat.add_diff_assoc Nat.add_diff_assoc2 add_diff_cancel_left' assms(3) cong_def diff_diff_cancel diff_diff_left diff_le_self le_simps(1) mod_add_self2)
  thus ?thesis 
    by (metis assms(3) cong_def mod_if)
qed

lemma funct_bid_False_d_gt_b:
  assumes "[(a, False), (e, False), (c, False)] \<in> set_spmf (funct_bid [s, b, d])"
  shows "d > b"
  using assms apply(auto simp add: Let_def)
  apply(cases "\<not> s \<le> max b d") by auto

lemma funct_bid_False_d_le_b:
  assumes "[(a, True), (e, True), (c, True)] \<in> set_spmf (funct_bid [s, b, d])"
  shows "d \<le> b"
  using assms apply(auto simp add: Let_def) 
  by (smt ccSUP_bot linorder_not_le list.inject mem_simps(2) prod.inject singletonD)

lemma 555:
  assumes "xa < q" and "xb < q" and "d < q"
  shows "((xa + (d + xb) mod q) mod q + q - (xa + xb) mod q) mod q = d"
proof-
  let ?y = "((xa + (d + xb) mod q) mod q + q - (xa + xb) mod q) mod q"
  have "[?y = ((xa + (d + xb) mod q) mod q + q - (xa + xb) mod q)] (mod q)"
    using cong_def by auto
  hence "[?y = ((xa + (d + xb) mod q) + q - (xa + xb) mod q)] (mod q)"
    by (smt Nat.add_diff_assoc cong_def mod_add_left_eq mod_le_divisor q_gt_0)
  hence "[?y = ((xa + (d + xb)) + q - (xa + xb) mod q)] (mod q)"
    by (smt Nat.add_diff_assoc cong_def mod_add_left_eq mod_add_right_eq mod_le_divisor q_gt_0)
  hence "[?y + (xa + xb) mod q = (xa + (d + xb)) + q] (mod q)" 
    by (smt cong_def le_add2 le_add_diff_inverse2 le_trans mod_add_left_eq mod_le_divisor q_gt_0)
  hence "[?y + xa + xb = (xa + (d + xb)) + q] (mod q)" 
    by (simp add: add.assoc cong_def mod_add_right_eq)
  hence "[?y + xa + xb = xa + xb + d] (mod q)" 
    by (metis (no_types, lifting) add.assoc add.commute cong_def mod_add_self2)
  hence "[?y = d] (mod q)" 
    using cong_def 
    by (smt add.assoc add.commute cong_add_rcancel_nat)
  thus ?thesis using cong_def 
    using assms(3) cong_less_modulus_unique_nat mod_less_divisor q_gt_0 by presburger
qed

lemma S_corrupt:
  assumes "s < q" "b < q" "d < q"
  shows "R_S_bid [s, b, d] = funct_bid [s, b, d] \<bind> (\<lambda> outputs. S_S_bid s (nth outputs 0))"
proof-
  note [simp] = Let_def
  have R_initial: "R_S_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs_ot12 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs_ot12' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs_ot12' 1);  
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
     apply(auto simp add: MPC1_correct OT12_correct_all MPC2_2  split del: if_split)+
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(auto simp add: OT12_correct_all MPC2_2 q_gt_0 split del: if_split)
    subgoal for x
      apply(cases x)
      apply auto
      using MPC2_2_all assms by auto  
    subgoal for x
      apply(cases x)
      apply auto
      using MPC2_2_all assms by auto  
    subgoal for x
      apply(cases x)
      apply auto
      using MPC2_2_all assms by auto  
    subgoal for x
      apply(cases x)
      apply auto
      using MPC2_2_all assms by auto  
    done
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    have R_case_b_ge_d: "R_S_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
      using R_initial 
[[simproc del: let_simp]] apply auto
       apply(intro bind_spmf_cong bind_spmf_cong[OF refl])
      apply simp apply simp apply simp
      using b_ge_d f_MPC1_contr_b_lt_d by blast +
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      have "R_S_bid [s, b, d] = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - (fst (nth outputs 0)))) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        using  R_case_b_ge_d 
        apply(auto simp only: R_case_b_ge_d Let_def)
        using b_ge_d b_ge_s 
        by (simp add: max.absorb1)
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = (snd (nth outputs 0)) \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - (fst (nth outputs 0)))) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
          apply(cases "\<not> s \<le> max b d")
        apply (auto simp add: b_ge_d b_ge_s q_gt_0) 
          apply (metis MPC2_correct assms(1) f_MPC2.simps mod_less_divisor mpc2.correctness_def q_gt_0 valid_inputs_mpc2.simps)
         by (metis b_ge_d b_ge_s ccSUP_bot mem_simps(2) nth_Cons_0 singletonD snd_conv)+
       ultimately show ?thesis 
         unfolding S_S_bid_def by simp
    next
      case False
      have "R_S_bid [s, b, d] = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        using b_ge_d R_case_b_ge_d by simp
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        by(auto simp add: q_gt_0 split_def assms MPC2_correct_unfold)
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    _ :: unit \<leftarrow> assert_spmf False;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+
        apply(auto simp add: q_gt_0) 
        by (metis 44 False Nat.add_diff_assoc assms(2) mod_le_divisor q_gt_0)
      ultimately have "R_S_bid [s, b, d] = return_pmf None"
        by auto
      moreover have "funct_bid [s, b, d] = return_pmf None" 
        using False b_ge_d 
        by(cases "s \<le> max b d"; auto)
      ultimately show ?thesis by auto
    qed
  next
    case False
    hence d_gt_b: "b < d" by simp
    have R_case_d_gt_b: "R_S_bid [s, b, d] = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
      using d_gt_b R_initial 
      apply(auto simp add: split_def)
      by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    thus ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      hence [simp]: "s \<le> max b d" by simp
      have "R_S_bid [s, b, d] = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = ((fst (nth outputs 0)) + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        using  d_gt_b R_case_d_gt_b
        apply auto
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using d_gt_b less_le_not_le max_def 
           apply (metis (no_types, lifting))
          apply (simp add: max_def)
        by (auto simp add: d_gt_b less_imp_le max_absorb2)
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = ((fst (nth outputs 0)) + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - (fst (nth outputs 0)))) mod q) mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
          apply(auto simp add: 11 q_gt_0) 
        by (metis "1" False assms(3) max.commute max_def)+
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> map_spmf (\<lambda> rd'. ((fst (nth outputs 0)) + rd') mod q) (sample_uniform q);
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - (fst (nth outputs 0)))) mod q) mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        by(simp add: bind_map_spmf o_def)
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - (fst (nth outputs 0)))) mod q) mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        by(simp add: samp_uni_plus_one_time_pad)
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = ((rd + (q - (fst (nth outputs 0)))) mod q + rb' mod q) mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
      proof-
        fix wb
        have "wb < q \<longrightarrow> (xa + (xb + (q - wb)) mod q) mod q = ((xa + (q - wb)) mod q + xb) mod q" for xb xa 
          by presburger
        thus ?thesis
          apply(auto simp add: q_gt_0)
           apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
             apply(auto simp add: q_gt_0)
              by(auto simp add: Groups.add_ac(3) linordered_field_class.sign_simps(2) mod_add_right_eq)+
      qed
      also have "... = do {
    outputs \<leftarrow> funct_bid [s, b, d];
    xd \<leftarrow> coin_spmf;
    let xb = (snd (nth outputs 0)) \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - (fst (nth outputs 0)))) mod q;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rb') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
        by (simp add: False mod_add_right_eq)+
      ultimately show ?thesis 
        by(simp add: S_S_bid_def split del: if_split)
    next
      case False
      with d_gt_b have s_gt: "s > b" "s > d" by auto
      have "R_S_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
      using R_initial apply auto    
       apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      using d_gt_b f_MPC1_contr_b_lt_d 
       apply linarith
      by(intro bind_spmf_cong bind_spmf_cong[OF refl];clarsimp)+
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        using d_gt_b by simp
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using MPC2_correct_unfold assms 
        by(auto simp add: split_def assms) 
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view \<leftarrow> S2_MPC2 (S_mpc2 (s, xb, yb)) (nth outputs_mpc2 1);
    _ :: unit \<leftarrow> assert_spmf False;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0) 
        using 555 assms
        by (simp add: False)
      ultimately have "R_S_bid [s, b, d] = return_pmf None"
        by auto
      moreover have "funct_bid [s, b, d] = return_pmf None"
        using s_gt(1) s_gt(2) 
        by(cases "s \<le> max b d"; auto)
      ultimately show ?thesis by simp
    qed
  qed
qed

fun R_B_bid :: "nat list \<Rightarrow> (nat \<times> 'b \<times> bool \<times> nat \<times> 'f \<times> 'g \<times> nat \<times> bool \<times> nat) spmf"
  where "R_B_bid [s, b, d] = do {
    (view_MPC1, outputs_mpc1) \<leftarrow> mpc1_1.real_view [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'f \<leftarrow> R1_OT12_1 [M2 input1, C1 xd];
    outputs \<leftarrow> protocol_OT12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view2_OT12 :: 'g \<leftarrow> R2_OT12_1 [M2 input1', C1 xb];
    outputs' \<leftarrow> protocol_OT12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);   
    let yd = (rd + rd') mod q;   
    let yb = (rb + rb') mod q;
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"

fun R_D_bid :: "nat list \<Rightarrow> (nat \<times> 'c \<times> bool \<times> 'g \<times> nat \<times> nat \<times> 'f \<times> 'd \<times> bool \<times> nat \<times> bool) spmf"
  where "R_D_bid [s, b, d] = do {
    (view_MPC2, outputs_mpc1) \<leftarrow> mpc1_2.real_view [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    view2_OT12  \<leftarrow> R2_OT12_1 [M2 input1, C1 xd];
    outputs \<leftarrow> protocol_OT12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'f \<leftarrow> R1_OT12_1 [M2 input1', C1 xb];
    outputs' \<leftarrow> protocol_OT12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1); 
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 :: 'd \<leftarrow> R1_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    outputs_mpc2 :: bool list \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"

definition S_D_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> 'c \<times> bool \<times> 'g \<times> nat \<times> nat \<times> 'f \<times> 'd \<times> bool \<times> nat \<times> bool) spmf"
  where "S_D_bid d W = do {
        let (wb, w) = W;
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb \<leftarrow> sample_uniform q; 
        view2_OT12 \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rb + rd') mod q; 
        let yb = ((rb + wb) + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"

sublocale bid_prot_D: semi_honest_det_security _ funct_bid valid_inputs_f_bid 2 R_D_bid S_D_bid .

lemma correct2:
  assumes "x < q" 
    and "xa < q"
    and "b < q"
  shows "((x + xa) mod q + q - ((x + q - b) mod q + xa) mod q) mod q = b"
proof-
  have "[((x + xa) mod q + q - ((x + q - b) mod q + xa) mod q) = ((x + xa) + q - ((x + q - b) mod q + xa) mod q)] (mod q)"
    using cong_def assms 
    by (smt Nat.add_diff_assoc cong_def le_simps(1) mod_add_left_eq q_gt_0 unique_euclidean_semiring_numeral_class.pos_mod_bound)
  hence "[((x + xa) mod q + q - ((x + q - b) mod q + xa) mod q) = ((x + xa) + q - ((x + q - b) mod q + xa))] (mod q)"
  proof-
    have "((x + xa) + q - ((x + q - b) mod q + xa)) > 0"
      using assms q_gt_0 
      by (smt add.commute add_cancel_right_left add_less_cancel_left add_mono_thms_linordered_field(5) less_add_same_cancel2 neq0_conv unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_diff)
    thus ?thesis 
      by (smt Nat.add_diff_assoc add_gr_0 cong_def cong_diff_nat le_simps(1) mod_add_left_eq mod_mod_trivial q_gt_0 unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_diff)
  qed
  hence "[((x + xa) mod q + q - ((x + q - b) mod q + xa) mod q) = ((x + xa) + q - ((x + q - b) + xa))] (mod q)"
    by (smt Nat.add_diff_assoc2 ab_semigroup_add_class.add_ac(1) add.commute add_gr_0 add_less_cancel_right cong_def cong_diff_nat diff_less diff_zero gr_implies_not_zero le_simps(1) linorder_neqE_nat linorder_not_less mod_add_left_eq mod_mod_trivial q_gt_0 unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_diff)
  hence "[((x + xa) mod q + q - ((x + q - b) mod q + xa) mod q) = b] (mod q)" 
    by (smt add.commute add.left_commute add_diff_cancel_left' add_diff_inverse_nat assms(3) le_simps(1) not_le)
  thus ?thesis by(simp add: cong_def assms)
qed

lemma 77:
  assumes "b < q" and "xb < q" and "xd < q"
  shows "((xb + xd) mod q + (q - ((xb + (q - b)) mod q + xd) mod q)) mod q = b"
proof-
  have "((xb + xd) mod q + (q - ((xb + (q - b)) mod q + xd) mod q)) mod q = ((xb + xd) mod q + q - ((xb + (q - b)) mod q + xd) mod q) mod q"
    by (simp add: q_gt_0)
  thus ?thesis using assms correct2 by simp
qed

lemma 88: 
  assumes "xa < q" and "xc < q" and "d < q"
  shows "((xa + (d + xc) mod q) mod q + (q - (xa + xc) mod q)) mod q = d"
proof(cases "d = 0")
  case True
  then show ?thesis using assms by simp
next
  case False
  let ?y = "((xa + (d + xc) mod q) mod q + (q - (xa + xc) mod q))"
  have "[?y = ((xa + (d + xc) mod q) + (q - (xa + xc) mod q))] (mod q)"
    using cong_def mod_add_left_eq by blast
  hence "[?y + q = ((xa + (d + xc)) + (q - (xa + xc) mod q))] (mod q)"
    by (simp add: add.commute cong_def mod_add_right_eq)
  hence "[?y + q - (q - (xa + xc) mod q) = ((xa + (d + xc)))] (mod q)"
  proof-
    have "?y + q - (q - (xa + xc) mod q) > 0" 
      using assms False 
      by linarith
    thus ?thesis 
      by (simp add: cong_def mod_add_right_eq)
  qed
  hence "[?y + (xa + xc) mod q = ((xa + (d + xc)))] (mod q)" 
    by (simp add: q_gt_0)
  hence "[?y + (xa + xc) = (xa + (d + xc))] (mod q)" 
    by (simp add: cong_def mod_add_right_eq)
  hence "[?y + xa + xc = xa + d + xc] (mod q)"
    by (simp add: add.assoc)
  hence "[?y = d] (mod q)" 
    by (metis add.commute cong_add_lcancel_nat)
  thus ?thesis 
    by (metis assms(3) cong_def mod_if)
qed


lemma 99:
  assumes "b < q" and "rb < q"
  shows "((rb + (q - b)) mod q + b) mod q = rb"
proof-
  let ?y = "(rb + (q - b)) mod q"
  have "[?y = rb + (q - b)] (mod q)"
    using assms cong_def by simp
  hence "[?y + b = rb] (mod q)" using assms 
    by (metis (mono_tags, lifting) add.assoc cong_def le_add_diff_inverse2 less_or_eq_imp_le mod_add_left_eq mod_add_self2)
  thus ?thesis using assms cong_def 
    by (metis mod_if)
qed

lemma not_b_ge_d_imp_False: "\<not> d \<le> b \<longrightarrow> ((if d \<le> b then True else False) = False)"
  by simp

lemma D_corrupt:
  assumes  "s < q" "b < q" "d < q"
  shows "R_D_bid [s, b, d] = funct_bid [s, b, d] \<bind> (\<lambda> outputs. S_D_bid d (nth outputs 2))"
proof-
  have "R_D_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    view2_OT12 :: 'g \<leftarrow> R2_OT12_1 [M2 input1, C1 xd];
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1); 
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 :: 'd \<leftarrow> R1_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
    using assms
    apply(auto simp add: split_def Let_def perfect_2_MPC1_unfold semi_honest_prob.ideal_view_def bind_map_spmf)
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto using OT12_correct_all apply auto 
    using OT12_1_unfold valid_inputs_ot12.simps apply blast +
    apply(simp add: f_ot12_if_unfold) using OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 
    subgoal for x 
      apply(cases x) 
      by auto 
   apply(simp add: f_ot12_if_unfold) using OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 
    subgoal for x 
      apply(cases x) 
      by auto 
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
    apply auto 
    using OT12_1_unfold valid_inputs_ot12.simps apply blast 
    using OT12_1_unfold valid_inputs_ot12.simps apply blast
       apply(auto simp add:  OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 split del: if_split)
      using MPC2_correct[unfolded mpc2.correctness_def] assms 
      by (auto simp add: OT12_correct_all OT12_1_unfold)
  also have "... = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd'' = output_ot_rev (nth outputs_ot12 1);
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs_ot12 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 :: 'd \<leftarrow> R1_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
    apply(auto simp add: OT12_2_1 split_def Let_def) 
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using  assms 
      apply(auto simp add: OT12_2_1 split_def Let_def) 
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    by(simp add: OT12_2_1 split_def Let_def) 
  also have "... = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd'' = output_ot_rev (nth outputs_ot12 1);
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs_ot12 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
    outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
    apply(simp only: Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    apply auto
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using assms MPC2_1 assms
    by(auto simp add: q_gt_0 split_def)
  ultimately have R_initial: "R_D_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd'' = output_ot_rev (nth outputs_ot12 1);
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
    outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs_ot12 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
    outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
    by argo
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    have R_case_b_ge_d: "R_D_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs 1);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
      using R_initial
      apply(simp add: Let_def R_initial  split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+ 
      apply auto
      using f_MPC1_contr_b_lt_d b_ge_d by auto
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      have 1: "(if False then True else False) = False" by simp
      have 2: "(False = (\<not> x)) = x" for x by simp
      have 3: "(if True then True else False) = True" by simp
      have "R_D_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        let rd = (rb + (q - b)) mod q;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        using R_case_b_ge_d  R_initial
        apply(auto simp add: Let_def)  
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+
        apply simp apply simp apply simp apply simp
        using f_MPC1_contr_b_lt_d b_ge_d  by blast +
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
         outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+ 
        by(auto simp add: 1 2 b_ge_d 3 f_ot12_if_unfold)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(auto simp add: Let_def) 
        apply(cases "s \<le> max b d")
        apply auto
        using b_ge_s apply presburger +
        using b_ge_d by blast
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 77 assms 
        by (metis b_ge_s lessThan_iff q_gt_0 set_spmf_sample_uniform)+
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 99 assms by(simp add: Let_def q_gt_0)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = ((q - b) + rb) mod q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof-
        have "((q - b) + rb) mod q = (rb + (q - b)) mod q" for rb 
          using add.commute by presburger
        thus ?thesis by(simp add: Let_def)
      qed
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> map_spmf (\<lambda> rb.((q - b) + rb) mod q) (sample_uniform q); 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        by(simp add: bind_map_spmf o_def Let_def)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        by(simp add: samp_uni_plus_one_time_pad)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + (fst (nth outputs 2))) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(auto simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0)
        by (metis max.orderE b_ge_d) 
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + (fst (nth outputs 2))) mod q + rd') mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof-
        have "((rd'' + wb) mod q + rd') mod q = ((rd'' + wb) + rd') mod q" for rd' rd'' wb
          using mod_add_left_eq by blast
        thus ?thesis by(simp)
      qed
      ultimately show ?thesis   
        apply(auto simp add: S_D_bid_def Let_def)
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
          by (simp add: mod_add_left_eq)
    next
      case False
      have *: "x ! 0 = True \<longrightarrow> x ! 1 = True \<longrightarrow> f_ot12 [M2 (if x ! 0 = False then (xb, (xb + (q - b)) mod q) else ((xb + (q - b)) mod q, xb)), C1 (x ! 1)] = return_spmf [U_ot12 (), P_ot12 (xb)]" for xb x
        by simp
      have **:"x ! 0 = True \<longrightarrow> x ! 1 = False \<longrightarrow> f_ot12 [M2 (if x ! 0 = False then (xb, (xb + (q - b)) mod q) else ((xb + (q - b)) mod q, xb)), C1 (x ! 1)] = return_spmf [U_ot12 (), P_ot12 ((xb + (q - b)) mod q)]" for xb x
        by simp
      have ***:"x ! 0 = False \<longrightarrow> x ! 1 = True \<longrightarrow> f_ot12 [M2 (if x ! 0 = False then (xb, (xb + (q - b)) mod q) else ((xb + (q - b)) mod q, xb)), C1 (x ! 1)] = return_spmf [U_ot12 (), P_ot12 ((xb + (q - b)) mod q)]" for xb x
        by simp
      have ****:"x ! 0 = False \<longrightarrow> x ! 1 = False \<longrightarrow> f_ot12 [M2 (if x ! 0 = False then (xb, (xb + (q - b)) mod q) else ((xb + (q - b)) mod q, xb)), C1 (x ! 1)] = return_spmf [U_ot12 (), P_ot12 (xb)]" for xb x
        by simp
      have "R_D_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd]; 
        let rd = output_ot_rev (nth outputs 1);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        using R_initial apply(auto simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+ (*takes a while*) 
           apply simp apply simp apply simp
        subgoal for x
          apply(cases "x ! 0"; cases "x ! 1")
          apply(simp add: *)
             apply (smt b_ge_d nth_Cons_0 nth_Cons_Suc)
          using ** apply simp apply simp
        apply(simp add: Let_def)
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+ 
          apply auto
          using f_MPC1_contr_b_lt_d b_ge_d by argo
        done
        also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        let rd = (rb + (q - b)) mod q;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(simp add: Let_def R_initial split del: if_split)
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
          apply auto
           apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
             apply(auto simp only: q_gt_0)
          using f_MPC1_contr_b_lt_d b_ge_d  by blast +
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+
              apply simp apply simp apply simp apply simp apply simp apply simp 
        subgoal for x 
          apply(cases x)
           apply(auto simp add: del: if_split)
          using f_MPC1_contr_b_lt_d b_ge_d by blast+
        done
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd'');
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf False;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(auto simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 Let_def)
        by (metis "44" False Nat.add_diff_assoc assms(2) mod_le_divisor q_gt_0) +
      ultimately have "R_D_bid [s, b, d] = return_pmf None"
        by(auto simp add: Let_def)
      moreover have "funct_bid [s, b, d] = return_pmf None"
        using False b_ge_d by(cases "s \<le> max b d"; auto)
      ultimately show ?thesis by auto
    qed
    next
    case False
    hence d_gt_b: "b < d" by simp
    then show ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      have "R_D_bid [s,b,d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs_ot12 1);
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rd);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        using R_initial 
        apply(simp add: Let_def R_initial split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        by auto
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto 
        using f_MPC1_contr_b_ge_d d_gt_b 
        by linarith +
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rb + rd') mod q; 
        let yb = (rb + (d + rd')) mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(auto simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 88 assms d_ge_s
         apply (auto simp add: d_ge_s) 
        using False apply blast 
        by (simp add: mod_add_right_eq)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rb + rd') mod q; 
        let yb = (rb + (fst (nth outputs 2) + rd')) mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(cases "s \<le> max b d")
         apply(auto simp add: Let_def)  
        using d_ge_s  
        using False apply blast 
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
          apply linarith  using d_ge_s  
        using False 
         apply blast using d_ge_s  
        using False 
        by linarith
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 2)) \<oplus> xd;
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let yd = (rb + rd') mod q; 
        let yb = (rb + (fst (nth outputs 2) + rd')) mod q;
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof- 
        have "(rb + (wb + rd')) mod q = ((rb + wb) + rd') mod q" for rd' rb wb by presburger
        thus ?thesis by(simp add: Let_def)
      qed
      ultimately show ?thesis 
        apply(auto simp add: S_D_bid_def Let_def)
        using False 
         by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?; simp add: Groups.add_ac(1)) +
    next
      case False
      with d_gt_b have s_gt: "s > b" "s > d" by auto
      have "R_D_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        outputs_ot12 \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs_ot12 1);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
        let rb' = output_ot_rev (nth outputs' 1);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        using R_initial
        apply(auto simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_ge_d d_gt_b 
        by auto
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        apply auto 
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
           apply (auto simp only: q_gt_0 set_spmf_sample_uniform) 
        using d_gt_b not_less by blast +
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC2 :: 'c \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xd) (P_ot12 rb);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12  \<leftarrow> S1_OT12_1 (M2 input1') (U_ot12 ());
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        view1_MPC2 :: 'd \<leftarrow> S1_MPC2 (D_mpc2 (xd,yd)) (nth outputs_mpc2 0);
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf False;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, (nth outputs_mpc2 0), wb, w)}"
        apply(auto simp only: Let_def) 
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 Let_def)
        using assms 
        by (simp add: "555" False)
      ultimately have "R_D_bid [s, b, d] = return_pmf None"
        by(auto simp add: Let_def)
      moreover have "funct_bid [s, b, d] = return_pmf None" 
        apply(cases "s \<le> max b d"; auto simp add: s_gt(1) s_gt(2) Let_def) 
        using False s_gt(1) by linarith
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma R1_final_output:
  assumes "xc < q" and "rd'< q"  and "b < q"
  shows "(((xc + (q - b)) mod q + rd') mod q + b) mod q = (xc + rd') mod q" 
proof(cases "b = 0")
  case True
  then show ?thesis 
    by (simp add: mod_add_left_eq)
next
  case False
  let ?y = "(((xc + (q - b)) mod q + rd') mod q + b)"
  have y_ge_0: "?y \<ge> 0" using assms by blast
  have "[?y = (xc + (q - b)) mod q + rd' + b] (mod q)" 
    using assms cong_def mod_add_left_eq by blast
  hence "[?y + q = xc + (q - b) + rd' + b] (mod q)"
    using assms
    by (simp add: cong_def mod_add_left_eq) 
  hence "[?y + q - (q - b) = xc + rd' + b] (mod q)"
  proof-
    have "?y + q - (q - b) > 0" 
      using y_ge_0 assms False by linarith
    thus ?thesis 
      by (smt Nat.add_diff_assoc add.assoc add.commute cong_def diff_le_self le_add_diff_inverse2 mod_add_left_eq mod_add_self2)
  qed
  hence "[?y + b = xc + rd' + b] (mod q)"
    using assms 
    by (metis Nat.add_diff_assoc diff_diff_cancel diff_le_self less_imp_le_nat)
  hence "[?y = xc + rd'] (mod q)" 
    using cong_add_rcancel_nat by blast
  thus ?thesis using cong_def by blast

qed

lemma 55:
  assumes "rd < q" and "d < q" and "rd'' < q"
  shows "(rd + (rd'' + (q - d)) mod q) mod q = ((rd + (q - d)) + rd'') mod q"
proof-
  let ?y = "(rd + (rd'' + (q - d)) mod q) mod q"
  have "[?y = rd + (rd'' + (q - d))] (mod q)" 
    using cong_def assms 
    by (simp add: mod_add_right_eq)
  hence "[?y = (rd + (q - d)) + rd''] (mod q)"
    using assms 
    by (metis add.commute add.left_commute)
  thus ?thesis using assms cong_def 
    by auto
qed

definition S_B_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> 'b \<times> bool \<times> nat \<times> 'f \<times> 'g \<times> nat \<times> bool \<times> nat) spmf"
  where "S_B_bid b W = do {
    let (wb,w) = W;
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
    rd' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
    let yd = ((rb + (q - wb)) + rd') mod q;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd', xd, yd)}"

sublocale bid_prot_B: semi_honest_det_security _ funct_bid valid_inputs_f_bid 1 R_B_bid S_B_bid .

lemma funct_bid_output_fst_b [simp]: 
  assumes "x \<in> set_spmf (return_spmf [(b, True), (b, True), (b, True)])"
  shows "fst (x ! (Suc 0)) = b" using assms by simp

lemma B_corrupt:
  assumes "s < q" "b < q" "d < q"
  shows "R_B_bid [s, b, d] = funct_bid [s, b, d] \<bind> (\<lambda> outputs. S_B_bid b (nth outputs 1))"
proof-
  have R_initial: "R_B_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rb');
    let yd = (rd + rd') mod q;   
    let yb = (rb + rb') mod q;
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"
    using assms 
    apply(auto simp add: split_def Let_def perfect_1_MPC1_unfold semi_honest_prob.ideal_view_def bind_map_spmf)
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
       apply(auto simp add:  OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 split del: if_split)
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
          apply (auto simp add: OT12_1_unfold OT12_correct_all Let_def) 
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
    using OT12_2_sec_all by auto 
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    hence R_bid_b_ge_d: "R_B_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
    let rd = (rb + (q - b)) mod q;
    rd' \<leftarrow> sample_uniform q;
    let rb' = rd';
    view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rb');
    let yd = (rd + rd') mod q;
    let yb = (rb + rb') mod q;
    outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"
      using R_initial
      apply(simp add: R_initial Let_def)
      by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      hence "R_B_bid [s, b, d] = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = (rd + rd') mod q;
        let yb = (rb + rd') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
       _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd', xd, yd)}"
        using R_bid_b_ge_d 
        by(cases "s \<le> max b d"; auto simp add: Let_def) 
      also have "... =  do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = ((rb + (q - (fst (nth outputs 1)))) mod q + rd') mod q;
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
         apply(cases "s \<le> b \<and> d \<le> b")
          apply(auto simp add: Let_def)
        using b_ge_d b_ge_s b_wins assms 
            apply (auto simp add: max.absorb1)
        apply(simp only: Let_def) 
        using funct_bid_output_fst_b  
          apply (metis Nat.diff_add_assoc less_or_eq_imp_le)
        by (metis Nat.add_diff_assoc funct_bid_output_fst_b le_simps(1))
      also have "... =  do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = ((rb + (q - (fst (nth outputs 1)))) mod q + rd') mod q;
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using assms  
        by(auto simp add: Let_def  MPC2_correct_unfold)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = ((rb + (q - (fst (nth outputs 1)))) + rd') mod q;
        let yb = (rb + rd'') mod q;
        _ :: unit \<leftarrow> assert_spmf True;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
        by (smt "44"  mod_add_left_eq assms(2) b_ge_d b_ge_s funct_bid_output_fst_b lessThan_iff max.orderE not_le q_gt_0 set_spmf_sample_uniform)
      ultimately show ?thesis  
        by(auto simp add: S_B_bid_def Let_def) 
    next
      case False 
      hence "R_B_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = (rd + rd') mod q;
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using  R_bid_b_ge_d apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
        apply(auto simp add: Let_def q_gt_0  R_bid_b_ge_d MPC2_correct_unfold) 
           apply (metis (no_types, lifting) "44" Nat.add_diff_assoc assms(2) mod_le_divisor q_gt_0)
        using assms "44" MPC2_correct_unfold f_MPC2.simps mod_less_divisor q_gt_0 valid_inputs_mpc2.simps b_ge_d by presburger +
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd');
        let yd = (rd + rd') mod q;
        let yb = (rb + rd'') mod q;
        _ :: unit \<leftarrow> assert_spmf False;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 Let_def) 
        by (metis "44" False Nat.diff_add_assoc assms(2) mod_le_divisor q_gt_0)
      ultimately have "R_B_bid [s, b, d] = return_pmf None"
        by(auto simp add: Let_def)
      moreover have "funct_bid [s, b, d] = return_pmf None" 
        using False b_ge_d by(cases "s \<le> max b d"; auto)
      ultimately show ?thesis by simp
    qed
  next
    case False
    hence d_gt_b: "b < d" by simp
    hence max_eq_d: "max b d = d" by simp
    then show ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      hence "R_B_bid [s, b, d] = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs 1);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using R_initial
        apply(auto simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
         apply auto using f_MPC1_contr_b_ge_d d_gt_b apply linarith using f_MPC1_contr_b_ge_d d_gt_b apply linarith
        by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs 1);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;  
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp add: Let_def)
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
          apply(auto simp add: q_gt_0 "11" assms)
        using "1" assms(3) apply simp
        by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs 1);
        rd'' \<leftarrow> map_spmf (\<lambda> rd'. (d + rd') mod q) (sample_uniform q);
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(simp add: bind_map_spmf o_def Let_def)
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
        let rd = output_ot_rev (nth outputs 1);
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(simp add: samp_uni_plus_one_time_pad)    
      also have "... = do {
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        let rd = rb;
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto
        using f_MPC1_contr_b_ge_d d_gt_b by presburger +
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
        let xb = (nth outputs_mpc1 0);
        let xd = (nth outputs_mpc1 1);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = ((rb + (q - (fst (nth outputs 1))) + rd'')) mod q;   
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def)
        apply(cases "s \<le> max b d") apply auto 
        using False apply blast 
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
           apply (smt add.assoc add.commute max.commute max_def mod_add_right_eq)
          apply (simp add: Groups.add_ac(2) Groups.add_ac(3) mod_add_right_eq)
        using False apply blast 
        by (simp add: d_ge_s max_def)
      also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = ((rb + (q - (fst (nth outputs 1))) + rd'')) mod q;  
        let yb = (rb + rd'') mod q;
        outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(cases "\<not> s \<le> max b d")
        apply(auto simp add: Let_def)
        using False apply linarith         
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 max_eq_d) using d_gt_b assms apply(simp add: MPC2_correct_unfold) 
        by (metis (no_types, lifting) "44" Nat.add_diff_assoc assms(3) mod_add_left_eq mod_le_divisor q_gt_0)
     also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = ((rb + (q - (fst (nth outputs 1))) + rd'')) mod q;  
        let yb = (rb + rd'') mod q;
        outputs_mpc2 :: bool list \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
        _ :: unit \<leftarrow> assert_spmf True; 
         return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
       apply(auto simp add: Let_def )
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
         apply(auto simp add: q_gt_0)
       by (metis (no_types, lifting) "44" Nat.add_diff_assoc assms(3) max_eq_d mod_add_left_eq mod_le_divisor q_gt_0)
     also have "... = do {
        outputs \<leftarrow> funct_bid [s, b, d];
        xd \<leftarrow> coin_spmf;
        let xb = (snd (nth outputs 1)) \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
        rd'' \<leftarrow> sample_uniform q;
        view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = ((rb + (q - (fst (nth outputs 1))) + rd'')) mod q;  
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
       by(simp add: bind_spmf_const q_gt_0 Let_def)
      ultimately show ?thesis  
        by(simp add: S_B_bid_def Let_def)
    next
      case False
      have "R_B_bid [s, b, d] = do {
       outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
       let xb = (nth outputs_mpc1 0);
       let xd = (nth outputs_mpc1 1);
       view_MPC1 \<leftarrow> S1_MPC1 b xb;
       rb \<leftarrow> sample_uniform q;
       let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
       view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
       outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
       let rd = output_ot_rev (nth outputs 1);
       rd' \<leftarrow> sample_uniform q;
       let rd'' = (d + rd') mod q;
       view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
       let yd = (rd + rd') mod q;   
       let yb = (rb + rd'') mod q;
       outputs_mpc2 \<leftarrow> protocol_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
       _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
       return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using R_initial
        apply(auto simp add: Let_def)
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_ge_d d_gt_b 
         apply linarith 
        by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+  
      also have "... = do {
       outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
       let xb = (nth outputs_mpc1 0);
       let xd = (nth outputs_mpc1 1);
       view_MPC1 \<leftarrow> S1_MPC1 b xb;
       rb \<leftarrow> sample_uniform q;
       let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
       view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
       outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
       let rd = output_ot_rev (nth outputs 1);
       rd' \<leftarrow> sample_uniform q;
       let rd'' = (d + rd') mod q;
       view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
       let yd = (rd + rd') mod q;   
       let yb = (rb + rd'') mod q;
       outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
       _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
       return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using assms
        by(auto simp add: Let_def MPC2_correct_unfold)
      also have "... = do {
       outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
       let xb = (nth outputs_mpc1 0);
       let xd = (nth outputs_mpc1 1);
       view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
       view1_OT12 :: 'f \<leftarrow> S1_OT12_1 (M2 input1) (U_ot12 ());
       outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
       let rd = output_ot_rev (nth outputs 1);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
       view2_OT12 :: 'g \<leftarrow> S2_OT12_1 (C1 xb) (P_ot12 rd'');
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
       _ :: unit \<leftarrow> assert_spmf False;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp only: Let_def split_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+
               apply(auto simp add: q_gt_0 Let_def split del: if_split) 
        apply(cases "d \<le> b") apply auto 
        using d_gt_b not_less apply blast
        subgoal for xa xb xc xd xe xf xg
          apply(cases xg) apply auto
          by (simp add: "555" False assms(3))+
        done
      also have "... = return_pmf None"
        by(auto simp add: Let_def) 
      ultimately have "R_B_bid [s, b, d] = return_pmf None"
        by simp
      moreover have "funct_bid [s, b, d] = return_pmf None"
        using False d_gt_b by(cases "s \<le> max b d"; auto)
      ultimately show ?thesis by simp
    qed
  qed
qed


lemma rd'_rewrite:
  assumes "yd = (rd + rd') mod q" and "rd < q" and "rd' < q"
  shows "(yd + q - rd) mod q = rd'"
proof-
  have *: "[yd + q = rd + rd'] (mod q)" 
    using assms cong_def by force
  hence "[yd + q - rd = rd'] (mod q)"
  proof-
    have "yd + q - rd > 0" 
      using assms by auto
    thus ?thesis 
      using * cong_add_lcancel_nat nat_diff_split
      by (metis add_diff_inverse_nat rel_simps(70))
  qed
  thus ?thesis using assms cong_def 
    by (simp add: \<open>\<And>c b a. [b = c] (mod a) = (b mod a = c mod a)\<close>)
qed

lemma rd'_rewrite':
  assumes "yd = (rd + rd') mod q" and "rd < q" and "rd' < q"
  shows "(rd', (d + rd') mod q) = ((yd + q - rd) mod q, (d + (yd + q - rd) mod q) mod q)"
  using assms rd'_rewrite by simp

lemma rb_rewrite:
  assumes "rd = (rb + (q - b)) mod q" and "rb < q" and "b < q"
  shows "(rd + b) mod q = rb"
proof(cases "b = 0")
  case True
  then show ?thesis using assms by simp
next
  case False
  hence b_gt_0: "b > 0" by simp
  have "[rd + q = rb + (q - b)] (mod q)" 
    using assms cong_def by force
  hence "[rd + q - (q - b) = rb] (mod q)"
  proof-
    have "rd + q - (q - b) > 0" 
      using assms b_gt_0 by linarith
    thus ?thesis 
      by (metis \<open>[rd + q = rb + (q - b)] (mod q)\<close> add.commute add_diff_inverse_nat cong_add_lcancel_nat less_numeral_extra(3) nat_diff_split)
  qed
  hence "[rd + b = rb] (mod q)" 
    using assms(3) by auto
  thus ?thesis using assms cong_def 
    by (metis mod_if)
qed

lemma rb_rewrite':
  assumes "rd = (rb + (q - b)) mod q" and "rb < q" and "b < q"
  shows "(rb, rd) = ((rd + b) mod q, rd)" 
  using assms rb_rewrite by auto

lemma in1_rewrite:
  assumes "in1' = (yd + (q - rd)) mod q" and "yd < q" and "rd < q"
  shows "(in1' + rd) mod q = yd"
proof(cases "rd = 0")
  case True
  then show ?thesis using assms by simp
next
  case False 
  have *: "[in1' + q = yd + (q - rd)] (mod q)"
    using assms cong_def by force
  hence "[in1' + q - (q - rd) = yd] (mod q)"
  proof-
    have "in1' + q - (q - rd) > 0"
      using False assms by auto
    thus ?thesis 
      by (metis * add_diff_inverse_nat cong_add_lcancel_nat linordered_field_class.sign_simps(2) nat_diff_split rel_simps(70))
  qed
  hence "[in1' + rd = yd] (mod q)"
    by (simp add: assms(3) le_simps(1))
  thus ?thesis  
    by (metis cong_def assms(2) mod_if)
qed

lemma in1_rewrite':
  assumes "in1' = (yd + (q - rd)) mod q" and "yd < q" and "rd < q"
  shows "((yd + (q - rd)) mod q + rd) mod q = yd"
  using in1_rewrite assms by simp

lemma in2_rewrite:
  assumes "in2' = (d + ((in1' + rd) mod q + q - rd) mod q) mod q"
    and "d < q" and "rd < q" and "in1' < q" 
  shows "(in2' + (q - d)) mod q = in1'"
proof(cases "d = 0")
  case True
  then show ?thesis 
    by (metis add.commute diff_zero rd'_rewrite assms)
next
  case False  
  have "[in2' = (d + ((in1' + rd) mod q + q - rd) mod q)] (mod q)"
    using assms cong_def by simp
  hence "[in2' = d + ((in1' + rd) mod q + q - rd)] (mod q)"
    by (simp add: cong_def mod_add_right_eq)
  hence "[in2' = d + in1'] (mod q)"
    by (smt ab_semigroup_add_class.add_ac(1) add.commute add_diff_cancel_right' assms(1) assms(3) assms(4) cong_def mod_add_self2 mod_mod_trivial rd'_rewrite)
  hence "[in2' + q = d + in1'] (mod q)"
    using assms 
    by (simp add: cong_def)
  hence "[in2' + q - d = in1'] (mod q)"
  proof-
    have "in2' + q - d > 0" using False assms by simp
    thus ?thesis 
      by (metis (mono_tags, lifting) \<open>[in2' = d + in1'] (mod q)\<close> assms(1) assms(2) assms(4) cong_def mod_mod_trivial rd'_rewrite)
  qed
  thus ?thesis 
    by (metis assms(2) assms(4) cong_def Nat.add_diff_assoc less_or_eq_imp_le mod_if)
qed

lemma in2_rewrite':
  assumes "in2' = (d + ((in1' + rd) mod q + q - rd) mod q) mod q"
    and "d < q" and "rd < q" and "in1' < q" 
  shows "((d + ((in1' + rd) mod q + q - rd) mod q) mod q + (q - d)) mod q = in1'"
  using in2_rewrite assms by blast

lemma correct1:
  assumes "x < q" and "xa < q" 
    and "d < q"
  shows "((x + (d + xa) mod q) mod q + q - (x + xa) mod q) mod q = d"
proof-
  have "[(x + (d + xa) mod q) mod q + q - (x + xa) mod q = (x + (d + xa) mod q) + q - (x + xa) mod q] (mod q)"
    using cong_def assms 
    by (smt Nat.add_diff_assoc gr_implies_not_zero le_simps(1) mod_add_left_eq nat_neq_iff unique_euclidean_semiring_numeral_class.pos_mod_bound)
  hence "[(x + (d + xa) mod q) mod q + q - (x + xa) mod q = (x + (d + xa)) + q - (x + xa) mod q] (mod q)"
    using cong_def assms 
    by (smt Nat.add_diff_assoc gr_implies_not_zero le_simps(1) mod_add_left_eq mod_add_right_eq nat_neq_iff unique_euclidean_semiring_numeral_class.pos_mod_bound)
  hence "[(x + (d + xa) mod q) mod q + q - (x + xa) mod q = (x + (d + xa)) + q - (x + xa)] (mod q)"
  proof- 
    have "(x + (d + xa)) + q - (x + xa) > 0" 
      using assms q_gt_0 by linarith
    thus ?thesis    using cong_def assms  
      by (smt Nat.add_diff_assoc add_gr_0 cong_diff_nat le_simps(1) less_imp_add_positive mod_add_right_eq mod_add_self2 mod_mod_trivial unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_diff)
  qed
  hence "[(x + (d + xa) mod q) mod q + q - (x + xa) mod q = d] (mod q)"
    by (simp add: cong_def)
  thus ?thesis using cong_def assms 
    by (simp add: \<open>\<And>c b a. [b = c] (mod a) = (b mod a = c mod a)\<close>)
qed

term "set_spmf (f_MPC1 [b, d])"

lemma 1 [simp]:
  assumes "Max {b,d} < q" and "b \<ge> d"
    and "[x,y] \<in> set_spmf (f_MPC1 [b, d])" shows "x = (\<not> y)"
  using assms by(auto)

lemma 2 [simp]:
  assumes "Max {b,d} < q" and "\<not> b \<ge> d"
    and "[x,y] \<in> set_spmf (f_MPC1 [b, d])" shows "\<not> (x = (\<not> y))"
  using assms by(auto)

lemma correctness_reserve_not_met:
  assumes "Max {b,d} < q"
    and "Max {b,d} < s"
    and "s < q"
  shows "protocol_bid [s, b, d] = funct_bid [s, b, d]"
proof-
  have [simp]: "b < q" "d < q" using assms by auto
  have "protocol_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);    
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf ([out, out, out])}"
    apply(auto simp only: protocol_bid.simps Let_def)
   apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using MPC1_correct apply simp
    using OT12_correct_all apply simp 
    using OT12_correct_all apply simp
    using  MPC2_correct[unfolded mpc2.correctness_def] assms
    by fastforce 
  also have "...  = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);   
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    _ :: unit \<leftarrow> assert_spmf False;
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf ([out, out, out])}"
    apply(auto simp only: Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    subgoal for xa xb xc xd xe
      apply(cases xe; cases "d \<le> b")
      apply(auto simp add: q_gt_0) 
      apply (metis "44" assms(2) Max.singleton Max_insert Nat.add_diff_assoc \<open>b < q\<close> assms(2) finite.intros(1) finite_insert linorder_not_le max.orderE mod_le_divisor q_gt_0)
      using "555" assms(2) apply simp
      apply (metis "44" Max.singleton Max_insert Nat.add_diff_assoc \<open>b < q\<close> assms(2) finite.intros(1) finite_insert linorder_not_le max.orderE mod_le_divisor q_gt_0)
      using "555" assms(2) by simp
    done
     also have "... = funct_bid [s, b, d]" 
       apply(auto simp add:  Let_def; cases "s \<le> max b d") 
       using assms by auto
  ultimately show ?thesis by argo
qed

lemma correctness_reserve_met:
  assumes "Max {b,d} < q"
    and "Max {b,d} \<ge> s"
    and "s < q"
  shows "protocol_bid [s, b, d] = funct_bid [s, b, d]"
proof-
  have prot_init: "protocol_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    outputs_mpc2 \<leftarrow> f_MPC2 [D_mpc2 (xd,yd), S_mpc2 (s,xb,yb)];
    _ :: unit \<leftarrow> assert_spmf (nth outputs_mpc2 0);
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf ([out, out, out])}"
    apply(auto simp only: protocol_bid.simps Let_def)
   apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using MPC1_correct apply simp
    using OT12_correct_all apply simp 
    using OT12_correct_all apply simp
    using  MPC2_correct[unfolded mpc2.correctness_def] assms
    by fastforce 
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    have "protocol_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf ([out, out, out])}"
      using prot_init
      apply(auto simp add: Let_def)
       apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      subgoal for x xa xb xc xd
        apply(cases x)
         apply auto 
        by (metis (no_types, lifting) "44" Max.singleton Max_insert assms(1) assms(2) finite.intros(1) finite_insert lessThan_iff max.orderE q_gt_0 set_spmf_sample_uniform)+
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      by (metis b_ge_d)
    also have "... = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    let out = ((yb + (q - yd)) mod q, True);
    return_spmf ([out, out, out])}"
      apply(simp add: Let_def split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      using b_ge_d assms f_MPC1_contr_b_lt_d correct2 q_gt_0 
      by blast
    also have "... = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    let out = (b, True);
    return_spmf ([out, out, out])}"
      apply(simp add: Let_def split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      subgoal for x xa xb xc xd
        apply(cases x)
         apply auto 
      using b_ge_d f_MPC1_contr_b_lt_d 
        by (metis "44" Max.singleton Max_insert b_ge_d assms(1) finite.intros(1) finite_insert lessThan_iff max.orderE q_gt_0 set_spmf_sample_uniform)+
      done
    also have "... = do {
    let out = (b, True);
    return_spmf ([out, out, out])}"
    proof-
      have "f_ot12 [M2 (if y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb)), C1 y] = return_spmf [U_ot12 (), P_ot12 ((rb + (q - b)) mod q)]" for y rb
        by simp
      moreover have "f_ot12 [M2 (if \<not> y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb)), C1 y] = return_spmf [U_ot12 (), P_ot12 rb]" for y rb
        by simp
      moreover have "f_ot12 [M2 (if y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), C1 (\<not> y)] = return_spmf [U_ot12 (), P_ot12 ((d + rd') mod q)]" for y rd'
        by simp
      moreover have "f_ot12 [M2 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), C1 (\<not> y)] = return_spmf [U_ot12 (), P_ot12 rd']" for y rd'
        by simp
      ultimately show ?thesis 
      apply(auto simp add: bind_spmf_const Let_def q_gt_0)
        using b_ge_d by linarith
    qed
    ultimately have "protocol_bid [s,b,d] = do {   
    let out = (b, True);
    return_spmf ([out, out, out])}"
      by argo
    moreover have "funct_bid [s,b,d] = do {   
    let out = (b, True);
    return_spmf ([out, out, out])}"
      using assms b_ge_d  
      by (auto simp add: max.absorb1)
    ultimately show ?thesis by argo
  next
    case False
    have "protocol_bid [s, b, d] = do {
    outputs_mpc1 \<leftarrow> f_MPC1 [b, d];
    let xb = (nth outputs_mpc1 0);
    let xd = (nth outputs_mpc1 1);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    outputs \<leftarrow> f_ot12 [M2 input1, C1 xd];
    let rd = output_ot_rev (nth outputs 1);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    outputs' \<leftarrow> f_ot12 [M2 input1', C1 xb]; 
    let rb' = output_ot_rev (nth outputs' 1);
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    let out = (d, False);
    return_spmf ([out, out, out])}"
      using prot_init
      apply(auto simp add: Let_def)
       apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(simp add: f_ot12_if_unfold) 
      using False apply linarith
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(simp add: f_ot12_if_unfold_neg) 
      using False 
      by (metis (no_types, lifting) "555" Max.singleton Max_insert Nat.add_diff_assoc assms(1) assms(2) empty_not_insert finite.intros(1) finite_insert lessThan_iff max.commute max_def mod_le_divisor q_gt_0 set_spmf_sample_uniform) 
    also have "... = do {
    let out = (d, False);
    return_spmf ([out, out, out])}" 
    proof-
      have "f_ot12 [M2 (if y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb)), C1 y] = return_spmf [U_ot12 (), P_ot12 ((rb + (q - b)) mod q)]" for y rb
        by simp
      moreover have "f_ot12 [M2 (if \<not> y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb)), C1 y] = return_spmf [U_ot12 (), P_ot12 rb]" for y rb
        by simp
      moreover have "f_ot12 [M2 (if y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), C1 (\<not> y)] = return_spmf [U_ot12 (), P_ot12 ((d + rd') mod q)]" for y rd'
        by simp
      moreover have "f_ot12 [M2 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), C1 (\<not> y)] = return_spmf [U_ot12 (), P_ot12 rd']" for y rd'
        by simp
      ultimately show ?thesis 
      apply(auto simp add: bind_spmf_const Let_def q_gt_0)
        using False 
        by(auto simp add: bind_spmf_const f_ot12_if_unfold_neg q_gt_0)
    qed
    ultimately have "protocol_bid [s,b,d] = do {
    let out = (d, False);
    return_spmf ([out, out, out])}" 
      by argo
    moreover have "funct_bid [s,b,d] = do {   
    let out = (d, False);
    return_spmf ([out, out, out])}"
      using assms False 
      by (auto simp add: max.absorb1 Let_def)
    ultimately show ?thesis 
      using False assms by argo
  qed
qed

theorem correctness:
  shows "bid_prot_correct.correctness [s, b, d]" 
  unfolding bid_prot_correct.correctness_def 
  apply(cases "Max {b,d} < s") 
  using correctness_reserve_not_met valid_inputs_f_bid.simps 
   apply (metis (no_types, hide_lams) basic_trans_rules(19))
  using correctness_reserve_met valid_inputs_f_bid.simps  
  by (metis Max.singleton Max_insert finite.intros(1) finite_insert max_less_iff_conj not_le_imp_less)

theorem perfect_security_B:
  shows "bid_prot_B.perfect_security [s,b,d]"
  using B_corrupt  unfolding bid_prot_B.perfect_security_def 
  by(auto simp add: split_def)

theorem perfect_security_S:
  shows "bid_prot_S.perfect_security [s,b,d]"
  using S_corrupt unfolding bid_prot_S.perfect_security_def
  by(auto simp add: split_def)

theorem perfect_security_D:
  shows "bid_prot_D.perfect_security [s,b,d]"
proof-
  have "[s, b, d] ! 2 = d" by simp
  thus ?thesis
    using D_corrupt valid_inputs_f_bid.simps unfolding bid_prot_D.perfect_security_def   
    by presburger
qed

end 

end 