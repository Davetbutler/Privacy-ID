theory Bidding_Prot imports
  CryptHOL.CryptHOL
  OT_Functionalities
  "HOL-Number_Theory.Cong"
  Semi_Honest
  Uniform_Sampling
begin
  (*could  introduce predicates like valid input s < q, b < q, d < q and reserve_met s b d = (b >= s \/ d >= s)*)
sledgehammer_params[timeout = 1000]

locale bidding_prot_base =
  fixes q :: nat
  assumes q_gt_0: "q > 0"
begin

definition valid_inputs_ot12 :: "((nat \<times> nat) \<times> bool) \<Rightarrow> bool"
  where "valid_inputs_ot12 inputs  = (fst (fst inputs) < q \<and> (snd (fst inputs)) < q)"

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

definition funct_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> bool) spmf"
  where "funct_bid inputs = do {
        let (s, b, d) = inputs;
        _ :: unit \<leftarrow> assert_spmf (if (Max {b,d} < s) then False else True);
        let out = (Max {b,d}, (if (Max {b,d} \<le> b) then True else False));
        return_spmf (out)}"

definition valid_inputs_f_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> bool"
  where "valid_inputs_f_bid inputs \<equiv> (fst inputs < q \<and> fst (snd inputs) < q \<and> snd (snd inputs) < q)"

lemma 
  assumes "valid_inputs_f_bid (s,b,d)" 
  shows "s < q" "b < q" "d < q"
  using assms
  by(auto simp add: valid_inputs_f_bid_def)

lemma b_wins:
  assumes b_ge_d: "b \<ge> d"
    and b_ge_s: "b \<ge> s"
    and asm: "(wb, w) \<in> set_spmf (funct_bid (s, b, d))"
  shows "wb = b"
  using assms by(auto simp add: funct_bid_def Let_def)

lemma d_wins:
  assumes b_ge_d: "d > b"
    and b_ge_s: "d \<ge> s"
    and asm: "(wb,w) \<in> set_spmf (funct_bid (s, b, d))"
  shows "wb = d"
  using assms by(auto simp add: funct_bid_def Let_def)

definition funct_MPC1_ideal :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (bool \<times> bool) spmf"
  where "funct_MPC1_ideal s W = do {
    let (wb, w) = W;
    a \<leftarrow> coin_spmf;
    return_spmf (w \<oplus> a, a)}"

definition f_MPC1  :: "(nat \<times> nat) \<Rightarrow> (bool \<times> bool) spmf"
  where "f_MPC1 inputs = do {
    let (b,d) = inputs;
    a \<leftarrow> coin_spmf;
    let xb = (if b \<ge> d then True else False);
    return_spmf (xb \<oplus> a,a)}"

definition valid_inputs_mpc1 :: "(nat \<times> nat) \<Rightarrow> bool"
  where "valid_inputs_mpc1 inputs \<equiv> (fst inputs < q \<and> snd inputs < q)"

lemma f_MPC1_contr_b_lt_d:
  assumes "(True, True) \<in> set_spmf (f_MPC1 (b, d)) \<or> (False, False) \<in> set_spmf (f_MPC1 (b, d))"
  shows "\<not> b \<ge> d"
  using assms by(auto simp add: f_MPC1_def)

lemma f_MPC1_contr_b_ge_d:
  assumes "(False, True) \<in> set_spmf (f_MPC1 (b, d)) \<or> (True, False) \<in> set_spmf (f_MPC1 (b, d))"
  shows "\<not> b < d"
  using assms by(auto simp add: f_MPC1_def)

lemma b_ge_d_f_MPC1_out:
  assumes "b \<ge> d"
  shows "(False, True) \<in> set_spmf (f_MPC1 (b, d)) \<or> (True, False) \<in> set_spmf (f_MPC1 (b, d))"
  using assms  by(auto simp add: f_MPC1_def)

lemma b_lt_d_f_MPC1_out:
  assumes "d > b"
  shows "(False, False) \<in> set_spmf (f_MPC1 (b, d)) \<or> (True, True) \<in> set_spmf (f_MPC1 (b, d))"
  using assms  by(auto simp add: f_MPC1_def)

lemma b_lt_d_f_MPC1:
  assumes "b < d" 
    and "(xb ,xd) \<in> set_spmf (f_MPC1 (b, d))"
  shows "xb \<oplus> xd = False"
  using assms unfolding f_MPC1_def by(simp add: Let_def)

definition f_MPC2 :: "((bool \<times> nat) \<times> (nat \<times> bool \<times> nat)) \<Rightarrow> (bool \<times> bool) spmf"
  where "f_MPC2 inputs = do {
    let out = (if (((snd (snd (snd inputs))) + (q - (snd (fst inputs)))) mod q \<ge> (fst (snd inputs))) then True else False);
    return_spmf (out, out)}"

lemma "f_MPC2 ((xd,yd), (s,xb,yb)) = do {
    let out = (if ((yb + (q - yd)) mod q \<ge> s) then True else False);
    return_spmf (out, out)}"
  by(simp add: f_MPC2_def split_def)


definition valid_inputs_mpc2 :: "((bool \<times> nat) \<times> (nat \<times> bool \<times> nat)) \<Rightarrow> bool"
  where "valid_inputs_mpc2 inputs = ((snd (fst inputs)) < q \<and> (snd (snd (snd inputs))) < q \<and> fst (snd inputs) < q)"

definition extract_fst_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat"
  where "extract_fst_bid inputs = fst inputs"

definition extract_snd_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat"
  where "extract_snd_bid inputs = fst (snd inputs)"

definition extract_thrd_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> nat"
  where  "extract_thrd_bid inputs = snd (snd inputs)"

end 

locale bidding_prot = bidding_prot_base 
  +  mpc1_1: semi_honest_prob f_MPC1 protocol_MPC1 mpc1_view_1 S1_MPC1 valid_inputs_mpc1 fst fst
  +  mpc1_2: semi_honest_prob f_MPC1 protocol_MPC1 mpc1_view_2 S2_MPC1 valid_inputs_mpc1 snd snd
  + mpc2: semi_honest_det_correctness f_MPC2 protocol_MPC2 valid_inputs_mpc2
  + mpc2_1: semi_honest_det_security f_MPC2 R1_MPC2 S1_MPC2 valid_inputs_mpc2 fst fst 
  + mpc2_2: semi_honest_det_security f_MPC2 R2_MPC2 S2_MPC2 valid_inputs_mpc2 snd snd 
  + ot12: semi_honest_det_correctness f_ot12 protocol_OT12 valid_inputs_ot12
  + ot12_1: semi_honest_det_security f_ot12 R1_OT12_1 S1_OT12_1 valid_inputs_ot12 fst fst 
  + ot12_2: semi_honest_det_security f_ot12 R2_OT12_1 S2_OT12_1 valid_inputs_ot12 snd snd 
  for  "protocol_MPC1" 
    and "mpc1_view_1" :: "nat \<times> nat \<Rightarrow> 'view_MPC1 spmf" 
    and "S1_MPC1" 
    and "mpc1_view_2" :: "nat \<times> nat \<Rightarrow> 'view_MPC2 spmf" 
    and "S2_MPC1" "protocol_MPC2" 
    and "R1_MPC2" :: "(bool \<times> nat) \<times> nat \<times> bool \<times> nat \<Rightarrow> 'view_MPC2_1 spmf"
    and S1_MPC2  
    and "R2_MPC2" :: "(bool \<times> nat) \<times> nat \<times> bool \<times> nat \<Rightarrow> 'view_MPC2_2 spmf"
    and S2_MPC2 protocol_OT12
    and "R1_OT12_1" :: "(nat \<times> nat) \<times> bool \<Rightarrow> 'view1_OT_1 spmf"
    and  R2_OT12_1 :: "(nat \<times> nat) \<times> bool \<Rightarrow> 'view2_OT_1 spmf" 
    and S1_OT12_1 S2_OT12_1  
    +  assumes MPC1_correct: "protocol_MPC1 (b, d) = f_MPC1 (b, d)"
    and MPC2_correct: "mpc2.correctness ((xd,yd), (s,xb,yb))"
    and OT12_correct: "ot12.correctness (M, \<sigma>)"
    and MPC1_1: "mpc1_1.perfect_security (m1, m2)"
    and MPC1_2: "mpc1_2.perfect_security (m1, m2)"
    and OT12_sec_P1: "ot12_1.perfect_security (M, \<sigma>)"
    and OT12_sec_P2: "ot12_2.perfect_security (M, \<sigma>)"
    and MPC2_sec_P1: "mpc2_1.perfect_security ((xd,yd), (s,xb,yb))"
    and MPC2_sec_P2: "mpc2_2.perfect_security ((xd,yd), (s,xb,yb))"
begin
 

lemma MPC2_correct_unfold: "\<forall> xd yd s xb yb. valid_inputs_mpc2 ((xd,yd), (s,xb,yb)) \<longrightarrow> protocol_MPC2 ((xd,yd), (s,xb,yb)) = f_MPC2 ((xd,yd), (s,xb,yb))"
  using MPC2_correct[unfolded mpc2.correctness_def] by simp

lemma OT12_1_1: 
  assumes "valid_inputs_ot12 ((m0,m1), \<sigma>)" 
  shows "R1_OT12_1 ((m0,m1), \<sigma>) = f_ot12 ((m0,m1), \<sigma>) \<bind> (\<lambda> (out1, out2). S1_OT12_1 (m0,m1) out1)"
  using OT12_sec_P1[unfolded ot12_1.perfect_security_def] assms by(auto simp add: split_def)

lemma OT12_2_1: 
  assumes "valid_inputs_ot12 ((m0,m1), \<sigma>)" 
  shows "R2_OT12_1 ((m0,m1), \<sigma>) = f_ot12 ((m0,m1), \<sigma>) \<bind> (\<lambda> (out1, out2). S2_OT12_1 \<sigma> out2)"
  using OT12_sec_P2[unfolded ot12_2.perfect_security_def] assms by(auto simp add: split_def)

lemma MPC2_1: 
  assumes "valid_inputs_mpc2 ((xd,yd), (s,xb,yb))"
  shows "R1_MPC2 ((xd,yd), (s,xb,yb)) = f_MPC2 ((xd,yd), (s,xb,yb)) \<bind> (\<lambda> (out1, out2). S1_MPC2 (xd,yd) out1)"
  using MPC2_sec_P1[unfolded mpc2_1.perfect_security_def] assms by(auto simp: Let_def split_def)

lemma MPC2_2:
  assumes "valid_inputs_mpc2 ((xd,yd), (s,xb,yb))"
  shows "R2_MPC2 ((xd,yd), (s,xb,yb)) = f_MPC2 ((xd,yd), (s,xb,yb)) \<bind> (\<lambda> (out1, out2). S2_MPC2 (s,xb,yb) out2)"
  using MPC2_sec_P2[unfolded mpc2_2.perfect_security_def] assms by(auto simp: Let_def split_def)

lemma OT12_2_sec_all : 
  assumes "valid_inputs_ot12 ((m0,m1), \<sigma>)" 
  shows "R2_OT12_1 ((m0,m1), \<sigma>) = f_ot12 ((m0,m1), \<sigma>) \<bind> (\<lambda> (out1, out2). S2_OT12_1 \<sigma> out2)"
  using OT12_2_1 assms by auto

lemma perfect_1_MPC1_unfold:
  assumes "valid_inputs_mpc1 (b,d)"
  shows "mpc1_1.real_view (b, d) = mpc1_1.ideal_view (b, d)"
  using MPC1_1[unfolded mpc1_1.perfect_security_def] assms by simp

lemma perfect_2_MPC1_unfold:
  assumes "valid_inputs_mpc1 (b,d)"
  shows "mpc1_2.real_view (b, d)  = mpc1_2.ideal_view (b, d)"
  using MPC1_2[unfolded mpc1_2.perfect_security_def] assms by simp

(*lemma perfect_1_MPC1_unfold':
  shows "f_MPC1 (m1, m2) \<bind> (\<lambda> (out1, out2). map_spmf (\<lambda> view. (view, (out1, out2))) (S1_MPC1 m1 out1)) =
        do {
          outputs :: (bool \<times> bool) \<leftarrow> protocol_MPC1 (m1, m2);
          view :: 'h \<leftarrow> R1_MPC1 (m1, m2);
          return_spmf (view, outputs)}"
  using MPC1_1[unfolded sim_non_det_def.perfect_sec_P1_def sim_non_det_def.Ideal1_def sim_non_det_def.Real1_def] 
  by simp*)

lemma OT12_correct_all: "\<forall> m0 m1 \<sigma>. valid_inputs_ot12 ((m0,m1), \<sigma>) \<longrightarrow> protocol_OT12 ((m0,m1), \<sigma>) = f_ot12 ((m0,m1), \<sigma>)" 
  by(auto simp add: OT12_correct[unfolded ot12.correctness_def])

(*lemma OT12_correct_all_if: "f_ot12 ((if \<not> ba then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), \<sigma>) = 
            protocol_OT12 ((if \<not> ba then ((d + rd') mod q, rd') else (rd', (d + rd') mod q)), \<sigma>)"
  using OT12_correct_all by simp*)

(*lemma lossless_protocol_OT12: "lossless_spmf (protocol_OT12 ((m0,m1), \<sigma>))"
  for m0 m1 \<sigma>
  using OT12_correct_all by auto*)

lemma OT12_1_unfold: 
  assumes "valid_inputs_ot12 ((m0, m1), \<sigma>)"
  shows "R1_OT12_1 ((m0,m1), \<sigma>) = S1_OT12_1 (m0,m1) ()" 
  using OT12_1_1 assms by(auto simp add: split_def f_ot12_def)

definition protocol_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> bool) spmf"
  where "protocol_bid inputs = do {
    let (s, b, d) = inputs;
    (xb :: bool,xd :: bool) \<leftarrow> protocol_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> protocol_OT12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> protocol_OT12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out1;
    let out = ((yb + (q - yd)) mod q, (xb \<oplus> xd));
    return_spmf (out)}"

definition R_S_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> bool \<times> nat \<times> 'view_MPC2_2 \<times> bool \<times> nat) spmf"
  where "R_S_bid inputs = do {
    let (s, b, d) = inputs;
    (xb :: bool,xd :: bool) \<leftarrow> protocol_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> protocol_OT12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> protocol_OT12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    view  \<leftarrow> R2_MPC2 ((xd, yd), (s, xb, yb));
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}" 

definition S_S_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> bool \<times> nat \<times> 'view_MPC2_2 \<times> bool \<times> nat) spmf"
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
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"

sublocale bid_prot_correct: semi_honest_det_correctness funct_bid protocol_bid valid_inputs_f_bid .

sublocale bid_prot_S: semi_honest_det_security funct_bid R_S_bid S_S_bid valid_inputs_f_bid extract_fst_bid id .

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
  assumes "(a, False) \<in> set_spmf (funct_bid (s, b, d))"
  shows "d > b"
  using assms apply(auto simp add: funct_bid_def)
  by (metis SUP_bot emptyE max.absorb1 mem_simps(1) not_le_imp_less prod.inject)

lemma funct_bid_False_d_le_b:
  assumes "(a, True) \<in> set_spmf (funct_bid (s, b, d))"
  shows "d \<le> b"
  using assms apply(auto simp add: funct_bid_def)
  by (metis SUP_bot emptyE mem_simps(1) prod.inject)

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
  shows "R_S_bid (s, b, d) = funct_bid (s, b, d) \<bind> (\<lambda> (wb,w). S_S_bid s (wb,w))"
proof-
  note [simp] = Let_def
  have R_initial: "R_S_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
    unfolding R_S_bid_def 
     apply(auto simp add: MPC1_correct OT12_correct_all MPC2_2  split del: if_split)+
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
     apply(auto simp add: OT12_correct_all MPC2_2 q_gt_0 valid_inputs_ot12_def split del: if_split)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    apply auto 
      apply (simp add: OT12_correct_all valid_inputs_ot12_def)+
    using MPC2_2 valid_inputs_mpc2_def assms
    by(auto simp add: split_def) 
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    have R_case_b_ge_d: "R_S_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
      apply(auto simp add: split_def R_initial f_ot12_def split del: if_split; intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?; auto)+
      using b_ge_d f_MPC1_contr_b_lt_d by blast +
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      have "R_S_bid (s, b, d) = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - wb)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(simp add: R_case_b_ge_d)
        using b_ge_d apply(simp add: f_MPC1_def)
       apply(auto simp add: funct_bid_def split del: if_split)
        using b_ge_s 
        by (simp add: max.absorb1)
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - wb)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        subgoal for a ba
          apply(cases ba) 
           apply auto
          using funct_bid_False_d_gt_b b_ge_d not_le by blast 
        subgoal for a ba
          apply(cases ba) 
           apply auto
          using funct_bid_False_d_gt_b b_ge_d not_le by blast 
        done
      ultimately show ?thesis 
        by(simp add: S_S_bid_def split del: if_split)
    next
      case False
      have "R_S_bid (s, b, d) = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        using b_ge_d R_case_b_ge_d 
        by(simp add: f_MPC1_def)
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        by(auto simp add: valid_inputs_mpc2_def q_gt_0 split_def assms MPC2_correct_unfold )
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = True \<oplus> xd;  
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - b)) mod q;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = rd';
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf False;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(simp add: q_gt_0 f_MPC2_def)
        by (metis 44 False Nat.add_diff_assoc assms(2) mod_le_divisor q_gt_0)
      ultimately have "R_S_bid (s, b, d) = return_pmf None"
       by(simp add: f_MPC1_def f_MPC2_def)
      moreover have "funct_bid (s, b, d) = return_pmf None"
        apply(simp add: funct_bid_def) 
        using False b_ge_d by auto
      ultimately show ?thesis by auto
    qed
  next
    case False
    hence d_gt_b: "b < d" by simp
    have R_case_d_gt_b: "R_S_bid (s, b, d) = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
      using d_gt_b apply(simp add: f_MPC1_def R_initial)
      apply(auto simp add: split_def f_MPC1_def f_MPC2_def f_ot12_def)
      by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    thus ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      have "R_S_bid (s, b, d) = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (wb + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        using  d_gt_b apply(simp add: f_MPC1_def R_case_d_gt_b)
        apply(auto simp add: funct_bid_def)
        using d_ge_s apply linarith 
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using d_gt_b less_le_not_le max_def 
          apply metis 
        by (auto simp add: d_gt_b less_imp_le max_absorb2)
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (wb + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - wb)) mod q) mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
         apply(auto simp add: 11 q_gt_0 f_MPC2_def f_MPC1_def)
        by (metis 1 assms(3) d_ge_s d_gt_b d_wins)+
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> map_spmf (\<lambda> rd'. (wb + rd') mod q) (sample_uniform q);
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - wb)) mod q) mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        by(simp add: bind_map_spmf o_def)
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = (rd + (rb' + (q - wb)) mod q) mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        by(simp add: samp_uni_plus_one_time_pad)
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = ((rd + (q - wb)) mod q + rb' mod q) mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
      proof-
        fix wb
        have "wb < q \<longrightarrow> (xa + (xb + (q - wb)) mod q) mod q = ((xa + (q - wb)) mod q + xb) mod q" for xb xa 
          by presburger
        thus ?thesis
          apply(auto simp add: q_gt_0)
          apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
            apply(auto simp add: q_gt_0)
          by (simp add: Groups.add_ac(3) linordered_field_class.sign_simps(2) mod_add_right_eq)+
      qed
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = (rb + (q - wb)) mod q;
    rb' \<leftarrow> sample_uniform q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rb') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
          apply (auto simp add: 44 mod_add_right_eq) 
           apply (smt False funct_bid_False_d_le_b)
        subgoal for a ba
          apply(cases ba) 
           apply auto
          using funct_bid_False_d_le_b
          using False by blast
        done
      ultimately show ?thesis 
        by(simp add: S_S_bid_def split del: if_split)
    next
      case False
      with d_gt_b have s_gt: "s > b" "s > d" by auto
      have "R_S_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(auto simp add: split_def R_initial)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto
        subgoal for a ba aa 
          apply(cases ba)
          unfolding f_ot12_def
          apply auto
          using f_MPC1_contr_b_ge_d d_gt_b by blast
        subgoal for a ba xa
          apply(cases ba)
          unfolding f_ot12_def
          apply auto
          using f_MPC1_contr_b_ge_d d_gt_b by blast
        done
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        using d_gt_b by(simp add: f_MPC1_def)
      also have "... = do {
    xd \<leftarrow> coin_spmf;
    let xb = False \<oplus> xd; 
    rb :: nat \<leftarrow> sample_uniform q;
    let rd = rb;
    rd' :: nat \<leftarrow> sample_uniform q;
    let rb' = (d + rd') mod q;
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out2;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using MPC2_correct_unfold assms unfolding valid_inputs_mpc2_def 
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
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view :: 'view_MPC2_2 \<leftarrow> S2_MPC2 (s, xb, yb) out2;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf False;
    return_spmf (s, xb, yb, view, xd, yd)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 f_MPC2_def) 
        using 555 assms
        by (simp add: False)
      ultimately have "R_S_bid (s, b, d) = return_pmf None"
        by(auto simp add: f_MPC1_def f_MPC2_def)
      moreover have "funct_bid (s, b, d) = return_pmf None"
        apply(simp add: funct_bid_def) 
        using s_gt(1) s_gt(2) by blast
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma perfect_security_S:
  assumes "s < q" and "b < q" and "d < q"
  shows "bid_prot_S.perfect_security (s, b, d)"
  using S_corrupt assms unfolding bid_prot_S.perfect_security_def extract_fst_bid_def 
  by(auto simp add: split_def)

definition R_B_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> 'view_MPC1 \<times> bool \<times> nat \<times> 'view1_OT_1 \<times> 'view2_OT_1 \<times> nat \<times> bool \<times> nat) spmf"
  where "R_B_bid inputs = do {
    let (s, b, d) = inputs;
    (view_MPC1, (xb, xd)) \<leftarrow> mpc1_1.real_view (b, d);
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> R1_OT12_1 (input1, xd);
    (_ :: unit, rd) \<leftarrow> protocol_OT12 (input1, xd);
    rd' \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view2_OT12 :: 'view2_OT_1 \<leftarrow> R2_OT12_1 (input1', xb);
    (_ :: unit, rb') \<leftarrow> protocol_OT12 (input1', xb);
    let yd = (rd + rd') mod q;   
    let yb = (rb + rb') mod q;
    (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"

definition R_D_bid :: "(nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> 'view_MPC2 \<times> bool \<times> 'view2_OT_1 \<times> nat \<times> nat \<times> 'view1_OT_1 \<times> 'view_MPC2_1 \<times> bool \<times> nat \<times> bool) spmf"
  where "R_D_bid inputs = do {
    let (s, b, d) = inputs;
    (view_MPC2 :: 'view_MPC2, (xb, xd)) \<leftarrow> mpc1_2.real_view (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    view2_OT12 :: 'view2_OT_1 \<leftarrow> R2_OT12_1 (input1, xd);
    (_ :: unit, rd :: nat) \<leftarrow> protocol_OT12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> R1_OT12_1 (input1', xb);
    (_ :: unit, rb') \<leftarrow> protocol_OT12 (input1', xb);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 \<leftarrow> R1_MPC2 ((xd,yd), (s,xb,yb));
    (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"

definition S_D_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> 'view_MPC2 \<times> bool \<times> 'view2_OT_1 \<times> nat \<times> nat \<times> 'view1_OT_1 \<times> 'view_MPC2_1 \<times> bool \<times> nat \<times> bool) spmf"
  where "S_D_bid d W = do {
        let (wb, w) = W;
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rb + rd') mod q; 
        let yb = ((rb + wb) + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 :: 'view_MPC2_1 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"

sublocale bid_prot_D: semi_honest_det_security funct_bid R_D_bid S_D_bid valid_inputs_f_bid extract_thrd_bid id .

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

lemma D_corrupt:
  assumes  "s < q" "b < q" "d < q"
  shows "R_D_bid (s, b, d) = funct_bid (s, b, d) \<bind> (\<lambda> (wb,w). S_D_bid d (wb, w))"
proof-
  have "R_D_bid (s, b, d) = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    view2_OT12 :: 'view2_OT_1 \<leftarrow> R2_OT12_1 (input1, xd);
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
    (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 \<leftarrow> R1_MPC2 ((xd,yd), (s,xb,yb));
    (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
    using assms valid_inputs_mpc1_def
    apply(simp add: R_D_bid_def split_def Let_def perfect_2_MPC1_unfold semi_honest_prob.ideal_view_def bind_map_spmf)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
       apply(auto simp add: bind_spmf_const OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 split del: if_split)
    using MPC2_correct[unfolded mpc2.correctness_def] valid_inputs_mpc2_def valid_inputs_ot12_def assms 
    by (auto simp add: OT12_correct_all valid_inputs_ot12_def OT12_1_unfold)
  also have "... = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    (_ :: unit, rd'' :: nat) \<leftarrow> f_ot12 (input1, xd);
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
    (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    view1_MPC2 \<leftarrow> R1_MPC2 ((xd,yd), (s,xb,yb));
    (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
    apply(auto simp add: OT12_2_1 split_def Let_def f_MPC1_def f_MPC2_def) 
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using valid_inputs_ot12_def assms 
      apply(auto simp add: OT12_2_1 split_def Let_def) 
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using valid_inputs_ot12_def assms 
    by(simp add: OT12_2_1 split_def Let_def) 
  also have "... = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    (_ :: unit, rd'' :: nat) \<leftarrow> f_ot12 (input1, xd);
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
    (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
    (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
    apply(simp add: Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    apply auto
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using valid_inputs_mpc2_def assms MPC2_1 assms
     by(auto simp add: q_gt_0 split_def)
    ultimately have R_initial: "R_D_bid (s, b, d) = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
    (_ :: unit, rd'' :: nat) \<leftarrow> f_ot12 (input1, xd);
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
    (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
    let yd = (rd + rd') mod q; 
    let yb = (rb + rb') mod q;
    (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
    (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    let wb = (yb + (q - yd)) mod q;
    let w = (xb \<oplus> xd);
    return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
    by argo
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    have R_case_b_ge_d: "R_D_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
      apply(simp add: Let_def R_initial f_ot12_def split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      using f_MPC1_contr_b_lt_d b_ge_d by auto
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      have "R_D_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        let rd = (rb + (q - b)) mod q;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
         _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        using R_case_b_ge_d
        apply(auto simp add: Let_def R_initial  split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        unfolding f_ot12_def
        subgoal for a ba
          apply(cases a; cases ba)
          apply auto (*takes a while*)
          using f_MPC1_contr_b_lt_d b_ge_d  by blast +
        done
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        by(simp add: Let_def)
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        unfolding f_ot12_def
        subgoal for a ba
          apply(cases a; cases ba)
          apply auto
          using f_MPC1_contr_b_lt_d b_ge_d by blast +
        done
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, met1, wb, w)}"
       apply(auto simp add: Let_def funct_bid_def f_MPC1_def) 
        using b_ge_s apply linarith 
        using b_ge_d by blast
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(simp add: Let_def f_MPC2_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 77 assms 
        by (metis b_ge_s lessThan_iff q_gt_0 set_spmf_sample_uniform)+
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 99 assms by(simp add: Let_def q_gt_0)
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = ((q - b) + rb) mod q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof-
        have "((q - b) + rb) mod q = (rb + (q - b)) mod q" for rb 
          using add.commute by presburger
        thus ?thesis by(simp add: Let_def)
      qed
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> map_spmf (\<lambda> rb.((q - b) + rb) mod q) (sample_uniform q); 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        by(simp add: bind_map_spmf o_def Let_def)
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + b) mod q + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        by(simp add: samp_uni_plus_one_time_pad)
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + wb) mod q + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(auto simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using b_ge_d b_ge_s b_wins by blast
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rd'' \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = ((rd'' + wb) + rd') mod q;
        let (out1, out2) = (True, True);
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof-
        have "((rd'' + wb) mod q + rd') mod q = ((rd'' + wb) + rd') mod q" for rd' rd'' wb
          using mod_add_left_eq by blast
        thus ?thesis by(simp)
      qed
      ultimately show ?thesis by(simp add: S_D_bid_def)
    next
      case False
      have "R_D_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def R_initial f_ot12_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_lt_d b_ge_d by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        let rd = (rb + (q - b)) mod q;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
         _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def R_initial f_ot12_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        subgoal for a ba
          apply(cases a; cases ba)
          apply auto
          using f_MPC1_contr_b_lt_d b_ge_d by auto
        done
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def f_ot12_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        subgoal for a ba
          apply(cases a; cases ba)
          apply auto
          using f_MPC1_contr_b_lt_d b_ge_d by auto
        done
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let rd'' = (rb + (q - b)) mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rd'' + rd') mod q; 
        let yb = (rb + rd') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf False;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd'', rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 f_MPC2_def f_MPC1_def)
        apply(auto simp add: Let_def f_MPC2_def f_MPC1_def)
        by (metis "44" False Nat.add_diff_assoc assms(2) mod_le_divisor q_gt_0) +
      ultimately have "R_D_bid (s, b, d) = return_pmf None"
        by(auto simp add: Let_def f_MPC1_def f_MPC2_def)
      moreover have "funct_bid (s, b, d) = return_pmf None"
        apply(simp add: funct_bid_def) 
        using False b_ge_d by auto
      ultimately show ?thesis by simp
    qed
    next
    case False
    hence d_gt_b: "b < d" by simp
    then show ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      have "R_D_bid (s,b,d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = rb;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def R_initial f_ot12_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_ge_d d_gt_b by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        subgoal for a xa
          apply(cases a; cases xa)
          unfolding f_ot12_def
             apply auto
          using f_MPC1_contr_b_ge_d d_gt_b by blast+
        done
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rb + rd') mod q; 
        let yb = (rb + (d + rd')) mod q;
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) True;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(simp add: Let_def f_MPC2_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 88 assms 
         apply (auto simp add: d_ge_s)
        by (simp add: mod_add_right_eq)
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rb + rd') mod q; 
        let yb = (rb + (wb + rd')) mod q;
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) True;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
        apply(auto simp add: Let_def funct_bid_def f_MPC1_def) 
        using d_ge_s apply linarith 
        using False apply blast 
        using d_ge_s not_less apply blast
         apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
         apply linarith
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?) 
        by linarith
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q; 
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let yd = (rb + rd') mod q; 
        let yb = ((rb + wb) + rd') mod q;
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) True;
        _ :: unit \<leftarrow> assert_spmf True;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, True, wb, w)}"
      proof- 
        have "(rb + (wb + rd')) mod q = ((rb + wb) + rd') mod q" for rd' rb wb by presburger
        thus ?thesis by(simp add: Let_def)
      qed
      ultimately show ?thesis 
        by(simp add: S_D_bid_def Let_def)
    next
      case False
      with d_gt_b have s_gt: "s > b" "s > d" by auto
      have "R_D_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        let rd'' = rb;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rd'';
        (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
        let yd = (rd + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rd, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def R_initial f_ot12_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_ge_d d_gt_b by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(simp add: Let_def split del: if_split)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
        subgoal for a xa
          apply(cases a; cases xa)
          unfolding f_ot12_def
          apply auto
          using f_MPC1_contr_b_ge_d d_gt_b by blast+
        done
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC2 :: 'view_MPC2 \<leftarrow> S2_MPC1 d xd;
        rb :: nat \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));  
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xd rb;
        rd' :: nat \<leftarrow> sample_uniform q;
        let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1' ();
        let rb' = (d + rd') mod q;
        let yd = (rb + rd') mod q; 
        let yb = (rb + rb') mod q;
        (out1, out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        view1_MPC2 \<leftarrow> S1_MPC2 (xd,yd) out1;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf False;
        let wb = (yb + (q - yd)) mod q;
        let w = (xb \<oplus> xd);
        return_spmf (d, view_MPC2, xd, view2_OT12, rb, rd', view1_OT12, view1_MPC2, met1, wb, w)}"
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 Let_def f_MPC2_def) 
        using assms
        by (simp add: "555" False)
      ultimately have "R_D_bid (s, b, d) = return_pmf None"
        by(auto simp add: Let_def f_MPC1_def f_ot12_def f_MPC2_def)
      moreover have "funct_bid (s, b, d) = return_pmf None"
        apply(simp add: funct_bid_def) 
        by (simp add: s_gt(1) s_gt(2))
      ultimately show ?thesis by simp
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

definition S_B_bid :: "nat \<Rightarrow> (nat \<times> bool) \<Rightarrow> (nat \<times> 'view_MPC1 \<times> bool \<times> nat \<times> 'view1_OT_1 \<times> 'view2_OT_1 \<times> nat \<times> bool \<times> nat) spmf"
  where "S_B_bid b W = do {
    let (wb,w) = W;
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd';
    let yd = ((rb + (q - wb)) + rd') mod q;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd', xd, yd)}"

sublocale bid_prot_B: semi_honest_det_security funct_bid R_B_bid S_B_bid valid_inputs_f_bid extract_snd_bid id .

lemma B_corrupt:
  assumes "s < q" "b < q" "d < q"
  shows "R_B_bid (s, b, d) = funct_bid (s, b, d) \<bind> (\<lambda> (wb,w). S_B_bid b (wb,w))"
proof-
  have R_initial: "R_B_bid (s, b, d) = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
    rd' \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb') \<leftarrow> f_ot12 (input1', xb);
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rb';
    let yd = (rd + rd') mod q;   
    let yb = (rb + rb') mod q;
    (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"
(*TODO: sort out this mess*)
    using assms valid_inputs_mpc1_def
    apply(auto simp add: R_B_bid_def split_def Let_def perfect_1_MPC1_unfold semi_honest_prob.ideal_view_def bind_map_spmf f_MPC1_def )
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
       apply(auto simp add:  OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 split del: if_split)
    using MPC2_correct[unfolded mpc2.correctness_def] valid_inputs_mpc2_def valid_inputs_ot12_def assms 
          apply (auto simp add: OT12_1_unfold OT12_correct_all f_ot12_def)
    using valid_inputs_ot12_def assms  OT12_2_sec_all 
      apply (auto simp add: split_def f_ot12_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
     apply auto using valid_inputs_mpc1_def assms   split_def f_ot12_def OT12_2_sec_all 
       apply (auto simp add: OT12_1_unfold split_def)
     apply(auto simp add:  OT12_correct_all  Let_def MPC2_correct[unfolded mpc2.correctness_def] OT12_1_1 OT12_2_1 split del: if_split)
     apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using OT12_2_1 valid_inputs_ot12_def apply(auto simp add: split_def OT12_correct_all)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    by (auto simp add: OT12_correct_all valid_inputs_ot12_def OT12_1_unfold)
  show ?thesis
  proof(cases "b \<ge> d")
    case b_ge_d: True
    hence R_bid_b_ge_d: "R_B_bid (s, b, d) = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    let rd = (rb + (q - b)) mod q;
    rd' \<leftarrow> sample_uniform q;
    let rb' = rd';
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rb';
    let yd = (rd + rd') mod q;
    let yb = (rb + rb') mod q;
    (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf met1;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rb', xd, yd)}"
      apply(simp add: R_initial Let_def f_ot12_def)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply auto
      using f_MPC1_contr_b_lt_d b_ge_d by auto
    show ?thesis 
    proof(cases "b \<ge> s")
      case b_ge_s: True
      hence "R_B_bid (s, b, d) = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(auto simp add: Let_def funct_bid_def R_bid_b_ge_d f_MPC1_def) 
      also have "... =  do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = ((rb + (q - wb)) mod q + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using b_ge_d b_ge_s b_wins by blast + 
      also have "... =  do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = ((rb + (q - wb)) + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(simp add: q_gt_0) 
        apply (simp add: mod_add_left_eq) 
        by (simp add: Groups.add_ac(2) mod_add_right_eq)
      also have "... =  do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = ((rb + (q - wb)) + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using assms valid_inputs_mpc2_def 
        by(auto simp add: Let_def funct_bid_def MPC2_correct_unfold)
      also have "... =  do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = ((rb + (q - wb)) + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf True;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def f_MPC2_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using 88 assms 
         apply (auto simp add: b_ge_s) 
        by (metis Nat.add_diff_assoc b_ge_d b_ge_s b_wins correct2 less_imp_le_nat mod_add_left_eq)
      also have "... = do {
        (wb,w) \<leftarrow> funct_bid (s, b, d);
        xd \<leftarrow> coin_spmf;
        let xb = w \<oplus> xd;
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = ((rb + (q - wb)) + rd') mod q;
        let yb = (rb + rd'') mod q;
        _ :: unit \<leftarrow> assert_spmf True;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(simp add: bind_spmf_const Let_def f_MPC2_def)
      ultimately show ?thesis  by(simp add: S_B_bid_def)
    next
      case False 
      hence "R_B_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using assms valid_inputs_mpc2_def
        by(auto simp add: Let_def  R_bid_b_ge_d MPC2_correct_unfold) 
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        let rd = (rb + (q - b)) mod q;
        rd' \<leftarrow> sample_uniform q;
        let rd'' = rd';
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf False;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0 Let_def f_MPC2_def) 
        by (metis "44" False Nat.diff_add_assoc assms(2) mod_le_divisor q_gt_0)
      ultimately have "R_B_bid (s, b, d) = return_pmf None"
        by(auto simp add: Let_def f_MPC1_def f_MPC2_def)
      moreover have "funct_bid (s, b, d) = return_pmf None" 
        apply(simp add: funct_bid_def) 
        using False b_ge_d by linarith
      ultimately show ?thesis by simp
    qed
  next
    case False
    hence d_gt_b: "b < d" by simp
    then show ?thesis 
    proof(cases "d \<ge> s")
      case d_ge_s: True
      hence "R_B_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def R_initial f_ot12_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto using f_MPC1_contr_b_ge_d d_gt_b by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;  
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply(auto simp add: q_gt_0)
        apply (simp add: "11" assms) 
        using "1" assms(3) by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd'' \<leftarrow> map_spmf (\<lambda> rd'. (d + rd') mod q) (sample_uniform q);
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(simp add: bind_map_spmf o_def Let_def)
      also have "... = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(simp add: samp_uni_plus_one_time_pad)    
      also have "... = do {
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    let rd = rb;
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = (rd + (rd'' + (q - d)) mod q) mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def f_ot12_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        apply auto
        using f_MPC1_contr_b_ge_d d_gt_b by auto
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    (xb,xd) \<leftarrow> f_MPC1 (b, d);
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = ((rb + (q - wb)) + rd'') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def)
       apply(auto simp add: Let_def funct_bid_def) 
        using d_ge_s apply linarith 
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
          apply (simp add: d_gt_b less_imp_le_nat linordered_field_class.sign_simps(3) max_def mod_add_right_eq semiring_normalization_rules(24))
         apply (simp add: d_gt_b linordered_field_class.sign_simps(2) linordered_field_class.sign_simps(3) max.absorb2 mod_add_right_eq order_less_imp_le)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
         apply (smt False add.assoc add.commute max.commute max_def mod_add_right_eq)
      proof -
        fix a :: bool and ba :: bool and x :: 'view_MPC1 and xa :: nat and xb :: 'view1_OT_1 and xc :: nat and xd :: 'view2_OT_1 and aa :: bool and bb :: bool
        have "max d b = d"
          by (metis d_gt_b max.strict_order_iff)
        then show "(assert_spmf aa \<bind> ((\<lambda>u. return_spmf (b, x, a, xa, xb, xd, xc, ba, (xa + (xc + (q - d)) mod q) mod q))::unit \<Rightarrow> (nat \<times> 'view_MPC1 \<times> bool \<times> nat \<times> 'view1_OT_1 \<times> 'view2_OT_1 \<times> nat \<times> bool \<times> nat) spmf)::(nat \<times> 'view_MPC1 \<times> bool \<times> nat \<times> 'view1_OT_1 \<times> 'view2_OT_1 \<times> nat \<times> bool \<times> nat) spmf) = assert_spmf aa \<bind> ((\<lambda>u. return_spmf (b, x, a, xa, xb, xd, xc, ba, (xa + (q - max b d) + xc) mod q))::unit \<Rightarrow> (nat \<times> 'view_MPC1 \<times> bool \<times> nat \<times> 'view1_OT_1 \<times> 'view2_OT_1 \<times> nat \<times> bool \<times> nat) spmf)"
          by (metis (no_types) Groups.add_ac(1) Groups.add_ac(2) max.commute mod_add_right_eq)
      qed
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = ((rb + (q - wb)) + rd'') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        by(auto simp add: f_MPC1_def Let_def funct_bid_def) 
      also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = ((rb + (q - wb)) + rd'') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp only: Let_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using valid_inputs_mpc2_def assms MPC2_correct_unfold  by auto
     also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = ((rb + (q - wb)) + rd'') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf True; 
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
       apply(auto simp add: Let_def f_MPC2_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+ 
       by (metis "44" assms(3) d_ge_s d_gt_b d_wins lessThan_iff mod_add_left_eq q_gt_0 set_spmf_sample_uniform)
     also have "... = do {
    (wb,w) \<leftarrow> funct_bid (s, b, d);
    xd \<leftarrow> coin_spmf;
    let xb = w \<oplus> xd;
    view_MPC1 \<leftarrow> S1_MPC1 b xb;
    rb \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
    rd'' \<leftarrow> sample_uniform q;
    view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
    let yd = ((rb + (q - wb)) + rd'') mod q;   
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
       by(simp add: bind_spmf_const q_gt_0 Let_def f_MPC2_def)
      ultimately show ?thesis  
        by(simp add: S_B_bid_def)
    next
      case False
      have "R_B_bid (s, b, d) = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> protocol_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
    return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(simp add: Let_def R_initial f_ot12_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
        using f_MPC1_contr_b_ge_d d_gt_b by auto
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf met1;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        using valid_inputs_mpc2_def assms
        by(auto simp add: Let_def funct_bid_def MPC2_correct_unfold)
      also have "... = do {
        (xb,xd) \<leftarrow> f_MPC1 (b, d);
        view_MPC1 \<leftarrow> S1_MPC1 b xb;
        rb \<leftarrow> sample_uniform q;
        let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
        view1_OT12 :: 'view1_OT_1 \<leftarrow> S1_OT12_1 input1 ();
        (_ :: unit, rd) \<leftarrow> f_ot12 (input1, xd);
        rd' \<leftarrow> sample_uniform q;
        let rd'' = (d + rd') mod q;
        view2_OT12 :: 'view2_OT_1 \<leftarrow> S2_OT12_1 xb rd'';
        let yd = (rd + rd') mod q;   
        let yb = (rb + rd'') mod q;
        (met1 :: bool, met2 :: bool) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
        _ :: unit \<leftarrow> assert_spmf False;
        return_spmf (b, view_MPC1, xb, rb, view1_OT12, view2_OT12, rd'', xd, yd)}"
        apply(auto simp only: Let_def f_ot12_def f_MPC2_def f_MPC1_def split_def)
        apply(intro bind_spmf_cong bind_spmf_cong[OF refl])+
                  apply(auto simp add: q_gt_0 Let_def split del: if_split) 
        by (smt "555" False assert_spmf_simps(2) assms(3) d_gt_b fst_conv not_le snd_conv)
      also have "... = return_pmf None"
      proof-
        have "f_ot12 (if \<not> y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb), y) = return_spmf ((),rb)" for y rb
          by(simp add: f_ot12_def)
        thus ?thesis
          by(auto simp add: Let_def f_MPC1_def f_ot12_def f_MPC2_def) 
      qed
      ultimately have "R_B_bid (s, b, d) = return_pmf None"
        by simp
      moreover have "funct_bid (s, b, d) = return_pmf None"
        apply(simp add: funct_bid_def) 
        using False d_gt_b by linarith
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma perfect_security_B:
  assumes "s < q" "b < q" "d < q"
  shows "bid_prot_B.perfect_security (s,b,d)"
  using B_corrupt assms unfolding bid_prot_B.perfect_security_def extract_snd_bid_def 
  by(auto simp add: split_def)

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


lemma 1 [simp]:
  assumes "Max {b,d} < q" and "b \<ge> d"
    and "(x,y) \<in> set_spmf (f_MPC1 (b, d))" shows "x = (\<not> y)"
  using assms by(auto simp add: f_MPC1_def)

lemma 2 [simp]:
  assumes "Max {b,d} < q" and "\<not> b \<ge> d"
    and "(x,y) \<in> set_spmf (f_MPC1 (b, d))" shows "\<not> (x = (\<not> y))"
  using assms by(auto simp add: f_MPC1_def)

lemma correctness_reserve_not_met:
  assumes "Max {b,d} < q"
    and "Max {b,d} < s"
    and "s < q"
  shows "protocol_bid (s, b, d) = funct_bid (s, b, d)"
proof-
  have [simp]: "b < q" "d < q" using assms by auto
  have "protocol_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out1;
    return_spmf ((yb + (q - yd)) mod q, (xb \<oplus> xd))}"
    apply(simp add: protocol_bid_def MPC1_correct MPC2_correct Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
     apply(auto simp add: valid_inputs_ot12_def OT12_correct_all Let_def MPC2_correct_unfold q_gt_0)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    by(auto simp add: valid_inputs_ot12_def valid_inputs_mpc2_def assms OT12_correct_all Let_def MPC2_correct_unfold q_gt_0)
  also have "...  = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb);
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf False;
    return_spmf ((yb + (q - yd)) mod q, (xb \<oplus> xd))}"
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    apply(auto simp add: q_gt_0 f_MPC2_def)
    unfolding f_ot12_def apply simp
    using 555 assms
    subgoal for a ba
      apply(cases a; cases ba)
         by (auto simp add: correct2)+
       done
     also have "... = funct_bid (s, b, d)" 
       apply(auto simp add: f_ot12_def Let_def funct_bid_def f_MPC1_def f_MPC2_def) 
       using assms by auto
  ultimately show ?thesis by argo
qed

lemma correctness_reserve_met:
  assumes "Max {b,d} < q"
    and "Max {b,d} \<ge> s"
    and "s < q"
  shows "protocol_bid (s, b, d) = funct_bid (s, b, d)"
proof-
  have prot_init: "protocol_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    (b_out1, b_out2) \<leftarrow> f_MPC2 ((xd,yd), (s,xb,yb));
    _ :: unit \<leftarrow> assert_spmf b_out1;
    return_spmf ((yb + (q - yd)) mod q, (xb \<oplus> xd))}"
    apply(simp add: protocol_bid_def MPC1_correct MPC2_correct Let_def)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
     apply(auto simp add: valid_inputs_ot12_def OT12_correct_all Let_def MPC2_correct_unfold q_gt_0)
    apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    by(auto simp add: valid_inputs_ot12_def valid_inputs_mpc2_def assms OT12_correct_all Let_def MPC2_correct_unfold q_gt_0)
  show ?thesis
  proof(cases "b \<ge> d")
    case True
    have "protocol_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    return_spmf ((yb + (q - yd)) mod q, (xb \<oplus> xd))}"
      apply(simp add: prot_init)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(auto simp add: q_gt_0 f_MPC2_def Let_def)
      unfolding f_ot12_def apply auto
         apply (metis "44" Max.singleton Max_insert Nat.add_diff_assoc True assms(1) assms(2) finite.intros(1) finite_insert max.orderE mod_le_divisor q_gt_0)
      using True f_MPC1_contr_b_lt_d apply blast +
      by (metis "44" Max.singleton Max_insert Nat.add_diff_assoc True assms(1) assms(2) finite.intros(1) finite_insert max.orderE mod_le_divisor q_gt_0)
    also have "... = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    return_spmf ((yb + (q - yd)) mod q, True)}"
      apply(simp add: Let_def split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      using True assms f_MPC1_contr_b_lt_d correct2 q_gt_0 by auto
    also have "... = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    return_spmf (b, True)}"
      apply(simp add: Let_def split del: if_split)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      unfolding f_ot12_def apply auto
      using True f_MPC1_contr_b_lt_d apply blast
        apply (metis "44" Max.singleton Max_insert True assms(1) finite.intros(1) finite_insert lessThan_iff max.orderE q_gt_0 set_spmf_sample_uniform)
       apply (metis "44" Max.singleton Max_insert True assms(1) finite.intros(1) finite_insert lessThan_iff max.orderE q_gt_0 set_spmf_sample_uniform)
      using True f_MPC1_contr_b_lt_d by blast
    also have "... = do {
    return_spmf (b, True)}"
    proof-
      have "f_ot12 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q), \<not> y) = return_spmf ((),rd')" for y rd'
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb), y) = return_spmf ((),(rb + (q - b)) mod q)" for rb y 
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if \<not> y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb), y) = return_spmf ((),rb)" for y rb 
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q), y) = return_spmf ((), (d + rd') mod q)" for y rd'
        by(auto simp add: f_ot12_def)
      ultimately show ?thesis
        using assms
        by(auto simp add: f_MPC1_def bind_spmf_const)
    qed
    ultimately show ?thesis 
      apply(auto simp add: funct_bid_def)
      using True assms by auto
  next
    case False
    have "protocol_bid (s, b, d) = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    return_spmf ((yb + (q - yd)) mod q,(xb \<oplus> xd))}"
      apply(simp add: prot_init)
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(auto simp add: q_gt_0 f_MPC2_def Let_def)
      unfolding f_ot12_def apply auto 
      using False f_MPC1_contr_b_ge_d linorder_not_le "555" False assms(1) assms(2) by auto
    also have "... = do {
    (xb :: bool,xd :: bool) \<leftarrow> f_MPC1 (b, d);
    rb :: nat \<leftarrow> sample_uniform q;
    let input1 = (if (xb = False) then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb));
    (_ :: unit, rd :: nat) \<leftarrow> f_ot12 (input1, xd);
    rd' :: nat \<leftarrow> sample_uniform q;
    let input1' = (if (xd = False) then ((d + rd') mod q, rd') else (rd', (d + rd') mod q));
    (_ :: unit, rb' :: nat) \<leftarrow> f_ot12 (input1', xb); 
    let yb = (rb + rb') mod q;
    let yd = (rd + rd') mod q;
    return_spmf (d, False)}"
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
      apply(auto simp add: q_gt_0 f_MPC2_def)
      unfolding f_ot12_def apply auto
      using False bidding_prot_base.f_MPC1_contr_b_ge_d bidding_prot_base_axioms not_le_imp_less apply blast
      using assms(1) correct1 apply auto
      using False bidding_prot_base.f_MPC1_contr_b_ge_d bidding_prot_base_axioms linorder_not_le apply blast
      using "2" False assms(1) by blast +
    also have "... = do {
    return_spmf (d, False)}"
    proof-
      have "f_ot12 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q), \<not> y) = return_spmf ((),rd')" for y rd'
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb), y) = return_spmf ((),(rb + (q - b)) mod q)" for rb y 
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if \<not> y then (rb, (rb + (q - b)) mod q) else ((rb + (q - b)) mod q, rb), y) = return_spmf ((),rb)" for y rb 
        by(auto simp add: f_ot12_def)
      moreover have "f_ot12 (if \<not> y then ((d + rd') mod q, rd') else (rd', (d + rd') mod q), y) = return_spmf ((), (d + rd') mod q)" for y rd'
        by(auto simp add: f_ot12_def)
      ultimately show ?thesis
        using assms
        by(auto simp add: f_MPC1_def bind_spmf_const)
    qed
    ultimately show ?thesis 
      apply(auto simp add: funct_bid_def)
      using False assms by auto
  qed
qed

lemma correctness:
  shows "bid_prot_correct.correctness (s, b, d)" 
  unfolding bid_prot_correct.correctness_def 
  by(cases "s \<le> Max {b, d}"; auto simp add: valid_inputs_f_bid_def correctness_reserve_met correctness_reserve_not_met not_le)

end 

end 