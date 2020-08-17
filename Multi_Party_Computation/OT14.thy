subsection \<open>1-out-of-2 OT to 1-out-of-4 OT\<close>

text \<open>Here we construct a protocol that achieves 1-out-of-4 OT from 1-out-of-2 OT. We follow the protocol
for constructing 1-out-of-n OT from 1-out-of-2 OT from \cite{DBLP:books/cu/Goldreich2004}. We assume the security
properties on 1-out-of-2 OT.\<close>

theory OT14 imports
  Semi_Honest
  OT_Functionalities
  Uniform_Sampling
begin

fun valid_inputs_ot12 :: "bool inputs_ot12 list \<Rightarrow> bool"
  where "valid_inputs_ot12 [M2 (b0, b1), C1 \<sigma>] = True" 

fun valid_inputs_ot14 :: "bool inputs_ot14 list \<Rightarrow> bool"
  where "valid_inputs_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = True" 

type_synonym input1 = "bool \<times> bool \<times> bool \<times> bool"
type_synonym input2 = "bool \<times> bool"
type_synonym 'ot12_view1' view1 = "((bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view1' \<times> 'ot12_view1' \<times> 'ot12_view1')"
type_synonym 'ot12_view2' view2 = "( (bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view2' \<times> 'ot12_view2' \<times> 'ot12_view2')"

locale ot14_base =   ot12: semi_honest_det_correctness f_ot12 protocol_ot12 valid_inputs_ot12
  + ot12_1: semi_honest_det_security f_ot12 protocol_ot12 valid_inputs_ot12 0 R1_OT12 S1_OT12 
  + ot12_2: semi_honest_det_security f_ot12 protocol_ot12 valid_inputs_ot12 1 R2_OT12 S2_OT12
  for R1_OT12 :: "bool inputs_ot12 list \<Rightarrow> 'ot12_view1 spmf"
    and S1_OT12 
    and R2_OT12 :: "bool inputs_ot12 list \<Rightarrow> 'ot12_view2 spmf"
    and  S2_OT12  protocol_ot12
    +
  fixes ot12_adv_P1 :: real
  assumes ot12_advantage_P1: "ot12_1.advantage [M2 (m0,m1), C1 \<sigma>] D \<le> ot12_adv_P1"
    and ot12_perfect_security_P2: "ot12_2.perfect_security [M2 (m0,m1), C1 \<sigma>]"
    and ot12_correct: "ot12.correctness [M2 (m0,m1), C1 \<sigma>]"
begin

lemma OT_12_P1_assms_bound': "\<bar>spmf (ot12_1.real_view [M2 (m0,m1), C1 \<sigma>] \<bind> (\<lambda> view. ((D::bool inputs_ot12 \<times> 'ot12_view1 \<Rightarrow> bool spmf) view)))  True 
                - spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ()) \<bind> (\<lambda> view. (D view))) True\<bar> \<le> ot12_adv_P1"
  using ot12_advantage_P1 unfolding ot12_1.advantage_def by simp


lemma OT_12_P2_assm: "R2_OT12 [M2 (m0,m1), C1 \<sigma>] = return_spmf (f_ot12 [M2 (m0,m1), C1 \<sigma>]) \<bind> (\<lambda> outputs. S2_OT12 (C1 \<sigma>) (nth outputs 1))"
  using ot12_perfect_security_P2 ot12_2.perfect_security_def ot12_2.perfect_sec_views_equal by simp

fun protocol_ot14 :: "bool inputs_ot14 list \<Rightarrow> (bool outputs_ot14 list) spmf"
  where "protocol_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool\<leftarrow> coin_spmf;
    S2 :: bool\<leftarrow> coin_spmf;
    S3 :: bool\<leftarrow> coin_spmf;
    S4 :: bool\<leftarrow> coin_spmf;
    S5 :: bool\<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m00;
    let a1 = S0 \<oplus> S3 \<oplus> m01;
    let a2 = S1 \<oplus> S4 \<oplus> m10;
    let a3 = S1 \<oplus> S5 \<oplus> m11;
    outputs_i :: bool outputs_ot12 list \<leftarrow> protocol_ot12 ([M2 (S0, S1), C1 c0] :: bool inputs_ot12 list);
    outputs_j :: bool outputs_ot12 list \<leftarrow> protocol_ot12 ([M2 (S2, S3), C1 c1] :: bool inputs_ot12 list);
    outputs_k :: bool outputs_ot12 list \<leftarrow> protocol_ot12 ([M2 (S4, S5), C1 c1] ::  bool inputs_ot12 list);
    let s2 = (xor_ot12 (nth outputs_i 1) (if c0 then (nth outputs_k 1) else (nth outputs_j 1))) \<oplus> (if c0 then (if c1 then a3 else a2) else (if c1 then a1 else a0)) ;
    return_spmf ([U_ot14 (), P_ot14 s2])}"

sublocale ot14_correct: semi_honest_det_correctness f_ot14 protocol_ot14 valid_inputs_ot14 .

lemma ot12_correct_unfold: "protocol_ot12 [M2 (S0, S1), C1 a] = return_spmf (f_ot12 [M2 (S0, S1), C1 a])" for a
  using ot12_correct[unfolded ot12.correctness_def] valid_inputs_ot12.simps by presburger

lemma ot14_correct_unfold: 
  shows "return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]) = protocol_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
proof-
  have "(S1 = (\<not> S5)) = (S1 = (S5 = (\<not> m))) = m" for S1 S5 m by blast
  thus ?thesis 
    by(auto simp add: ot12_correct_unfold bind_spmf_const ot12_correct)
qed

lemma ot14_correct: "ot14_correct.correctness [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  unfolding ot14_correct.correctness_def
  using ot14_correct_unfold by simp

fun R1_14 :: "bool inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
  where "R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S0, S1), C1 c0]; 
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf ((S0, S1, S2, S3, S4, S5), a, b, c)}"

fun R1_14_interm1 :: "bool inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
  where "R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U_ot12 ()); 
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf ((S0, S1, S2, S3, S4, S5), a, b, c)}"

fun real_view1_14_interm1 :: "bool inputs_ot14 list \<Rightarrow> (bool inputs_ot14 \<times> 'ot12_view1 view1) spmf"
  where "real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U_ot12 ()); 
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf (M4 (m00, m01, m10, m11), (S0, S1, S2, S3, S4, S5), a, b, c)}"

fun R1_14_interm2 :: "bool inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
  where "R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U_ot12 ()); 
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2, S3)) (U_ot12 ());
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf ((S0, S1, S2, S3, S4, S5), a, b, c)}"

fun real_view2_14_interm2 :: "bool inputs_ot14 list \<Rightarrow> (bool inputs_ot14 \<times> 'ot12_view1 view1) spmf"
  where "real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U_ot12 ()); 
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2, S3)) (U_ot12 ());
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf (M4 (m00, m01, m10, m11),(S0, S1, S2, S3, S4, S5), a, b, c)}"

fun S1_14 :: "bool inputs_ot14 \<Rightarrow> bool outputs_ot14 \<Rightarrow> 'ot12_view1 view1 spmf"
  where "S1_14 (M4 (m00, m01, m10, m11)) (U_ot14 ()) = do {   
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U_ot12 ()); 
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2, S3)) (U_ot12 ());
    c :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S4, S5)) (U_ot12 ());
    return_spmf ((S0, S1, S2, S3, S4, S5), a, b, c)}"

sublocale ot14_P1: semi_honest_det_security f_ot14 protocol_ot14 valid_inputs_ot14 0 R1_14 S1_14 .

lemma reduction_step1: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (ot14_P1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
              \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
  including monad_normalisation
proof-
  define A1' where "A1' == \<lambda> (view :: bool inputs_ot12 \<times> 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    let R = (M4 (m00, m01, m10, m11), (m0,m1, S2, S3, S4, S5), snd view, b, c);
    D1 R}"
  have "\<bar>spmf (bind_spmf (ot14_P1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
              \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1' view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
    unfolding ot14_P1.real_view_def ot12_1.ideal_view_def ot12_1.real_view_def
    by(auto simp add: pair_spmf_alt_def A1'_def Let_def split_def)
  then show ?thesis by auto
qed

lemma reduction_step1': "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>
            \<le> ot12_adv_P1"
  (is "?lhs \<le> ot12_adv_P1")
proof-
  have int1: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>(m0,m1). spmf ((ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))) True)" 
    and int2: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>(m0,m1). spmf ((ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))) True)" 
    by(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)+
  have "?lhs = 
            \<bar>LINT (m0,m1)|measure_spmf (pair_spmf coin_spmf coin_spmf). spmf ((ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))) True 
              - spmf ((ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))) True\<bar>"
    apply(subst (1 2) spmf_bind) using int1 int2 by(simp add: split_def)
  also have "... \<le> LINT (m0,m1)|measure_spmf (pair_spmf coin_spmf coin_spmf). 
               \<bar>spmf ((ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))) True - spmf ((ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))) True\<bar>"
    by(rule integral_abs_bound[THEN order_trans]; simp add: split_def split_beta)
  ultimately have "?lhs \<le> LINT (m0,m1)|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                      \<bar>spmf ((ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))) True - spmf ((ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))) True\<bar>"
    by simp
  also have "LINT (m0,m1)|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                \<bar>spmf ((ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))) True 
                    - spmf ((ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))) True\<bar> \<le> ot12_adv_P1"
    apply(rule integral_mono[THEN order_trans])
       apply(rule measure_spmf.integrable_const_bound[where B=2])
        apply clarsimp
        apply(rule abs_triangle_ineq4[THEN order_trans])
    subgoal for m0 m1
      using pmf_le_1[of "(ot12_1.real_view [M2 (m0,m1), C1 c0]) \<bind> (\<lambda>view. A1 view (m0, m1))" "Some True"]
        pmf_le_1[of "(ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) \<bind> (\<lambda> view. (A1 view (m0,m1)))" "Some True"]
      by simp
       apply simp
      apply(rule measure_spmf.integrable_const)
     apply clarify
     apply(rule OT_12_P1_assms_bound'[rule_format]) 
    by simp
  ultimately show ?thesis by simp
qed

lemma reduction_step2: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
  including monad_normalisation
proof-
  define A1' where "A1' == \<lambda> (view :: bool inputs_ot12 \<times> 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2,S3)) (U_ot12 ());
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    let R = (M4 (m00, m01, m10, m11), (S2,S3, m0, m1, S4, S5), a, snd view, c);
    D1 R}"
  have "\<bar>spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding  A1'_def Let_def split_def ot12_1.real_view_def ot12_1.ideal_view_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by simp 
    also have "(bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) =  (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding A1'_def Let_def split_def ot12_1.ideal_view_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
      by(simp)  
    ultimately show ?thesis by simp
  qed
  then show ?thesis by auto
qed

lemma reduction_step3: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
proof-
  define A1' where "A1' == \<lambda> (view :: bool inputs_ot12 \<times> 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2,S3)) (U_ot12 ());
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S4, S5)) (U_ot12 ());
    let R = (M4 (m00, m01, m10, m11), (S2,S3, S4, S5,m0, m1), a, b, snd view);
    D1 R}"
  have "\<bar>spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) 
            = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding A1'_def Let_def split_def ot12_1.real_view_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by(simp)
    also have "(bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) 
                = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding Let_def A1'_def split_def ot14_P1.ideal_view_def ot12_1.ideal_view_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      including monad_normalisation by(simp)
    ultimately show ?thesis by simp
  qed
  then show ?thesis by auto
qed

lemma reduction_P1: 
  shows "\<bar>spmf (bind_spmf (ot14_P1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True 
            - spmf (bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) True\<bar> 
                \<le> 3 * ot12_adv_P1"
    (is "?lhs \<le> ?rhs")
proof-
  have lhs: "?lhs \<le> \<bar>spmf (bind_spmf (ot14_P1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> + 
                     \<bar>spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> +
                      \<bar>spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) True\<bar>"
    by simp
  obtain A1 where A1: "\<bar>spmf (bind_spmf (ot14_P1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
              \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
    using reduction_step1 by blast
  obtain A2 where A2: "\<bar>spmf (bind_spmf (real_view1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar>"
    using reduction_step2 by blast
  obtain A3 where A3: "\<bar>spmf (bind_spmf (real_view2_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (ot14_P1.ideal_view (M4 (m00, m01, m10, m11)) (U_ot14 ())) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using reduction_step3 by blast
  have lhs_bound: "?lhs \<le> \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> + 
                   \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar> +
                     \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using A1 A2 A3 lhs by argo
  have bound1: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> 
                      \<le> ot12_adv_P1" 
    and bound2:  "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar>
                      \<le> ot12_adv_P1" 
    and bound3: " \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.real_view [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (ot12_1.ideal_view (M2 (m0,m1)) (U_ot12 ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar> \<le> ot12_adv_P1"
    using reduction_step1' by auto
  thus ?thesis
    using reduction_step1' lhs_bound by argo  
qed

text\<open>Party 2 security.\<close>

lemma coin_coin: "map_spmf (\<lambda> S0. S0 \<oplus> S3 \<oplus> m1) coin_spmf = coin_spmf"
  (is "?lhs = ?rhs")
proof-
  have lhs: "?lhs = map_spmf (\<lambda> S0. S0 \<oplus> (S3 \<oplus> m1)) coin_spmf" by blast
  also have op_eq: "... = map_spmf ((\<oplus>) (S3 \<oplus> m1)) coin_spmf" 
    by (metis xor_bool_def)
  also have "... = ?rhs" 
    using xor_uni_samp by fastforce
  ultimately show ?thesis 
    using op_eq by auto
qed

lemma coin_coin': "map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf = coin_spmf"
proof-
  have "map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf = map_spmf (\<lambda> S3. S3 \<oplus> S0 \<oplus> m1) coin_spmf" 
    by (metis xor_left_commute)
  thus ?thesis using coin_coin by simp
qed

fun R2_14:: "bool inputs_ot14 list \<Rightarrow> 'ot12_view2 view2 spmf"
  where "R2_14 [M4 (m0,m1,m2,m3), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'ot12_view2 \<leftarrow> R2_OT12 [M2 (S0,S1), C1 c0];
    b :: 'ot12_view2 \<leftarrow> R2_OT12 [M2 (S2,S3), C1 c1];
    c :: 'ot12_view2 \<leftarrow> R2_OT12 [M2 (S4,S5), C1 c1];
    return_spmf ((a0,a1,a2,a3), a,b,c)}"

fun S2_14 :: "bool inputs_ot14 \<Rightarrow> bool outputs_ot14 \<Rightarrow> 'ot12_view2 view2 spmf"
  where "S2_14 (C2 (c0,c1)) (P_ot14 out) = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 :: bool \<leftarrow> coin_spmf;
    let a0' = (if ((\<not> c0) \<and> (\<not> c1)) then (S0 \<oplus> S2 \<oplus> out) else a0);
    let a1' = (if ((\<not> c0) \<and> c1) then (S0 \<oplus> S3 \<oplus> out) else a1);
    let a2' = (if (c0 \<and> (\<not> c1)) then (S1 \<oplus> S4 \<oplus> out) else a2);
    let a3' = (if (c0 \<and> c1) then (S1 \<oplus> S5 \<oplus> out) else a3);
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c0) (if c0 then (P_ot12 S1) else (P_ot12 S0));
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c1) (if c1 then (P_ot12 S3) else (P_ot12 S2));
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c1) (if c1 then (P_ot12 S5) else (P_ot12 S4));
    return_spmf ((a0',a1',a2',a3'), a,b,c)}"

sublocale P2_security: semi_honest_det_security f_ot14 protocol_ot14 valid_inputs_ot14 1 R2_14 S2_14 .

(*lemma
  shows "P2_security.perfect_security [M4 (m00, m01, m10, m11), C2 (c0,c1)]"
  unfolding P2_security.perfect_security_def P2_security.real_view_def P2_security.ideal_view_def
  apply auto
  apply(simp add: bind_spmf_const)
     apply(intro bind_spmf_cong[OF refl]; clarsimp?)+


lemma
  assumes "valid_inputs_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]"
  shows "(P2_security.real_view [M4 (m0,m1,m2,m3), C2 (c0,c1)] \<bind> (D2 :: (bool inputs_ot14 \<times> (bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view2 \<times> 'ot12_view2 \<times> 'ot12_view2) \<Rightarrow> bool spmf) )  
                = (return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]) \<bind> (\<lambda> outputs_ot12. P2_security.ideal_view (C2 (c0,c1)) (nth outputs_ot12 1) \<bind> D2))"

  unfolding P2_security.real_view_def P2_security.ideal_view_def

  apply auto
  apply(simp add: bind_spmf_const)
     apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
  apply(simp add: bind_spmf_const)

lemma P2_OT_14_FT:
  shows "R2_14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]  
              = f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)] \<bind> (\<lambda> outputs. S2_14 (C2 (c0,c1)) (nth outputs 1))"
*)
lemma P2_OT_14_FT:
  shows "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (False, True)]  
              = return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (False, True)]) \<bind> (\<lambda> outputs. P2_security.ideal_view (C2 (False,True)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (False, True)] =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def OT_12_P2_assm semi_honest_det_security.real_view_def)
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> map_spmf (\<lambda> S1. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: bind_spmf_const semi_honest_det_security.ideal_view_def)
qed

lemma P2_OT_14_TT: 
  shows "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (True,True)] 
            = return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (True,True)]) 
              \<bind> (\<lambda> outputs. P2_security.ideal_view (C2 (True,True)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (True,True)] =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def OT_12_P2_assm Let_def semi_honest_det_security.real_view_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S0. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)    
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    by(simp add: bind_spmf_const semi_honest_det_security.ideal_view_def)
qed

lemma P2_OT_14_FF: 
  shows "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (False, False)] 
             = return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (False, False)]) 
                \<bind> (\<lambda> outputs. P2_security.ideal_view (C2 (False, False)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (False, False)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def OT_12_P2_assm Let_def semi_honest_det_security.real_view_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> map_spmf (\<lambda> S1. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: bind_spmf_const semi_honest_det_security.ideal_view_def)
qed

lemma P2_OT_14_TF: "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (True,False)] = return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (True,False)]) 
          \<bind> (\<lambda> outputs. P2_security.ideal_view (C2 (True,False)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (True,False)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    apply(simp add: OT_12_P2_assm Let_def semi_honest_det_security.real_view_def)
    apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S0. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P_ot12 S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P_ot12 S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    by(simp add: bind_spmf_const semi_honest_det_security.ideal_view_def)
qed

lemma perfect_security_P2: 
  shows "P2_security.real_view [M4 (m0,m1,m2,m3), C2 (c0,c1)] 
            = return_spmf (f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]) 
              \<bind> (\<lambda> outputs. P2_security.ideal_view (C2 (c0,c1)) (nth outputs 1))"
  apply(cases c0; cases c1)
  using P2_OT_14_FF P2_OT_14_TF P2_OT_14_FT P2_OT_14_TT by auto


lemma ot14_security_P1: "ot14_P1.advantage [M4 (m0,m1,m2,m3), C2 (c0,c1)] D \<le> 3 * ot12_adv_P1"
  unfolding ot14_P1.advantage_def   
  using reduction_P1 by simp

lemma ot14_security_P2: "P2_security.perfect_security [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  unfolding P2_security.perfect_security_def
  using perfect_security_P2 by simp



end

locale OT_14_asymp =
  fixes R1_OT12 :: "nat \<Rightarrow> bool inputs_ot12 list \<Rightarrow> 'ot12_view1 spmf"
    and S1_OT12 :: "nat \<Rightarrow> bool inputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> 'ot12_view1 spmf"
    and R2_OT12 :: "nat \<Rightarrow> bool inputs_ot12 list \<Rightarrow> 'ot12_view2 spmf"
    and S2_OT12 :: "nat \<Rightarrow> bool inputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> 'ot12_view2 spmf"
    and protocol_ot12 :: "nat \<Rightarrow> bool inputs_ot12 list \<Rightarrow> bool outputs_ot12 list spmf"
    and ot12_adv_P1 :: "nat \<Rightarrow> real"
  assumes ot14_base: "\<And> (n::nat). ot14_base (R1_OT12 n) (S1_OT12 n) (R2_OT12 n) (S2_OT12 n) (protocol_ot12 n) (ot12_adv_P1 n)"
begin 

sublocale ot14_base "(R1_OT12 n)" "(S1_OT12 n)" "(R2_OT12 n)" "(S2_OT12 n)" "(protocol_ot12 n)" "(ot12_adv_P1 n)" 
  using local.ot14_base by simp

lemma bound_P1: "ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D \<le> 3 * (ot12_adv_P1 n)"
  by(rule ot14_security_P1) 

theorem OT_14_P1_asym_sec: "negligible (\<lambda> n. ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D)" if "negligible (\<lambda> n. ot12_adv_P1 n)"
proof-
  have adv_neg: "negligible (\<lambda>n. 3 * ot12_adv_P1 n)" using that negligible_cmultI by simp
  have "\<bar>ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D\<bar> \<le> \<bar>3 * (ot12_adv_P1 n)\<bar>" for n 
  proof -
    have "\<bar>ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D\<bar> \<le> 3 * ot12_adv_P1 n"
      using ot14_P1.advantage_def ot14_base.ot14_security_P1 ot14_base_axioms bound_P1 by auto
    then show ?thesis
      by (meson abs_ge_self order_trans)
  qed
  thus ?thesis using bound_P1 negligible_le adv_neg 
    by (metis (no_types, lifting) negligible_absI)
qed

theorem ot14_: "P2_security.perfect_security n [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  by(rule ot14_security_P2)

theorem ot14_correct: "ot14_correct.correctness n [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  by(rule ot14_correct)

end

end