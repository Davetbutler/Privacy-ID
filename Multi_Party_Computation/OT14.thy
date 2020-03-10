subsection \<open>1-out-of-2 OT to 1-out-of-4 OT\<close>

text \<open>Here we construct a protocol that achieves 1-out-of-4 OT from 1-out-of-2 OT. We follow the protocol
for constructing 1-out-of-n OT from 1-out-of-2 OT from \cite{DBLP:books/cu/Goldreich2004}. We assume the security
properties on 1-out-of-2 OT.\<close>

theory OT14 imports
  Semi_Honest
  OT_Functionalities
  Uniform_Sampling
begin
sledgehammer_params[timeout = 1000]
datatype inputs_ot12 = M2 "(bool \<times> bool)" | C1 bool

datatype outputs = P bool | U unit

fun xor :: "outputs \<Rightarrow> outputs \<Rightarrow> bool"
  where "xor (P a) (P b) = a \<oplus> b"

fun f_ot12 :: "inputs_ot12 list \<Rightarrow> (outputs list) spmf"
  where "f_ot12 [M2 (m0,m1), C1 \<sigma>] = return_spmf ([U (), if \<sigma> then (P m1) else (P m0)])"

fun valid_inputs_ot12 :: "inputs_ot12 list \<Rightarrow> bool"
  where "valid_inputs_ot12 [M2 (b0, b1), C1 \<sigma>] = True" 

datatype inputs_ot14 = M4 "(bool \<times> bool \<times> bool \<times> bool)" | C2 "(bool \<times> bool)"

fun f_ot14 :: "inputs_ot14 list \<Rightarrow> (outputs list) spmf"
  where "f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] 
              = return_spmf ([U (), if c0 then (if c1 then P (m11) else (P m10)) else (if c1 then (P m01) else (P m00))])"

fun valid_inputs_ot14 :: "inputs_ot14 list \<Rightarrow> bool"
  where "valid_inputs_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = True" 

type_synonym input1 = "bool \<times> bool \<times> bool \<times> bool"
type_synonym input2 = "bool \<times> bool"
type_synonym 'ot12_view1' view1 = "(inputs_ot14 \<times> (bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view1' \<times> 'ot12_view1' \<times> 'ot12_view1')"
type_synonym 'ot12_view2' view2 = "(inputs_ot14 \<times> (bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view2' \<times> 'ot12_view2' \<times> 'ot12_view2')"

locale ot14_base = ot12_1: semi_honest_det_security 0 f_ot12 R1_OT12 S1_OT12 valid_inputs_ot12 + 
  ot12_2: semi_honest_det_security 1 f_ot12 R2_OT12 S2_OT12 valid_inputs_ot12 +
  ot12: semi_honest_det_correctness f_ot12 protocol_ot12 valid_inputs_ot12
  for R1_OT12 :: "inputs_ot12 list \<Rightarrow> 'ot12_view1 spmf"
    and S1_OT12 
    and R2_OT12 :: "inputs_ot12 list \<Rightarrow> 'ot12_view2 spmf"
    and  S2_OT12 protocol_ot12
    +
  fixes ot12_adv_P1 :: real
  assumes ot12_advantage_P1: "ot12_1.advantage [M2 (m0,m1), C1 \<sigma>] D \<le> ot12_adv_P1"
    and ot12_perfect_security_P2: "ot12_2.perfect_security [M2 (m0,m1), C1 \<sigma>]"
    and ot12_correct: "ot12.correctness [M2 (m0,m1), C1 \<sigma>]"
begin

lemma OT_12_P1_assms_bound': "\<bar>spmf (bind_spmf (R1_OT12 [M2 (m0,m1), C1 \<sigma>]) (\<lambda> view. (D view ))) True 
                - spmf (bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (D view))) True\<bar> \<le> ot12_adv_P1"
proof-
  have "ot12_1.advantage [M2 (m0,m1), C1 \<sigma>] D =
                     \<bar>spmf (bind_spmf (R1_OT12 [M2 (m0,m1), C1 \<sigma>]) (\<lambda> view. (D view ))) True 
                - spmf (bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (D view ))) True\<bar>"
    using ot12_1.advantage_def by auto
  thus ?thesis  
    by(metis ot12_advantage_P1)
qed

lemma OT_12_P2_assm: "R2_OT12 [M2 (m0,m1), C1 \<sigma>] = f_ot12 [M2 (m0,m1), C1 \<sigma>] \<bind> (\<lambda> outputs. S2_OT12 (C1 \<sigma>) (nth outputs 1))"
  using ot12_perfect_security_P2 ot12_2.perfect_security_def by simp

fun protocol_ot14 :: "inputs_ot14 list \<Rightarrow> (outputs list) spmf"
  where "protocol_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 \<leftarrow> coin_spmf;
    S1 \<leftarrow> coin_spmf;
    S2 \<leftarrow> coin_spmf;
    S3 \<leftarrow> coin_spmf;
    S4 \<leftarrow> coin_spmf;
    S5 \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m00;
    let a1 = S0 \<oplus> S3 \<oplus> m01;
    let a2 = S1 \<oplus> S4 \<oplus> m10;
    let a3 = S1 \<oplus> S5 \<oplus> m11;
    outputs_i :: outputs list \<leftarrow> protocol_ot12 [M2 (S0, S1), C1 c0];
    outputs_j :: outputs list \<leftarrow> protocol_ot12 [M2 (S2, S3), C1 c1];
    outputs_k :: outputs list \<leftarrow> protocol_ot12 [M2 (S4, S5), C1 c1];
    let s2 = (xor (nth outputs_i 1) (if c0 then (nth outputs_k 1) else (nth outputs_j 1))) \<oplus> (if c0 then (if c1 then a3 else a2) else (if c1 then a1 else a0)) ;
    return_spmf ([U (), P s2])}"

(*lemma lossless_protocol_14_OT: "lossless_spmf (protocol_14_OT M C)" 
  by(simp add: protocol_14_OT_def lossless_protocol_OT12 split_def)*)

fun R1_14 :: "inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
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
    return_spmf (M4 (m00, m01, m10, m11), (S0, S1, S2, S3, S4, S5), a, b, c)}"

(*lemma lossless_R1_14: "lossless_spmf (R1_14 msgs C)"
  by(simp add: R1_14_def split_def lossless_R1_12)*)

fun R1_14_interm1 :: "inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
  where "R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U ()); 
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf (M4 (m00, m01, m10, m11), (S0, S1, S2, S3, S4, S5), a, b, c)}"

(*lemma lossless_R1_14_interm1: "lossless_spmf (R1_14_interm1 msgs C)"
  by(simp add: R1_14_interm1_def split_def lossless_R1_12 lossless_S1_12)*)

fun R1_14_interm2 :: "inputs_ot14 list \<Rightarrow> 'ot12_view1 view1 spmf"
  where "R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U ()); 
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2, S3)) (U ());
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    return_spmf (M4 (m00, m01, m10, m11), (S0, S1, S2, S3, S4, S5), a, b, c)}"

(*lemma lossless_R1_14_interm2: "lossless_spmf (R1_14_interm2 msgs C)"
  by(simp add: R1_14_interm2_def split_def lossless_R1_12 lossless_S1_12)*)

fun S1_14 :: "inputs_ot14 \<Rightarrow> outputs \<Rightarrow> 'ot12_view1 view1 spmf"
  where "S1_14 (M4 (m00, m01, m10, m11)) (U ()) = do {   
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S0, S1)) (U ()); 
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2, S3)) (U ());
    c :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S4, S5)) (U ());
    return_spmf (M4 (m00, m01, m10, m11), (S0, S1, S2, S3, S4, S5), a, b, c)}"

(*lemma lossless_S1_14: "lossless_spmf (S1_14 m out)"
  by(simp add: S1_14_def lossless_S1_12)*)

lemma reduction_step1: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
              \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
  including monad_normalisation
proof-
  define A1' where "A1' == \<lambda> (view :: 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    b :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S2, S3), C1 c1];
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    let R = (M4 (m00, m01, m10, m11), (m0,m1, S2, S3, S4, S5), view, b, c);
    D1 R}"
  have "\<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
    by(simp add: pair_spmf_alt_def A1'_def Let_def split_def) 
  then show ?thesis by auto
qed

lemma reduction_step1':
  shows " \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> 
                        \<le> ot12_adv_P1"
  (is "?lhs \<le> ot12_adv_P1")
proof-
  have int1: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>x. spmf (case x of (m0, m1) \<Rightarrow> R1_OT12 [M2 (m0, m1), C1 c0] \<bind> (\<lambda>view. A1 view (m0, m1))) True)" 
    and int2: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>x. spmf (case x of (m0, m1) \<Rightarrow> S1_OT12 (M2 (m0, m1)) (U ()) \<bind> (\<lambda>view. A1 view (m0, m1))) True)" 
    by(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)+
  have "?lhs = 
            \<bar>LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). spmf (case x of (m0, m1) \<Rightarrow> R1_OT12 [M2 (m0, m1), C1 c0] \<bind> (\<lambda>view. A1 view (m0, m1))) True 
              - spmf (case x of (m0, m1) \<Rightarrow> S1_OT12 (M2 (m0, m1)) (U ()) \<bind> (\<lambda>view. A1 view (m0, m1))) True\<bar>"
    apply(subst (1 2) spmf_bind) using int1 int2 by auto
  also have "... \<le> LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
               \<bar>spmf (R1_OT12 [M2 x, C1 c0] \<bind> (\<lambda>view. A1 view x)) True - spmf (S1_OT12 (M2 x) (U ()) \<bind> (\<lambda>view. A1 view x)) True\<bar>"
    by(rule integral_abs_bound[THEN order_trans]; simp add: split_beta)
  ultimately have "?lhs \<le> LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                      \<bar>spmf (R1_OT12 [M2 x, C1 c0] \<bind> (\<lambda>view. A1 view x)) True - spmf (S1_OT12 (M2 x) (U ()) \<bind> (\<lambda>view. A1 view x)) True\<bar>"
    by simp
  also have "LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                \<bar>spmf (R1_OT12 [M2 x, C1 c0] \<bind> (\<lambda>view. A1 view x)) True 
                    - spmf (S1_OT12 (M2 x) (U ()) \<bind> (\<lambda>view. A1 view x)) True\<bar> \<le> ot12_adv_P1"
    apply(rule integral_mono[THEN order_trans])
       apply(rule measure_spmf.integrable_const_bound[where B=2])
        apply clarsimp
        apply(rule abs_triangle_ineq4[THEN order_trans])
    subgoal for m0 m1
      using pmf_le_1[of "R1_OT12 [M2 (m0, m1), C1 c0] \<bind> (\<lambda>view. A1 view (m0, m1))" "Some True"]
        pmf_le_1[of "S1_OT12 (M2 (m0, m1)) (U ()) \<bind> (\<lambda>view. A1 view (m0, m1))" "Some True"]
      by simp
       apply simp
      apply(rule measure_spmf.integrable_const)
     apply clarify
     apply(rule OT_12_P1_assms_bound'[rule_format]) 
    by simp
  ultimately show ?thesis by simp
qed

lemma reduction_step2: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1 view (m0,m1))))) True -
            spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
proof-
  define A1' where "A1' == \<lambda> (view :: 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2,S3)) (U ());
    c :: 'ot12_view1 \<leftarrow> R1_OT12 [M2 (S4, S5), C1 c1];
    let R = (M4 (m00, m01, m10, m11), (S2,S3, m0, m1, S4, S5), a, view, c);
    D1 R}"
  have "\<bar>spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding  A1'_def Let_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by(simp)
    also have "(bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) =  (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding A1'_def Let_def split_def
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
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1 view (m0,m1))))) True -
            spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
proof-
  define A1' where "A1' == \<lambda> (view :: 'ot12_view1) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S2,S3)) (U ());
    b :: 'ot12_view1 \<leftarrow> S1_OT12 (M2 (S4, S5)) (U ());
    let R = (M4 (m00, m01, m10, m11), (S2,S3, S4, S5,m0, m1), a, b, view);
    D1 R}"
  have "\<bar>spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) 
            = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding A1'_def Let_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by(simp)
    also have "(bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) 
                = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding Let_def A1'_def split_def
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

lemma reduction_P1_interm: 
  shows "\<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) True\<bar> \<le> 3 * ot12_adv_P1"
    (is "?lhs \<le> ?rhs")
proof-
  have lhs: "?lhs \<le> \<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> + 
                     \<bar>spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> +
                      \<bar>spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) True\<bar>"
    by simp
  obtain A1 where A1: "\<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> =
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
    using reduction_step1 by blast
  obtain A2 where A2: "\<bar>spmf (bind_spmf (R1_14_interm1 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True\<bar> = 
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar>"
    using reduction_step2 by blast
  obtain A3 where A3: "\<bar>spmf (bind_spmf (R1_14_interm2 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D1) True - spmf (bind_spmf (S1_14 (M4 (m00, m01, m10, m11)) (U ())) D1) True\<bar> =
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using reduction_step3 by blast
  have lhs_bound: "?lhs \<le> \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> + 
                   \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                    spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar> +
                     \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
                      spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using A1 A2 A3 lhs by argo
  have bound1: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c0]) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> 
                      \<le> ot12_adv_P1" 
    and bound2: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A2 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A2 view (m0,m1))))) True\<bar> 
                      \<le> ot12_adv_P1" 
    and bound3: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 [M2 (m0,m1), C1 c1]) (\<lambda> view. (A3 view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (M2 (m0,m1)) (U ())) (\<lambda> view. (A3 view (m0,m1))))) True\<bar> \<le> ot12_adv_P1"
    using reduction_step1' by auto
  thus ?thesis
    using reduction_step1' lhs_bound by argo  
qed

lemma reduction_P1: "\<bar>spmf (bind_spmf (R1_14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) D) True 
                        - spmf (f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] \<bind> (\<lambda> outputs. S1_14 (M4 (m00, m01, m10, m11)) (nth outputs 0) \<bind> (\<lambda> view. D view))) True\<bar> 
                              \<le> 3 * ot12_adv_P1"
  using reduction_P1_interm by simp

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

fun R2_14:: "inputs_ot14 list \<Rightarrow> 'ot12_view2 view2 spmf"
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
    return_spmf (C2 (c0,c1), (a0,a1,a2,a3), a,b,c)}"

fun S2_14 :: "inputs_ot14 \<Rightarrow> outputs \<Rightarrow> 'ot12_view2 view2 spmf"
  where "S2_14 (C2 (c0,c1)) (P out) = do {
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c0) (if c0 then (P S1) else (P S0));
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c1) (if c1 then (P S3) else (P S2));
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 c1) (if c1 then (P S5) else (P S4));
    return_spmf (C2 (c0,c1), (a0',a1',a2',a3'), a,b,c)}"

lemma P2_OT_14_FT:
  shows "R2_14 [M4 (m0,m1,m2,m3), C2 (False, True)]  
              = f_ot14 [M4 (m0,m1,m2,m3), C2 (False, True)] \<bind> (\<lambda> outputs. S2_14 (C2 (False,True)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "R2_14 [M4 (m0,m1,m2,m3), C2 (False, True)] =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2\<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2\<leftarrow> S2_OT12 (C1 True) (P S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def OT_12_P2_assm)
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
    return_spmf (C2 (False,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: bind_spmf_const)
qed

lemma P2_OT_14_TT: "R2_14 [M4 (m0,m1,m2,m3), C2 (True,True)] = f_ot14 [M4 (m0,m1,m2,m3), C2 (True,True)] \<bind> (\<lambda> outputs. S2_14 (C2 (True,True)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "R2_14 [M4 (m0,m1,m2,m3), C2 (True,True)] =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def OT_12_P2_assm Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S3);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S5);
    return_spmf (C2 (True,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    by(simp add: bind_spmf_const)
qed

lemma P2_OT_14_FF: "R2_14 [M4 (m0,m1,m2,m3), C2 (False, False)] = f_ot14 [M4 (m0,m1,m2,m3), C2 (False, False)] \<bind> (\<lambda> outputs. S2_14 (C2 (False, False)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "R2_14 [M4 (m0,m1,m2,m3), C2 (False, False)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def OT_12_P2_assm Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S0); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
    return_spmf (C2 (False,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: bind_spmf_const)
qed

lemma P2_OT_14_TF: "R2_14 [M4 (m0,m1,m2,m3), C2 (True,False)] = f_ot14 [M4 (m0,m1,m2,m3), C2 (True,False)] \<bind> (\<lambda> outputs. S2_14 (C2 (True,False)) (nth outputs 1))"
  including monad_normalisation
proof-
  have "R2_14 [M4 (m0,m1,m2,m3), C2 (True,False)] = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    apply(simp add: OT_12_P2_assm Let_def)
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
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
    a :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 True) (P S1); 
    b :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S2);
    c :: 'ot12_view2 \<leftarrow> S2_OT12 (C1 False) (P S4);
    return_spmf (C2 (True,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    by(simp add: bind_spmf_const)
qed

lemma perfect_security_P2: 
  shows "R2_14 [M4 (m0,m1,m2,m3), C2 (c0,c1)] = f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)] \<bind> (\<lambda> outputs. S2_14 (C2 (c0,c1)) (nth outputs 1))"
  apply(cases c0; cases c1)
  using P2_OT_14_FF P2_OT_14_TF P2_OT_14_FT P2_OT_14_TT by auto

sublocale ot14_P1: semi_honest_det_security 0 f_ot14 R1_14 S1_14 valid_inputs_ot14 .

lemma ot14_secuirty_P1: "ot14_P1.advantage [M4 (m0,m1,m2,m3), C2 (c0,c1)] D \<le> 3 * ot12_adv_P1"
  unfolding ot14_P1.advantage_def   
  using reduction_P1 by simp

sublocale ot14_P2: semi_honest_det_security 1 f_ot14 R2_14 S2_14 valid_inputs_ot14 .

lemma ot14_security_P2: "ot14_P2.perfect_security [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  unfolding ot14_P2.perfect_security_def
  using perfect_security_P2 by simp

sublocale ot14_correct: semi_honest_det_correctness f_ot14 protocol_ot14 valid_inputs_ot14 .

lemma ot12_correct_unfold: "protocol_ot12 [M2 (S0, S1), C1 a] = f_ot12 [M2 (S0, S1), C1 a]" for a
  using ot12_correct[unfolded ot12.correctness_def] valid_inputs_ot12.simps by presburger

lemma ot14_correct_unfold: 
  shows "f_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)] = protocol_ot14 [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
proof-
  have "(S1 = (\<not> S5)) = (S1 = (S5 = (\<not> m))) = m" for S1 S5 m by blast
  thus ?thesis 
    by(auto simp add: ot12_correct_unfold bind_spmf_const ot12_correct)
qed

lemma ot14_correct: "ot14_correct.correctness [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  unfolding ot14_correct.correctness_def
  using ot14_correct_unfold by simp

end

locale OT_14_asymp =
  fixes R1_OT12 :: "nat \<Rightarrow> inputs_ot12 list \<Rightarrow> 'ot12_view1 spmf"
    and S1_OT12 :: "nat \<Rightarrow> inputs_ot12 \<Rightarrow> outputs \<Rightarrow> 'ot12_view1 spmf"
    and R2_OT12 :: "nat \<Rightarrow> inputs_ot12 list \<Rightarrow> 'ot12_view2 spmf"
    and S2_OT12 :: "nat \<Rightarrow> inputs_ot12 \<Rightarrow> outputs \<Rightarrow> 'ot12_view2 spmf"
    and protocol_ot12 :: "nat \<Rightarrow> inputs_ot12 list \<Rightarrow> outputs list spmf"
    and ot12_adv_P1 :: "nat \<Rightarrow> real"
  assumes ot14_base: "\<And> (n::nat).ot14_base (R1_OT12 n) (S1_OT12 n) (R2_OT12 n) (S2_OT12 n) (protocol_ot12 n) (ot12_adv_P1 n)"
begin 

sublocale ot14_base "(R1_OT12 n)" "(S1_OT12 n)" "(R2_OT12 n)" "(S2_OT12 n)" "(protocol_ot12 n)" "(ot12_adv_P1 n)" 
  using local.ot14_base by simp

lemma bound_P1: "ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D \<le> 3 * (ot12_adv_P1 n)"
  by(rule ot14_secuirty_P1) 

theorem OT_14_P1_asym_sec: "negligible (\<lambda> n. ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D)" if "negligible (\<lambda> n. ot12_adv_P1 n)"
proof-
  have adv_neg: "negligible (\<lambda>n. 3 * ot12_adv_P1 n)" using that negligible_cmultI by simp
  have "\<bar>ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D\<bar> \<le> \<bar>3 * (ot12_adv_P1 n)\<bar>" for n 
  proof -
    have "\<bar>ot14_P1.advantage n [M4 (m0,m1,m2,m3), C2 (c0,c1)] D\<bar> \<le> 3 * ot12_adv_P1 n"
      using ot14_P1.advantage_def ot14_base.ot14_secuirty_P1 ot14_base_axioms bound_P1 by auto
    then show ?thesis
      by (meson abs_ge_self order_trans)
  qed
  thus ?thesis using bound_P1 negligible_le adv_neg 
    by (metis (no_types, lifting) negligible_absI)
qed

theorem ot14_: "ot14_P2.perfect_security n [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  by(rule ot14_security_P2)

theorem ot14_correct: "ot14_correct.correctness n [M4 (m0,m1,m2,m3), C2 (c0,c1)]"
  by(rule ot14_correct)

end

end