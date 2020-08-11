subsection \<open>1-out-of-4 OT to GMW\<close>

text\<open>We prove security for the gates of the GMW protocol in the semi honest model. We assume security on
1-out-of-4 OT.\<close>

theory GMW imports
  Semi_Honest
begin
(*TODO: secret sharing scheme stuff got taken out*)
datatype gmw_outputs = Q bool

datatype inputs_ot12 = M2 "(bool \<times> bool)" | C1 bool

datatype outputs_ot = P bool | U unit

fun K where "K (P x) = Q x"

fun xor :: "outputs_ot \<Rightarrow> outputs_ot \<Rightarrow> bool"
  where "xor (P a) (P b) = a \<oplus> b"

fun f_ot12 :: "inputs_ot12 list \<Rightarrow> (outputs_ot list)"
  where "f_ot12 [M2 (m0,m1), C1 \<sigma>] =  [U (), if \<sigma> then (P m1) else (P m0)]"

fun valid_inputs_ot12 :: "inputs_ot12 list \<Rightarrow> bool"
  where "valid_inputs_ot12 [M2 (b0, b1), C1 \<sigma>] = True" 

datatype inputs_ot14 = M4 "(bool \<times> bool \<times> bool \<times> bool)" | C2 "(bool \<times> bool)"

fun f_ot14 :: "inputs_ot14 list \<Rightarrow> (outputs_ot list)"
  where "f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] 
              = ([U (), if c0 then (if c1 then P (m11) else (P m10)) else (if c1 then (P m01) else (P m00))])"

fun valid_inputs_ot14 :: "inputs_ot14 list \<Rightarrow> bool"
  where "valid_inputs_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] = True" 

type_synonym share_1 = bool 
type_synonym share_2 = bool

type_synonym shares_1 = "bool list"
type_synonym shares_2 = "bool list"

type_synonym share_wire = "(share_1 \<times> share_2)"

type_synonym gmw_inputs = "share_wire"

type_synonym input1 = "bool \<times> bool \<times> bool \<times> bool"
type_synonym input2 = "bool \<times> bool"
type_synonym 'ot12_view1' view1 = "(inputs_ot14 \<times> (bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view1' \<times> 'ot12_view1' \<times> 'ot12_view1')"
type_synonym 'ot12_view2' view2 = "(inputs_ot14 \<times> (bool \<times> bool \<times> bool \<times> bool) \<times> 'ot12_view2' \<times> 'ot12_view2' \<times> 'ot12_view2')"

locale gmw =   ot14: semi_honest_det_correctness f_ot14 protocol_ot14 valid_inputs_ot14 
  + ot14_1: semi_honest_det_security f_ot14 protocol_ot14 valid_inputs_ot14 0 R1_OT14 S1_OT14 
  + ot14_2: semi_honest_det_security f_ot14 protocol_ot14 valid_inputs_ot14 1 R2_OT14 S2_OT14
  for R1_OT14 :: "inputs_ot14 list \<Rightarrow> 'ot14_view1 spmf"
    and S1_OT14 
    and R2_OT14 :: "inputs_ot14 list \<Rightarrow> 'ot14_view2 spmf"
    and  S2_OT14 protocol_ot14
    +
  fixes ot14_adv_P1 :: real
  assumes ot14_advantage_P1: "ot14_1.advantage [M4 (m00, m01, m10, m11), C2 (c0,c1)] D \<le> ot14_adv_P1"
    and ot14_perfect_security_P2: "ot14_2.perfect_security [M4 (m00, m01, m10, m11), C2 (c0,c1)]"
    and ot14_correct: "ot14.correctness [M4 (m00, m01, m10, m11), C2 (c0,c1)]"
begin

lemma ot14_correct_unfold: "\<forall> c0 c1 m00 m01 m10 m11. protocol_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] =  return_spmf (f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)])"
  using ot14_correct unfolding ot14.correctness_def by auto

lemma inf_th_14_OT_P4: "ot14_2.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)] = (return_spmf (f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) \<bind> (\<lambda> outputs_ot. ot14_2.ideal_view (C2 (c0,c1)) (nth outputs_ot 1)))" 
  using ot14_perfect_security_P2[unfolded ot14_2.perfect_security_def] by auto

lemma ass_adv_14_OT: "\<bar>spmf (bind_spmf (ot14_1.ideal_view (M4 (m00, m01, m10, m11)) (U())) (\<lambda> view. (D view))) True - 
                    spmf (bind_spmf (ot14_1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)]) (\<lambda> view. (D view))) True \<bar> \<le> ot14_adv_P1"
  using ot14_advantage_P1 unfolding ot14_1.advantage_def 
  by (simp add: abs_minus_commute)

(*proof-
  have "return_spmf (f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)]) \<bind> (\<lambda> outputs_ot. ot14_1.ideal_view (M4 (m00, m01, m10, m11)) (nth outputs_ot 0) \<bind> D) 
          = ot14_1.real_view [M4 (m00, m01, m10, m11), C2 (c0,c1)] \<bind> D" 
    unfolding ot14_1.real_view_def ot14_1.ideal_view_def 
  thus ?thesis 
    using ot14_advantage_P1[unfolded ot14_1.advantage_def, of m00 m01 m10 m11 c0 c1]

 unfolding ot14_1.real_view_def ot14_1.ideal_view_def 
    apply (auto simp add: abs_minus_commute) 
qed
*)

text \<open>The sharing scheme\<close>

definition share :: "bool \<Rightarrow> share_wire spmf"
  where "share x = do {
    a\<^sub>1 \<leftarrow> coin_spmf;
    let b\<^sub>1 = x \<oplus> a\<^sub>1;
    return_spmf (a\<^sub>1, b\<^sub>1)}" 

lemma lossless_share [simp]: "lossless_spmf (share x)" 
  by(simp add: share_def)

definition reconstruct :: "(share_1 \<times> share_2) \<Rightarrow> bool spmf"
  where "reconstruct shares = do {
    let (a,b) = shares;
    return_spmf (a \<oplus> b)}"

lemma lossless_reconstruct [simp]: "lossless_spmf (reconstruct s)" 
  by(simp add: reconstruct_def split_def)

lemma reconstruct_share : "(bind_spmf (share x) reconstruct) = (return_spmf x)"
proof-
  have "y = (y = x) = x" for y by auto
  thus ?thesis 
    by(auto simp add: share_def reconstruct_def bind_spmf_const eq_commute)  
qed

lemma "(reconstruct (s1,s2) \<bind> (\<lambda> rec. share rec \<bind> (\<lambda> shares. reconstruct shares))) = return_spmf (s1 \<oplus> s2)"
  apply(simp add: reconstruct_share reconstruct_def share_def)
  apply(cases s1; cases s2) by(auto simp add: bind_spmf_const)

definition xor_evaluate ::  "bool \<Rightarrow> bool \<Rightarrow> bool spmf"
  where "xor_evaluate A B = return_spmf (A \<oplus> B)"

fun xor_funct :: "share_wire list \<Rightarrow> bool list"
  where "xor_funct [A,B] = do {
    let (a1, b1) = A;
    let (a2, b2) = B;
    [a1 \<oplus> a2, b1 \<oplus> b2]}"

fun xor_protocol :: "share_wire list \<Rightarrow> bool list spmf"
  where "xor_protocol [A,B] = do {
    let (a1, b1) = A;
    let (a2, b2) = B;
    return_spmf ([a1 \<oplus> a2, b1 \<oplus> b2])}"

fun valid_inptuts_xor where "valid_inptuts_xor [(a1, b1),(a2,b2)] = True"

lemma share_xor_reconstruct: 
  shows "share x \<bind> (\<lambda> w1. share y \<bind> (\<lambda> w2. xor_protocol [w1, w2] 
              \<bind> (\<lambda> outputs. reconstruct (nth outputs 0, nth outputs 1)))) = xor_evaluate x y"
proof-
  have "(ya = (\<not> yb)) = ((x = (\<not> ya)) = (y = (\<not> yb))) = (x = (\<not> y))" for ya yb
    by auto
  then show ?thesis
    by(simp add: share_def reconstruct_def xor_evaluate_def bind_spmf_const)
qed

fun R1_xor :: "share_wire list \<Rightarrow> (bool \<times> bool) spmf"
  where "R1_xor [A, B] = return_spmf A"

definition S1_xor :: "share_wire \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
  where "S1_xor A out  = return_spmf A"

fun  R2_xor :: "share_wire list \<Rightarrow> (bool \<times> bool) spmf"
  where "R2_xor [A, B] = return_spmf B"

definition S2_xor :: "share_wire \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
  where "S2_xor B out  = return_spmf B"

lemma lossless_S2_xor: "lossless_spmf (S2_xor A out)" 
  by(simp add: S2_xor_def)

sublocale gmw_xor_correct: semi_honest_det_correctness xor_funct xor_protocol valid_inptuts_xor .

theorem correct_xor: "gmw_xor_correct.correctness [A,B]"
  unfolding gmw_xor_correct.correctness_def 
  by (simp add: split_def) 

sublocale gmw_xor_1: semi_honest_det_security xor_funct xor_protocol valid_inptuts_xor 0 R1_xor S1_xor .

sublocale gmw_xor_2: semi_honest_det_security xor_funct xor_protocol valid_inptuts_xor 1 R2_xor S2_xor .

lemma "gmw_xor_1.perfect_security [s1, s2]"
  using gmw_xor_1.perfect_security_def  
  by (simp add: S1_xor_def gmw_xor_1.ideal_view_def gmw_xor_1.real_view_def)

lemma "gmw_xor_2.perfect_security [s1, s2]"
  using gmw_xor_2.perfect_security_def[of "[s1, s2]"]
  by (auto simp add: split_def S2_xor_def gmw_xor_2.ideal_view_def gmw_xor_2.real_view_def semi_honest_det_security.real_view_def)

fun and_funct :: "share_wire list \<Rightarrow> (gmw_outputs list) spmf"
  where "and_funct [A, B] = do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    return_spmf ([Q \<sigma>, Q(\<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2)))])}"

fun valid_inputs_and where "valid_inputs_and [A, B] = True"

definition and_evaluate :: "bool \<Rightarrow> bool \<Rightarrow> bool spmf"
  where "and_evaluate A B  = return_spmf (A \<and> B)"

fun and_protocol :: "share_wire list \<Rightarrow> (gmw_outputs list) spmf"
  where "and_protocol [A, B] = do {
    let (a1, b1) = A;
    let (a2,b2) = B;
    \<sigma> :: bool \<leftarrow> coin_spmf;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (b1 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (b1 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (b1 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (b1 \<oplus> True)); 
    outputs :: outputs_ot list \<leftarrow> protocol_ot14 [M4 (s0,s1,s2,s3), C2 (a2,b2)];
    return_spmf ([Q \<sigma>, K (nth outputs 1)])}" 

lemma and_correct: "and_protocol [(a1, b1), (a2,b2)] = and_funct [(a1, b1), (a2,b2)]"
  apply(auto simp add: ot14_correct) 
  by(cases b2 ; cases b1; cases a1; cases a2; auto simp add:  ot14_correct_unfold) 

fun  and_R1 :: "gmw_inputs list \<Rightarrow> (( bool \<times> 'ot14_view1)) spmf"
  where "and_R1 [A, B] = do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V :: 'ot14_view1 \<leftarrow> R1_OT14 [M4 (s0,s1,s2,s3), C2 (b1,b2)];
    return_spmf ((\<sigma>, V))}"

fun and_outputs_1 :: "gmw_inputs list \<Rightarrow> (bool \<times> 'ot14_view1) \<Rightarrow> (gmw_outputs list) spmf"
  where "and_outputs_1 [A, B] view = do {
            let (\<sigma>, v) = view;
            let (a1, a2) = A;
            let (b1,b2) = B;
            let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
            let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
            let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
            let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
            outputs :: outputs_ot list \<leftarrow> protocol_ot14 [M4 (s0,s1,s2,s3), C2 (b1,b2)];
            return_spmf ([Q \<sigma>, K (nth outputs 1)])}" 
            (*let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
            let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
            let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
            let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); *)
fun and_outputs_2 :: "gmw_inputs list \<Rightarrow> ('ot14_view2 \<times> bool) \<Rightarrow> (gmw_outputs list) spmf"
  where "and_outputs_2 [A, B] view = do {
            let (v, s) = view;
            let (a1, a2) = A;
            let (b1,b2) = B;
            let \<sigma> = s \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2));
            return_spmf ([Q \<sigma>, Q s])}"

fun S1_and :: "gmw_inputs \<Rightarrow> gmw_outputs \<Rightarrow> ((bool \<times> 'ot14_view1)) spmf"
  where "S1_and A (Q \<sigma>) = do {
    let (a1,a2) = A;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V \<leftarrow> S1_OT14 (M4 (s0,s1,s2,s3)) (U ());
    return_spmf (\<sigma>, V)}"

sublocale gmw_and_1: semi_honest_prob 0 and_funct and_outputs_1 and_R1 S1_and valid_inputs_and  .

lemma sec_ex_P1_and: 
  shows "\<exists> (A :: (inputs_ot14 \<times> 'ot14_view1) \<Rightarrow> bool \<Rightarrow> bool spmf).
          \<bar>spmf ((gmw_and_1.real_view [(a1,a2),(b1,b2)]) \<bind> D) True - spmf ((gmw_and_1.ideal_view [(a1,a2),(b1,b2)] 
            \<bind> (D :: ((bool \<times> bool) \<times> (bool \<times> 'ot14_view1) \<times> gmw_outputs list) \<Rightarrow> bool spmf))) True\<bar> =
              \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma> :: bool. ot14_1.real_view [(M4 ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True))))), (C2 (b1, b2))] 
                    \<bind> (\<lambda> view. A view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.ideal_view (M4((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True))))) (U ()) 
                \<bind>  (\<lambda> view. A view \<sigma>))) True \<bar>"
  including monad_normalisation
proof-
  define A' :: "((inputs_ot14 \<times> 'ot14_view1)) \<Rightarrow> bool \<Rightarrow> bool spmf" 
    where "A' == \<lambda> (inputs, view) \<sigma>.  (D ((a1,a2), (\<sigma>, view), [Q \<sigma>, Q (\<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2)))]))" 
  have "\<bar>spmf ((gmw_and_1.real_view [(a1,a2),(b1,b2)]) \<bind> (D)) True - spmf ((gmw_and_1.ideal_view [(a1,a2),(b1,b2)]  
          \<bind> (D))) True\<bar> =
              \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.real_view [M4((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))), C2 (b1, b2)] 
                  \<bind> (\<lambda> view. A' view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.ideal_view ((M4 ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))))) (U ()) 
                \<bind>  (\<lambda> view. A' view \<sigma>))) True\<bar>"
    by(auto simp add: ot14_1.real_view_def ot14_1.ideal_view_def semi_honest_prob.ideal_view_def gmw_and_1.real_view_def  A'_def   Let_def split_def ot14_correct_unfold ; cases a1; cases a2; cases b1; cases b2; auto)
    then show ?thesis by auto
qed

lemma bound_14_OT:
  "\<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.real_view [M4 ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))), C2 (b1, b2)] 
              \<bind> (\<lambda> view. A view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.ideal_view (M4 ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True))))) (U ()) 
        \<bind>  (\<lambda> view. (A :: (inputs_ot14 \<times> 'ot14_view1) \<Rightarrow> bool \<Rightarrow> bool spmf) view \<sigma>))) True\<bar> \<le> ot14_adv_P1"
  (is "?lhs \<le> ot14_adv_P1")
proof-
  have int1: "integrable (measure_spmf coin_spmf) (\<lambda>x. spmf (ot14_1.ideal_view (M4 (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True))) (U ()) \<bind> (\<lambda>view. A view x)) True)"
    and int2: "integrable (measure_spmf coin_spmf) (\<lambda>x. spmf (ot14_1.real_view [M4 (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True)), C2 (b1, b2)] \<bind> (\<lambda>view. A view x)) True)"
    by(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)+
  have "?lhs = \<bar>LINT x|measure_spmf coin_spmf.
        spmf (ot14_1.ideal_view (M4 (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True))) (U ()) \<bind> (\<lambda>view. A view x)) True -
        spmf (ot14_1.real_view [(M4 (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True))), C2 (b1, b2)] \<bind> (\<lambda>view. A view x)) True\<bar>"
    apply(subst (1 2) spmf_bind) using int1 int2 by simp
  also have "... \<le> LINT x|measure_spmf coin_spmf. \<bar>spmf (ot14_1.ideal_view (M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2))) (U ()) \<bind> (\<lambda>view. A view x)) True 
                - spmf (ot14_1.real_view [M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)), C2 (b1, b2)] \<bind> (\<lambda>view. A view x)) True\<bar>"
    by(rule integral_abs_bound[THEN order_trans]; simp add: split_beta)
  ultimately have "?lhs \<le> LINT x|measure_spmf coin_spmf. \<bar>spmf (ot14_1.ideal_view (M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2))) (U ()) \<bind> (\<lambda>view. A view x)) True 
                - spmf (ot14_1.real_view [M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)), C2 (b1, b2)] \<bind> (\<lambda>view. A view x)) True\<bar>"
    by simp
  also have "LINT x|measure_spmf coin_spmf. \<bar>spmf (ot14_1.ideal_view (M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2))) (U ()) \<bind> (\<lambda>view. A view x)) True 
                - spmf (ot14_1.real_view [M4 (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)), C2 (b1, b2)] \<bind> (\<lambda>view. A view x)) True\<bar> \<le> ot14_adv_P1"
    apply(rule integral_mono[THEN order_trans]) 
       apply(rule measure_spmf.integrable_const_bound[where B=2])
        apply clarsimp
        apply(rule abs_triangle_ineq4[THEN order_trans])
        apply(cases a1) apply(cases a2) 
    subgoal for M
      using pmf_le_1[of "ot14_1.real_view [M4 (\<not> M, M, M, M), C2 (b1,b2)] \<bind>  (\<lambda> view. A view M)" "Some True"]
        pmf_le_1[of "ot14_1.ideal_view (M4 (\<not> M, M, M, M)) (U ()) \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by simp
    subgoal for M 
      using pmf_le_1[of "ot14_1.real_view [M4 (M, \<not> M, M, M), C2 (b1,b2)] \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "ot14_1.ideal_view (M4 (M, \<not> M, M, M)) (U ()) \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by simp
        apply(cases a2) apply(auto)
    subgoal for M
      using pmf_le_1[of "ot14_1.real_view [M4 (M, M, \<not> M, M), C2 (b1,b2)] \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "ot14_1.ideal_view (M4 (M, M, \<not> M, M)) (U ()) \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by(simp)
    subgoal for M
      using pmf_le_1[of "ot14_1.real_view [M4 (M, M, M, \<not> M), C2 (b1,b2)] \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "ot14_1.ideal_view (M4 (M, M, M, \<not> M)) (U ()) \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by(simp)
    using ass_adv_14_OT by fast
  ultimately show ?thesis by simp
qed

lemma and_advantage_P1:
  shows "gmw_and_1.advantage [(a1,a2),(b1,b2)] D \<le> ot14_adv_P1"
proof-
  obtain A :: "(inputs_ot14 \<times> 'ot14_view1) \<Rightarrow> bool \<Rightarrow> bool spmf" where "\<bar>spmf ((gmw_and_1.real_view [(a1,a2),(b1,b2)]) \<bind> D) True - spmf ((gmw_and_1.ideal_view [(a1,a2),(b1,b2)] 
            \<bind> (D :: ((bool \<times> bool) \<times> (bool \<times> 'ot14_view1) \<times> gmw_outputs list) \<Rightarrow> bool spmf))) True\<bar> =
              \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.real_view [(M4 ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True))))), (C2 (b1, b2))] 
                    \<bind> (\<lambda> view. A view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. ot14_1.ideal_view (M4((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True))))) (U ()) 
                \<bind>  (\<lambda> view. A view \<sigma>))) True\<bar>"
    using sec_ex_P1_and by blast 
  thus ?thesis 
  unfolding gmw_and_1.advantage_def gmw_and_1.real_view_def gmw_and_1.ideal_view_def using sec_ex_P1_and bound_14_OT by auto
qed

fun and_R2 :: "gmw_inputs list \<Rightarrow> ('ot14_view2 \<times> bool) spmf"
  where "and_R2 [A, B] = do {
    let (a1, a2) = A;
    let (c0,c1) = B;
    \<sigma> \<leftarrow> coin_spmf;
    let m00 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let m01 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let m10 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let m11 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V :: 'ot14_view2 \<leftarrow> R2_OT14 [M4 (m00,m01,m10,m11), C2 B];
    let s = (if c0 then (if c1 then (m11) else (m10)) else (if c1 then (m01) else (m00)));
    return_spmf (V, s)}"

fun S2_and :: "gmw_inputs \<Rightarrow> gmw_outputs \<Rightarrow> ('ot14_view2 \<times> bool) spmf"
  where "S2_and B (Q s2) =  do {
    let (b1,b2) = B;
    V :: 'ot14_view2 \<leftarrow> S2_OT14 (C2 B) (P s2);
    return_spmf (V, s2)}"

sublocale gmw_and_2: semi_honest_prob 1 and_funct and_outputs_2 and_R2 S2_and valid_inputs_and .

(*lemma 1: "valid_inputs_ot14 inputs \<longrightarrow> R2_OT14 [M4 (m00, m01, m10, m11), C2 (c0, c1)] 
              = return_spmf (f_ot14 [M4 (m00, m01, m10, m11), C2 (c0, c1)]) 
                  \<bind> (\<lambda> outputs. S2_OT14 (C2 (c0, c1)) (outputs ! 1))"
  using ot14_perfect_security_P2[of m00 m01 m10  m11 c0 c1] 
 using ot14_2.views_all[of "[M4 (m00, m01, m10, m11), C2 (c0, c1)]"] by auto 
*)

lemma "C2 (True, True) = (True, True)"

lemma 

"valid_inputs_ot14 [M4 (\<not> x, x, x, x), C2 (True, True)] \<longrightarrow>  R2_OT14 [M4 (\<not> x, x, x, x), C2 (True, True)] \<bind> (\<lambda>y :: 'ot14_view2 . return_spmf ((True, True), (y, x), [Q x, Q x])) =
         S2_OT14 (C2 (True, True)) (P x) \<bind> (\<lambda>y. return_spmf ((True, True), (y, x), [Q x, Q x]))"
  using ot14_perfect_security_P2[unfolded ot14_2.perfect_security_def ot14_2.ideal_view_def ot14_2.real_view_def, of "\<not> x" x x x True True]   apply auto apply(cases x) oops
lemma and_perfect_security_P2: 

  shows "gmw_and_2.perfect_security [(a1,a2),(b1,b2)]"
  unfolding gmw_and_2.perfect_security_def gmw_and_2.real_view_def gmw_and_2.ideal_view_def
using inf_th_14_OT_P4 apply auto 
  apply(auto simp add: Let_def split_def)

  using  ot14_perfect_security_P2 
  apply(cases b1;cases b2; cases a1; cases a2; auto)
                 apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
using ot14_correct_unfold inf_th_14_OT_P4 ot14_2.real_view_def ot14_2.ideal_view_def
  (*using 1*) apply auto using  ot14_perfect_security_P2[unfolded ot14_2.perfect_security_def ot14_2.ideal_view_def ot14_2.real_view_def] 
  subgoal for x using ot14_perfect_security_P2[unfolded ot14_2.perfect_security_def ot14_2.ideal_view_def ot14_2.real_view_def, of "\<not> x" x x x True True]
apply auto apply(cases x) 



  using ot14_correct_unfold inf_th_14_OT_P4 
  apply(simp only:  ot14_2.real_view_def  ot14_2.ideal_view_def) 
  apply(auto simp add: split_def Let_def)
  apply(cases b1;cases b2; cases a1; cases a2; auto)
 
                 apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
  using inf_th_14_OT_P4[unfolded ot14_2.real_view_def ot14_2.ideal_view_def] 
end 

locale gmw_asym = 
  fixes R1_OT14 :: "nat \<Rightarrow> inputs_ot14 list \<Rightarrow> 'ot14_view1 spmf"
    and S1_OT14 :: "nat \<Rightarrow> inputs_ot14 \<Rightarrow> outputs_ot \<Rightarrow> 'ot14_view1 spmf"
    and R2_OT14 :: "nat \<Rightarrow> inputs_ot14 list \<Rightarrow> 'ot14_view2 spmf"
    and S2_OT14 :: "nat \<Rightarrow> inputs_ot14 \<Rightarrow> outputs_ot \<Rightarrow> 'ot14_view2 spmf"
    and protocol_ot14 :: "nat \<Rightarrow> inputs_ot14 list \<Rightarrow> outputs_ot list spmf"
    and ot14_adv_P1 :: "nat \<Rightarrow> real"
  assumes gmw: "\<And> (n::nat). gmw (R1_OT14 n) (S1_OT14 n) (R2_OT14 n) (S2_OT14 n) (protocol_ot14 n) (ot14_adv_P1 n)"
begin 

sublocale gmw "(R1_OT14 n)" "(S1_OT14 n)" "(R2_OT14 n)" "(S2_OT14 n)" "(protocol_ot14 n)" "(ot14_adv_P1 n)"
  by (simp add: gmw)

lemma "gmw_xor_1.perfect_security [s1, s2]"
  using gmw_xor_1.perfect_security_def by(simp add: split_def S1_xor_def)

lemma "gmw_xor_2.perfect_security [s1, s2]"
  using gmw_xor_2.perfect_security_def by(simp add: split_def S2_xor_def)

lemma and_advantage_P1:
  assumes "negligible (\<lambda> n. ot14_adv_P1 n)"
  shows "negligible (\<lambda>n.  gmw_and_1.advantage n [(a1,a2),(b1,b2)] D)"
proof-
  have "gmw_and_1.advantage n [(a1,a2),(b1,b2)] D \<le> ot14_adv_P1 n" 
    for n 
    by (simp add: and_advantage_P1)
  thus ?thesis 
    using assms gmw_and_1.advantage_def negligible_le by auto
qed

lemma "gmw_and_2.perfect_security n [(a1,a2),(b1,b2)]"
  by(rule and_perfect_security_P2)

lemma "gmw_and_1.correctness n [(a1, b1), (a2,b2)]"
  unfolding gmw_and_1.correctness_def
  using and_correct by simp

end

end


