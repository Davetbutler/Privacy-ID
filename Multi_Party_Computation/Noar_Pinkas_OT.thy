subsection \<open>Noar Pinkas OT\<close>

text\<open>Here we prove security for the Noar Pinkas OT from \cite{DBLP:conf/soda/NaorP01}.\<close>

theory Noar_Pinkas_OT imports
  Cyclic_Group_Ext 
  Game_Based_Crypto.Diffie_Hellman
  OT_Functionalities 
  Semi_Honest 
  Uniform_Sampling 
begin

locale np_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes or_gt_0: "0 < order \<G>"
    and prime_order: "prime (order \<G>)"
begin

fun valid_inputs_np_ot12 where "valid_inputs_np_ot12 [M2 (m0,m1), C1 \<sigma>] = (m0 \<in> carrier \<G> \<and> m1 \<in> carrier \<G>)"

lemma prime_field: "a < (order \<G>) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a (order \<G>)"
  by(metis dvd_imp_le neq0_conv not_le prime_imp_coprime prime_order coprime_commute)

lemma weight_sample_uniform_units: "weight_spmf (sample_uniform_units (order \<G>)) = 1"
  using  lossless_spmf_def lossless_sample_uniform_units prime_order  prime_gt_1_nat by auto

fun protocol :: "'grp inputs_ot12 list \<Rightarrow> ('grp outputs_ot12 list) spmf"
  where "protocol [M2 (m0,m1), C1 \<sigma>] = do {
    a :: nat \<leftarrow> sample_uniform (order \<G>);
    b :: nat \<leftarrow> sample_uniform (order \<G>);
    let c\<^sub>v = (a*b) mod (order \<G>);
    c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
    r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
    let z0' = ((\<^bold>g [^] (if \<sigma> then c\<^sub>v' else c\<^sub>v)) [^] s0) \<otimes> ((\<^bold>g [^] b) [^] r0);
    r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
    let z1' = ((\<^bold>g [^] ((if \<sigma> then c\<^sub>v else c\<^sub>v'))) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
    let enc_m0 = z0' \<otimes> m0;
    let enc_m1 = z1' \<otimes> m1;
    let out_2 = (if \<sigma> then enc_m1 \<otimes> inv (w1 [^] b) else enc_m0 \<otimes> inv (w0 [^] b));
    return_spmf [U_ot12 (), P_ot12 out_2]}"

lemma lossless_protocol: "lossless_spmf (protocol [M2 (m0,m1), C1 \<sigma>])"
  apply(auto simp add: Let_def split_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

type_synonym 'grp' view1 = "(('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp')) spmf"

type_synonym 'grp' dist_adversary = "('grp' inputs_ot12 \<times> 'grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> bool spmf"

fun R1 :: "'grp inputs_ot12 list \<Rightarrow> 'grp view1"
  where "R1 [M2 (m0,m1), C1 \<sigma>] = do {
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);
    let c\<^sub>\<sigma> = a*b;
    c\<^sub>\<sigma>' \<leftarrow> sample_uniform (order \<G>);
    return_spmf ((\<^bold>g [^] a, \<^bold>g [^] b, (if \<sigma> then \<^bold>g [^] c\<^sub>\<sigma>' else \<^bold>g [^] c\<^sub>\<sigma>), (if \<sigma> then \<^bold>g [^] c\<^sub>\<sigma> else \<^bold>g [^] c\<^sub>\<sigma>')))}"  

lemma lossless_R1: "lossless_spmf (R1 [M2 (m0,m1), C1 \<sigma>])"
  by(simp add: Let_def lossless_sample_uniform_units or_gt_0)

fun inter :: "'grp inputs_ot12 \<Rightarrow> ('grp inputs_ot12 \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp)  spmf"
  where "inter (M2 (m0,m1)) = do {
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);  
    c \<leftarrow> sample_uniform (order \<G>);
    d \<leftarrow> sample_uniform (order \<G>);
    return_spmf (M2 (m0,m1), \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c, \<^bold>g [^] d)}"

fun S1 :: "'grp inputs_ot12 \<Rightarrow> 'grp outputs_ot12 \<Rightarrow> 'grp view1"
  where "S1 (M2 (m0,m1)) (U_ot12 ()) = do {
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);
    c \<leftarrow> sample_uniform (order \<G>);
    return_spmf ((\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c, \<^bold>g [^] (a*b)))}"  

lemma lossless_S1: "lossless_spmf (S1 (M2 (m0,m1)) (U_ot12 ()))"
  by(simp add: Let_def lossless_sample_uniform_units or_gt_0)

fun R1_inter_adversary :: "'grp dist_adversary \<Rightarrow> 'grp inputs_ot12 \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where "R1_inter_adversary \<A> msgs \<alpha> \<beta> \<gamma> = do {
    c \<leftarrow> sample_uniform (order \<G>);
    \<A> (msgs, \<alpha>, \<beta>, \<gamma>, \<^bold>g [^] c)}"

fun inter_S1_adversary :: "'grp dist_adversary \<Rightarrow>  'grp inputs_ot12 \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where "inter_S1_adversary \<A> msgs \<alpha> \<beta> \<gamma> = do {
    c \<leftarrow> sample_uniform (order \<G>);
    \<A> (msgs, \<alpha>, \<beta>, \<^bold>g [^] c, \<gamma>)}"

sublocale ddh: ddh \<G> .

fun R2 :: " 'grp inputs_ot12 list \<Rightarrow> ('grp \<times> 'grp \<times>  'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
  where "R2 [M2 (m0,m1), C1 \<sigma>]  = do {
  a :: nat \<leftarrow> sample_uniform (order \<G>);
  b :: nat \<leftarrow> sample_uniform (order \<G>);
  let c\<^sub>v = (a*b) mod (order \<G>);
  c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
  r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
  let z = ((\<^bold>g [^] c\<^sub>v') [^] s0) \<otimes> ((\<^bold>g [^] b) [^] r0);
  r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
  let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
  let enc_m = z \<otimes> (if \<sigma> then m0 else m1);
  let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
  return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 

lemma lossless_R2: "lossless_spmf (R2 [M2 (m0,m1), C1 \<sigma>])"
  apply(simp add: Let_def split_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

fun S2 :: "'grp inputs_ot12 \<Rightarrow> 'grp outputs_ot12 \<Rightarrow> ('grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
  where "S2 (C1 \<sigma>) (P_ot12 m) =  do {
  a :: nat \<leftarrow> sample_uniform (order \<G>);
  b :: nat \<leftarrow> sample_uniform (order \<G>);
  let c\<^sub>v = (a*b) mod (order \<G>);
  r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
  r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
  let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
  s' \<leftarrow> sample_uniform (order \<G>);
  let enc_m =  \<^bold>g [^] s';
  let enc_m' = z' \<otimes> m ;
  return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"

lemma lossless_S2: "lossless_spmf (S2 (C1 \<sigma>) (P_ot12 m))"
  apply(simp add: Let_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

sublocale np_correct: semi_honest_det_correctness f_ot12 protocol valid_inputs_np_ot12 .

sublocale np_P1: semi_honest_det_security f_ot12 protocol valid_inputs_np_ot12 0 R1 S1 .

sublocale np_P2: semi_honest_det_security f_ot12 protocol valid_inputs_np_ot12 1 R2 S2 .

end

locale np = np_base + cyclic_group \<G>
begin

lemma protocol_inverse: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>" 
  shows" ((\<^bold>g [^] ((a*b) mod (order \<G>))) [^] (s1 :: nat)) \<otimes> ((\<^bold>g [^] b) [^] (r1::nat)) \<otimes> (if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b) 
        = (if v then m0 else m1)"
(is "?lhs = ?rhs")
proof-
  have  1: "(a*b)*(s1) + b*r1 =((a::nat)*(s1) + r1)*b " using mult.commute mult.assoc  add_mult_distrib by auto
  have "?lhs = 
 ((\<^bold>g [^] (a*b)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1) \<otimes> (if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b)"
    by(simp add: pow_generator_mod)
  also have "... = (\<^bold>g [^] ((a*b)*(s1))) \<otimes> ((\<^bold>g [^] (b*r1))) \<otimes> ((if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] ((a*(s1) + r1)*b)))))"
    by(auto simp add: nat_pow_pow nat_pow_mult assms cyclic_group_assoc)
  also have "... = \<^bold>g [^] ((a*b)*(s1)) \<otimes> \<^bold>g [^] (b*r1) \<otimes> ((inv (((\<^bold>g [^] ((a*(s1) + r1)*b))))) \<otimes> (if v then m0 else m1))"
    by(simp add: nat_pow_mult cyclic_group_commute assms)
  also have "... = (\<^bold>g [^] ((a*b)*(s1) + b*r1) \<otimes> inv (((\<^bold>g [^] ((a*(s1) + r1)*b))))) \<otimes> (if v then m0 else m1)"
    by(simp add: nat_pow_mult cyclic_group_assoc assms)
  also have "... = (\<^bold>g [^] ((a*b)*(s1) + b*r1) \<otimes> inv (((\<^bold>g [^] (((a*b)*(s1) + r1*b)))))) \<otimes> (if v then m0 else m1)"
    using 1 by (simp add: mult.commute)
  ultimately show ?thesis
    using l_cancel_inv assms  by (simp add: mult.commute)
qed

lemma correctness: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>" 
  shows  "protocol [M2 (m0,m1), C1 \<sigma>] = return_spmf (f_ot12 [M2 (m0,m1), C1 \<sigma>])"
proof-
  have "protocol [M2 (m0,m1), C1 \<sigma>] = do {
    a :: nat \<leftarrow> sample_uniform (order \<G>);
    b :: nat \<leftarrow> sample_uniform (order \<G>);
    r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let out_2 = ((\<^bold>g [^] ((a*b) mod (order \<G>))) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1) \<otimes> (if \<sigma> then m1 else m0) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b);
    return_spmf [U_ot12 (), P_ot12 out_2]}"
    by(simp add: lossless_sample_uniform_units bind_spmf_const weight_sample_uniform_units or_gt_0)
  also have "... = do {   
    let out_2 = (if \<sigma> then m1 else m0);
    return_spmf [U_ot12 (), P_ot12 out_2]}"
    by(simp add: protocol_inverse assms lossless_sample_uniform_units bind_spmf_const weight_sample_uniform_units or_gt_0)
  ultimately show ?thesis by(simp add: Let_def)
qed

theorem correct_np: "np_correct.correctness [M2 (m0,m1), C1 \<sigma>]"
  unfolding np_correct.correctness_def using correctness by simp 

lemma security_P1: 
  shows "np_P1.advantage [M2 (m0,m1), C1 \<sigma>] D 
            \<le> ddh.advantage (R1_inter_adversary D (M2 (m0,m1))) 
                + ddh.advantage (inter_S1_adversary D (M2 (m0,m1)))"
    (is "?lhs \<le> ?rhs")
proof(cases \<sigma>)
  case True
  have "R1 [M2 (m0,m1), C1 \<sigma>] = S1 (M2 (m0,m1)) (U_ot12 ())" for out1
    by(simp add: True)
  then have "np_P1.advantage [M2 (m0,m1), C1 \<sigma>] D = 0"
    by(simp add: np_P1.advantage_def  Let_def np_P1.real_view_def np_P1.ideal_view_def) 
  also have "ddh.advantage A \<ge> 0" for A using ddh.advantage_def by simp 
  ultimately show ?thesis by simp 
next
  case False
  have bounded_advantage: "\<bar>(a :: real) - b\<bar> = e1 \<Longrightarrow> \<bar>b - c\<bar> = e2 \<Longrightarrow> \<bar>a - c\<bar> \<le> e1 + e2" 
    for a b e1 c e2 by simp
  also have R1_inter_dist: "\<bar>spmf (np_P1.real_view [M2 (m0,m1), C1 False] \<bind> D) True - spmf ((inter (M2 (m0,m1))) \<bind> D) True\<bar> = ddh.advantage (R1_inter_adversary D (M2 (m0,m1)))"
    unfolding ddh.advantage_def ddh.ddh_0_def ddh.ddh_1_def Let_def split_def np_P1.real_view_def by simp
  also  have inter_S1_dist: "\<bar>spmf ((inter (M2 (m0,m1))) \<bind> D) True - spmf (np_P1.ideal_view (M2 (m0,m1)) (U_ot12 ()) \<bind> D) True\<bar> = ddh.advantage (inter_S1_adversary D (M2 (m0,m1)))" 
    including monad_normalisation
    by(simp add: ddh.advantage_def ddh.ddh_0_def ddh.ddh_1_def np_P1.ideal_view_def) 
  ultimately have "\<bar>spmf (np_P1.real_view [M2 (m0,m1), C1 False] \<bind> (\<lambda>view. D view)) True - spmf (np_P1.ideal_view (M2 (m0,m1)) (U_ot12 ()) \<bind> (\<lambda>view. D view)) True\<bar> \<le> ?rhs"
    using R1_inter_dist by auto
  thus ?thesis by(simp add: np_P1.advantage_def False) 
qed

lemma add_mult_one_time_pad: 
  assumes "s0 < order \<G>" 
    and "s0 \<noteq> 0"
  shows "map_spmf (\<lambda> c\<^sub>v'. (((b* r0) + (s0 * c\<^sub>v')) mod(order \<G>))) (sample_uniform (order \<G>)) = sample_uniform (order \<G>)"
proof-
  have "gcd s0 (order \<G>) = 1" 
    using assms prime_field by simp
  thus ?thesis 
    using add_mult_one_time_pad by force
qed

lemma security_P2: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>"
  shows "R2 [M2 (m0,m1), C1 \<sigma>] = S2 (C1 \<sigma>) (if \<sigma> then (P_ot12 m1) else (P_ot12 m0))"
  including monad_normalisation
proof-
  have "R2 [M2 (m0,m1), C1 \<sigma>] = do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      let s' = (((b* r0) + ((c\<^sub>v')*(s0))) mod(order \<G>));
      let z = \<^bold>g [^] s' ;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 
    by(simp add: nat_pow_pow nat_pow_mult pow_generator_mod add.commute) 
  also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      s' \<leftarrow> map_spmf (\<lambda> c\<^sub>v'. (((b* r0) + ((c\<^sub>v')*(s0))) mod(order \<G>))) (sample_uniform (order \<G>));
      let z = \<^bold>g [^] s';
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      s' \<leftarrow>  (sample_uniform (order \<G>));
      let z = \<^bold>g [^] s';
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"  
    by(simp add: add_mult_one_time_pad Let_def mult.commute cong: bind_spmf_cong_simp)
  also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      enc_m \<leftarrow> map_spmf (\<lambda> s'.  \<^bold>g [^] s' \<otimes> (if \<sigma> then m0 else m1)) (sample_uniform (order \<G>)); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      enc_m \<leftarrow> map_spmf (\<lambda> s'.  \<^bold>g [^] s') (sample_uniform (order \<G>)); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"
    by(simp add: sample_uniform_one_time_pad assms)
  ultimately show ?thesis by(simp add: Let_def bind_map_spmf o_def)
qed

theorem np_perfect_security_P2:
  shows "np_P2.perfect_security [M2 (m0,m1), C1 \<sigma>]"
  unfolding np_P2.perfect_security_def np_P2.real_view_def np_P2.ideal_view_def using security_P2 by auto

end 

locale np_asymp = 
  fixes \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  assumes np: "\<And>\<eta>. np (\<G> \<eta>)"
begin
  
sublocale np "\<G> \<eta>" for \<eta> by(simp add: np)

theorem correctness_asymp: 
  shows "np_correct.correctness \<eta> [M2 (m0,m1), C1 \<sigma>]"
  by(rule correct_np) 

theorem security_P1_asymp: 
  assumes "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (inter_S1_adversary \<eta> D (M2 (m0,m1))))"
    and "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (R1_inter_adversary \<eta>  D (M2 (m0,m1))))"
  shows "negligible (\<lambda> \<eta>. np_P1.advantage \<eta> [M2 (m0,m1), C1 \<sigma>] D)"
proof-
  have "np_P1.advantage \<eta> [M2 (m0,m1), C1 \<sigma>] D \<le> ddh.advantage \<eta> (R1_inter_adversary \<eta>  D (M2 (m0,m1))) + ddh.advantage \<eta> (inter_S1_adversary \<eta> D (M2 (m0,m1)))" 
    for \<eta>
    using security_P1 by simp
  moreover have "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (R1_inter_adversary \<eta>  D (M2 (m0,m1))) + ddh.advantage \<eta> (inter_S1_adversary \<eta> D (M2 (m0,m1))))"
    using assms 
    by (simp add: negligible_plus)
  ultimately show ?thesis 
    using negligible_le np_P1.advantage_def by auto
qed

theorem np_perfect_security_asymp: 
  shows "np_P2.perfect_security \<eta> [M2 (m0,m1), C1 \<sigma>]"
  using np_perfect_security_P2 by simp

end

end