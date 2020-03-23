subsection \<open> Oblivious transfer constructed from ETPs \<close>

text\<open>Here we construct the OT protocol based on ETPs given in \cite{DBLP:books/sp/17/Lindell17} (Chapter 4) and prove
semi honest security for both parties. We show information theoretic security for Party 1 and reduce the security of 
Party 2 to the HCP assumption.\<close>

theory ETP_OT imports
  "HOL-Number_Theory.Cong"
  ETP
  OT_Functionalities
  Semi_Honest
begin

fun valid_bool_inputs_ot12 :: "bool inputs_ot12 list \<Rightarrow> bool"
  where "valid_bool_inputs_ot12 [M2 (b0, b1), C1 \<sigma>] = True" 

type_synonym 'range viewP1 = "(bool inputs_ot12 \<times> 'range \<times> 'range) spmf"
type_synonym 'range dist1 = "(bool inputs_ot12 \<times> 'range \<times> 'range) \<Rightarrow> bool spmf"
type_synonym 'index viewP2 = "(bool inputs_ot12 \<times> 'index \<times> (bool \<times> bool)) spmf"
type_synonym 'index dist2 = "(bool inputs_ot12 \<times> 'index \<times> bool \<times> bool) \<Rightarrow> bool spmf"
type_synonym ('index, 'range) advP2 = "'index dist2 \<Rightarrow> 'index \<Rightarrow> bool inputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> 'range \<Rightarrow> bool spmf"

lemma if_False_True: "(if x then False else \<not> False) \<longleftrightarrow> (if x then False else True)"
  by simp

lemma if_then_True [simp]: "(if b then True else x) \<longleftrightarrow> (\<not> b \<longrightarrow> x)"
  by simp

lemma if_else_True [simp]: "(if b then x else True) \<longleftrightarrow> (b \<longrightarrow> x)"
  by simp

lemma inj_on_Not [simp]: "inj_on Not A"
  by(auto simp add: inj_on_def)

locale ETP_ot12_base = etp: etp I domain range F F\<^sub>i\<^sub>n\<^sub>v B
  for I :: "('index \<times> 'trap) spmf" \<comment> \<open>samples index and trapdoor\<close>
    and domain :: "'index \<Rightarrow> 'range set" 
    and range :: "'index \<Rightarrow> 'range set"
    and B :: "'index \<Rightarrow> 'range \<Rightarrow> bool" \<comment> \<open>hard core predicate\<close>
    and F :: "'index \<Rightarrow> 'range \<Rightarrow> 'range"
    and F\<^sub>i\<^sub>n\<^sub>v :: "'index \<Rightarrow> 'trap \<Rightarrow> 'range \<Rightarrow> 'range"
begin

text\<open>The probabilistic program that defines the protocol.\<close>

fun protocol :: "bool inputs_ot12 list \<Rightarrow> (bool outputs_ot12 list) spmf"
  where "protocol [M2 (b\<^sub>\<sigma>, b\<^sub>\<sigma>'), C1 \<sigma>] = do {  
    (\<alpha> :: 'index, \<tau> :: 'trap) \<leftarrow> I;
    x\<^sub>\<sigma> :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    let (y\<^sub>\<sigma> :: 'range) = F \<alpha> x\<^sub>\<sigma>;
    let (x\<^sub>\<sigma> :: 'range) = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
    let (x\<^sub>\<sigma>' :: 'range) = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let (\<beta>\<^sub>\<sigma> :: bool) = xor (B \<alpha> x\<^sub>\<sigma>) b\<^sub>\<sigma>;
    let (\<beta>\<^sub>\<sigma>' :: bool) = xor (B \<alpha> x\<^sub>\<sigma>') b\<^sub>\<sigma>';
    return_spmf ([U_ot12 (), if \<sigma> then (P_ot12 (xor (B \<alpha> x\<^sub>\<sigma>') \<beta>\<^sub>\<sigma>')) else (P_ot12 (xor (B \<alpha> x\<^sub>\<sigma>) \<beta>\<^sub>\<sigma>))])}"

lemma correctness: "protocol [M2 (m0,m1), C1 c] = f_ot12 [M2 (m0,m1), C1 c]"
proof-
  have "(B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = (B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = m1)) = m1" 
    for \<alpha> \<tau> y\<^sub>\<sigma>'  by auto
  then show ?thesis 
    by(auto simp add: Let_def etp.B_F_inv_rewrite bind_spmf_const etp.lossless_S local.etp.lossless_I lossless_weight_spmfD split_def cong: bind_spmf_cong)
qed

text \<open> Party 1 views \<close>

fun R1 :: "bool inputs_ot12 list \<Rightarrow> 'range viewP1"
  where "R1 [M2 (b\<^sub>0, b\<^sub>1), C1 \<sigma>] = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
    return_spmf (M2 (b\<^sub>0, b\<^sub>1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"

lemma lossless_R1: "lossless_spmf (R1 [M2 (b\<^sub>0, b\<^sub>1), C1 \<sigma>])"
  by(simp add: local.etp.lossless_I split_def etp.lossless_S Let_def)

fun S1 :: "bool inputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> 'range viewP1"
  where "S1 (M2 (b\<^sub>0, b\<^sub>1)) (U_ot12 ()) = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>0 :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>1 \<leftarrow> etp.S \<alpha>;
    return_spmf (M2 (b\<^sub>0, b\<^sub>1), y\<^sub>0, y\<^sub>1)}" 

lemma lossless_S1: "lossless_spmf (S1 (M2 (b\<^sub>0, b\<^sub>1)) (U_ot12 ()))"
  by(simp add: local.etp.lossless_I split_def etp.lossless_S)

text \<open> Party 2 views \<close>

fun R2 :: "bool inputs_ot12 list \<Rightarrow> 'index viewP2"
  where "R2 [M2 (b0, b1), C1 \<sigma>] = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
    let x\<^sub>\<sigma> = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
    let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> (if \<sigma> then b1 else b0);
    let \<beta>\<^sub>\<sigma>' = (B \<alpha> x\<^sub>\<sigma>') \<oplus> (if \<sigma> then b0 else b1);
    return_spmf (C1 \<sigma>, \<alpha>,(\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'))}"

lemma lossless_R2: "lossless_spmf (R2 [M2 (b0, b1), C1 \<sigma>])"
  by(simp add: Let_def split_def local.etp.lossless_I etp.lossless_S)

fun S2 :: "bool inputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> 'index viewP2"
  where "S2 (C1 \<sigma>) (P_ot12 b\<^sub>\<sigma>) = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = B \<alpha> x\<^sub>\<sigma>';
    return_spmf (C1 \<sigma>, \<alpha>, (\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'))}"

lemma lossless_S2: "lossless_spmf (S2 (C1 \<sigma>) (P_ot12 b\<^sub>\<sigma>))"
  by(simp add: local.etp.lossless_I etp.lossless_S split_def)

text \<open> Security for Party 1 \<close>

text\<open>We have information theoretic security for Party 1.\<close>

lemma P1_security: "R1 [M2 (b0, b1), C1 \<sigma>] = f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. S1 (nth [M2 (b0, b1), C1 \<sigma>] 0) (nth outputs_ot12 0))" 
  including monad_normalisation
proof-
  have "R1 [M2(b0, b1), C1 \<sigma>] =  do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma> \<leftarrow> map_spmf (\<lambda> x\<^sub>\<sigma>. F \<alpha> x\<^sub>\<sigma>) (etp.S \<alpha>);
    return_spmf (M2 (b0,b1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    return_spmf (M2 (b0,b1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"
    by(simp add: etp.uni_set_samp Let_def split_def cong: bind_spmf_cong)
  also have "... = f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12 :: bool outputs_ot12 list. S1 (M2 (b0,b1)) (U_ot12 (() :: unit)))"
    by(cases \<sigma>; simp add: Let_def) 
  ultimately show ?thesis by auto
qed 

text \<open> The adversary used in proof of security for party 2 \<close>

fun \<A> :: "('index, 'range) advP2"
  where "\<A> D' \<alpha> (C1 \<sigma>) (P_ot12 b\<^sub>\<sigma>) x = do {          
    \<beta>\<^sub>\<sigma>' \<leftarrow> coin_spmf;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    d \<leftarrow> D'(C1 \<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    return_spmf(if d then (\<beta>\<^sub>\<sigma>') else (\<not> \<beta>\<^sub>\<sigma>'))}"

lemma assm_bound_f_ot12: 
  assumes "etp.HCP_adv \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D \<le> HCP_ad"
  shows "\<bar>spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. 
              etp.HCP_game \<A> (C1 \<sigma>) (nth outputs_ot12 1) D)) True - 1/2\<bar> \<le> HCP_ad"
(is "?lhs \<le> HCP_ad")
proof-
  have "?lhs = \<bar>spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D) True - 1/2\<bar>" 
    by simp
  thus ?thesis 
    using assms
    by (simp add: local.etp.HCP_adv_def)+
qed

lemma assm_bound_f_ot12_collapse: 
  assumes "\<forall> b\<^sub>\<sigma>. etp.HCP_adv \<A> (C1 \<sigma>) (P_ot12 b\<^sub>\<sigma>) D \<le> HCP_ad"
  shows "\<bar>spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. etp.HCP_game \<A> (C1 \<sigma>) (nth outputs_ot12 1) D)) True - 1/2\<bar> \<le> HCP_ad"
proof -
  have "\<bar>spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda>zs. local.etp.HCP_game \<A> (C1 \<sigma>) (zs ! 1) D)) True - 1 / 2\<bar> \<le> HCP_ad \<or> local.etp.HCP_adv \<A> (C1 \<sigma>) (if \<sigma> then P_ot12 b1 else P_ot12 b0) D \<le> HCP_ad"
    using assms by presburger
  then show ?thesis
    using assm_bound_f_ot12 by blast
qed 

text \<open> To prove security for party 2 we split the proof on the cases on party 2's input \<close>

lemma R2_S2_False:
  assumes "((if \<sigma> then b0 else b1) = False)" 
  shows "spmf (R2 [M2 (b0, b1), C1 \<sigma>] \<bind> (D2::(bool inputs_ot12 \<times> 'index \<times> (bool \<times> bool)) \<Rightarrow> bool spmf)) True 
                = spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. S2 (C1 \<sigma>) (nth outputs_ot12 1) \<bind> D2)) True"
proof-
  have "\<sigma> \<Longrightarrow> \<not> b0" using assms by simp
  moreover have "\<not> \<sigma> \<Longrightarrow> \<not> b1" using assms by simp
  ultimately show ?thesis
    by(auto simp add: split_def local.etp.F_f_inv assms cong: bind_spmf_cong_simp) 
qed

lemma R2_S2_True:
  assumes "((if \<sigma> then b0 else b1) = True)" 
    and lossless_D2: "\<forall> view. lossless_spmf (D2 view)"
  shows "\<bar>(spmf (bind_spmf (R2 [M2 (b0, b1), C1 \<sigma>]) (D2::(bool inputs_ot12 \<times> 'index \<times> (bool \<times> bool)) \<Rightarrow> bool spmf)) True) 
                - spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda>outputs. S2 (C1 \<sigma>) (nth outputs 1) \<bind> (\<lambda> view. D2 view))) True\<bar>
                         = \<bar>2*((spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True) - 1/2)\<bar>"
proof-
  have  "(spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. S2 (C1 \<sigma>) (nth outputs_ot12 1) \<bind> D2)) True
              - spmf (bind_spmf (R2 [M2 (b0, b1), C1 \<sigma>]) D2) True) 
                    = 2 * ((spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True) - 1/2)"
  proof-
    have  "((spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True) - 1/2)  = 
                  1/2*(spmf (bind_spmf (S2 (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0))) D2) True
                        - spmf (bind_spmf (R2 [M2 (b0, b1), C1 \<sigma>]) D2) True)"
      including monad_normalisation
    proof- 
      have \<sigma>_true_b0_true: "\<sigma> \<Longrightarrow> b0 = True" using assms(1) by simp
      have \<sigma>_false_b1_true: "\<not> \<sigma> \<Longrightarrow> b1" using assms(1) by simp 
      have return_True_False: "spmf (return_spmf (\<not> d)) True = spmf (return_spmf d) False"
        for d by(cases d; simp)
      define HCP_game_true where "HCP_game_true == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      x \<leftarrow> (etp.S \<alpha>);
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x); 
      d \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      let b' = (if d then \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
      let b = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
      return_spmf (b = b')}"
      define HCP_game_false where "HCP_game_false == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      x \<leftarrow> (etp.S \<alpha>);
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x); 
      d \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      let b' = (if d then \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
      let b = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
      return_spmf (b = b')}"
      define HCP_game_\<A> where "HCP_game_\<A> == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
      \<beta>\<^sub>\<sigma>' \<leftarrow> coin_spmf;
      (\<alpha>, \<tau>) \<leftarrow> I;
      x \<leftarrow> etp.S \<alpha>;
      x' \<leftarrow> etp.S \<alpha>;
      d \<leftarrow> D2(\<sigma>, \<alpha>, (B \<alpha> x) \<oplus> b\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      let b' = (if d then  \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
      return_spmf (B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x') = b')}"
      define S2D where "S2D == \<lambda> \<sigma> b\<^sub>\<sigma> . do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
      let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = B \<alpha> x\<^sub>\<sigma>';
      d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      return_spmf d}"
      define R2D where "R2D == \<lambda> msgs \<sigma>.  do {
      let (b0,b1) = msgs;
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
      let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
      let x\<^sub>\<sigma> = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
      let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> (if \<sigma> then b1 else b0) ;
      let \<beta>\<^sub>\<sigma>' = (B \<alpha> x\<^sub>\<sigma>') \<oplus> (if \<sigma> then b0 else b1);
      b :: bool \<leftarrow> D2((C1 \<sigma>), \<alpha>,(\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'));
      return_spmf b}"
      define D_true where "D_true  == \<lambda>\<sigma> b\<^sub>\<sigma>. do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      x \<leftarrow> (etp.S \<alpha>);
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
      d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      return_spmf d}"
      define D_false where "D_false == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      x \<leftarrow> etp.S \<alpha>;
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
      d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      return_spmf d}"
      have lossless_D_false: "lossless_spmf (D_false a b)"
        for a b by(auto simp add: D_false_def lossless_D2 split_def etp.lossless_I etp.lossless_S)
      have "spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True =  spmf (HCP_game_\<A> (C1 \<sigma>) (if \<sigma> then b1 else b0)) True" 
        apply(simp add: etp.HCP_game_def HCP_game_\<A>_def split_def etp.F_f_inv)
        by(rewrite bind_commute_spmf[where q = "coin_spmf"]; rewrite bind_commute_spmf[where q = "coin_spmf"]; rewrite bind_commute_spmf[where q = "coin_spmf"]; auto)+
      also have "... = spmf (bind_spmf (map_spmf Not coin_spmf) (\<lambda>b. if b then HCP_game_true (C1 \<sigma>) (if \<sigma> then b1 else b0) else HCP_game_false (C1 \<sigma>) (if \<sigma> then b1 else b0))) True"
        unfolding HCP_game_\<A>_def HCP_game_true_def HCP_game_false_def Let_def
        apply(simp add: split_def cong: if_cong)
        supply [[simproc del: monad_normalisation]]
        apply(subst if_distrib[where f = "bind_spmf _" for f, symmetric]; simp cong: bind_spmf_cong add: if_distribR )+
        apply(rewrite in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(fold map_spmf_conv_bind_spmf)
        apply(rule conjI; rule impI; simp) 
         apply(simp only: spmf_bind)
         apply(rule Bochner_Integration.integral_cong[OF refl])+
         apply clarify
        subgoal for r r\<^sub>\<sigma> \<alpha> \<tau> 
          apply(simp only: UNIV_bool spmf_of_set integral_spmf_of_set) 
          apply(simp cong: if_cong split del: if_split)
          apply(cases "B r (F\<^sub>i\<^sub>n\<^sub>v r r\<^sub>\<sigma> \<tau>)") 
          by auto
        apply(rewrite in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(simp only: spmf_bind)
        apply(rule Bochner_Integration.integral_cong[OF refl])+
        apply clarify
        subgoal for r r\<^sub>\<sigma> \<alpha> \<tau> 
          apply(simp only: UNIV_bool spmf_of_set integral_spmf_of_set) 
          apply(simp cong: if_cong split del: if_split)
          apply(cases " B r (F\<^sub>i\<^sub>n\<^sub>v r r\<^sub>\<sigma> \<tau>)") 
          by auto
        done
      also have "... = 1/2*(spmf (HCP_game_true (C1 \<sigma>) (if \<sigma> then b1 else b0)) True) + 1/2*(spmf (HCP_game_false (C1 \<sigma>) (if \<sigma> then b1 else b0)) True)"
        by(simp add: spmf_bind UNIV_bool spmf_of_set integral_spmf_of_set)
      also have "... = 1/2*(spmf (D_true (C1 \<sigma>) (if \<sigma> then b1 else b0)) True) + 1/2*(spmf (D_false (C1 \<sigma>) (if \<sigma> then b1 else b0)) False)"   
      proof-
        have "spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2((C1 \<sigma>), \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)) \<bind> (\<lambda>d. return_spmf (\<not> d)))))) True 
                = spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2((C1 \<sigma>), \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)))))) False"
          (is "?lhs = ?rhs")
        proof-
          have "?lhs = spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2((C1 \<sigma>), \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)) \<bind> (\<lambda>d. return_spmf (d)))))) False"
            by(simp only: split_def return_True_False spmf_bind) 
          then show ?thesis by simp
        qed
        then show ?thesis  by(simp add: HCP_game_true_def HCP_game_false_def Let_def D_true_def D_false_def if_distrib[where f="(=) _"] cong: if_cong)   
      qed
      also have "... =  1/2*((spmf (D_true (C1 \<sigma>) (if \<sigma> then b1 else b0)) True) + (1 - spmf (D_false (C1 \<sigma>) (if \<sigma> then b1 else b0)) True))"
        by(simp add: spmf_False_conv_True lossless_D_false)
      also have "... = 1/2 + 1/2* (spmf (D_true (C1 \<sigma>) (if \<sigma> then b1 else b0)) True) - 1/2*(spmf (D_false (C1 \<sigma>) (if \<sigma> then b1 else b0)) True)" 
        by(simp)     
      also have "... =  1/2 + 1/2* (spmf (S2D (C1 \<sigma>) (if \<sigma> then b1 else b0)) True) - 1/2*(spmf (R2D (b0,b1) \<sigma> ) True)"
        apply(auto  simp add: local.etp.F_f_inv S2D_def R2D_def D_true_def D_false_def  assms split_def cong: bind_spmf_cong_simp)
         apply(simp add: \<sigma>_true_b0_true)
        by(simp add: \<sigma>_false_b1_true)
      ultimately show ?thesis by(simp add: S2D_def R2D_def split_def)
    qed
    then show ?thesis by auto 
  qed
  thus ?thesis by simp
qed

lemma P2_adv_bound_unfold:
  assumes lossless_D2: "\<forall> view. lossless_spmf (D2 view)"
  shows "\<bar>(spmf (bind_spmf (R2 [M2 (b0, b1), C1 \<sigma>]) D2) True) - spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. S2 (C1 \<sigma>) (nth outputs_ot12 1) \<bind> (\<lambda> view. D2 view))) True\<bar>
                         \<le> \<bar>2*((spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True) - 1/2)\<bar>"
  apply(cases "(if \<sigma> then (b0) else (b1))")
   apply(auto simp only: split_def R2_S2_False) 
  using R2_S2_True assms by simp

sublocale ot12_correct: semi_honest_det_correctness f_ot12 protocol valid_bool_inputs_ot12 .

sublocale ot12_party1: semi_honest_det_security protocol f_ot12 valid_bool_inputs_ot12 0 R1 S1 .

lemma perfect_security_P1: "ot12_party1.perfect_security [M2 (b0, b1), C1 \<sigma>]" 
  unfolding ot12_party1.perfect_security_def 
  using P1_security  by(auto simp add: P1_security Let_def) 

sublocale ot12_party2: semi_honest_det_security protocol f_ot12 valid_bool_inputs_ot12 1 R2 S2 .

lemma correct: "ot12_correct.correctness [M2 (b0, b1), C1 \<sigma>]"
  unfolding ot12_correct.correctness_def  
  using correctness by simp

lemma P2_adv_bound:
  assumes lossless_D2: "\<forall> view. lossless_spmf (D2 view)"
  shows "ot12_party2.advantage [M2 (b0, b1), C1 \<sigma>] D2 \<le> \<bar>2*((spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True) - 1/2)\<bar>"
  using P2_adv_bound_unfold assms unfolding ot12_party2.advantage_def 
  by(auto simp add: split_def)

lemma P2_security:
  assumes "etp.HCP_adv \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2 \<le> HCP_ad"
    and lossless_D2: "\<forall> view. lossless_spmf (D2 view)"
  shows "ot12_party2.advantage [M2 (b0, b1), C1 \<sigma>] D2 \<le> 2 * HCP_ad"
proof-
  have *: "\<bar>2 * (spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. etp.HCP_game \<A> (C1 \<sigma>) (nth outputs_ot12 1) D2)) True - 1/2)\<bar> 
                = \<bar>2 * (spmf (etp.HCP_game \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2) True - 1/2)\<bar>"
    by simp
  hence "ot12_party2.advantage [M2 (b0, b1), C1 \<sigma>] D2 \<le> \<bar>2*((spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. etp.HCP_game \<A> (C1 \<sigma>) (nth outputs_ot12 1) D2)) True) - 1/2)\<bar>"
    using P2_adv_bound assms by auto
  moreover with * have "\<bar>2*((spmf (f_ot12 [M2 (b0, b1), C1 \<sigma>] \<bind> (\<lambda> outputs_ot12. etp.HCP_game \<A> (C1 \<sigma>) (nth outputs_ot12 1) D2)) True) - 1/2)\<bar> \<le> \<bar>2*HCP_ad\<bar>" 
    using assms 
    by (simp add: local.etp.HCP_adv_def)+
  moreover have "HCP_ad \<ge> 0" 
    using assms by (simp add: local.etp.HCP_adv_def)+
  ultimately show ?thesis by argo
qed

end

text \<open> We also consider the asymptotic case for security proofs \<close>

locale ETP_sec_para = 
  fixes I :: "nat \<Rightarrow> ('index \<times> 'trap) spmf"
    and domain ::  "'index \<Rightarrow> 'range set"
    and range ::  "'index \<Rightarrow> 'range set"
    and F :: "'index \<Rightarrow> 'range \<Rightarrow> 'range"
    and F\<^sub>i\<^sub>n\<^sub>v :: "'index \<Rightarrow> 'trap \<Rightarrow> 'range \<Rightarrow> 'range"
    and B :: "'index \<Rightarrow> 'range \<Rightarrow> bool"
  assumes ETP_base: "\<And> n. ETP_ot12_base (I n) domain range F F\<^sub>i\<^sub>n\<^sub>v"
begin

sublocale ETP_ot12_base "(I n)" domain range 
  using ETP_base  by simp

lemma correct_asym: "ot12_correct.correctness n [M2 (b0, b1), C1 \<sigma>]"
  by(simp add: correct)

lemma P1_sec_asym: "ot12_party1.perfect_security n [M2 (b0, b1), C1 \<sigma>]"
  using perfect_security_P1 by simp                                                                

lemma P2_sec_asym: 
  assumes HCP_adv_neg: "negligible (\<lambda> n. etp_advantage n)"
    and etp_adv_bound: "\<forall> n. etp.HCP_adv n \<A> (C1 \<sigma>) (if \<sigma> then (P_ot12 b1) else (P_ot12 b0)) D2 \<le> etp_advantage n"
    and lossless_D2: "\<forall> view. lossless_spmf (D2 view)"
  shows "negligible (\<lambda> n. ot12_party2.advantage n [M2 (b0, b1), C1 \<sigma>] D2)" 
proof-
  have "negligible (\<lambda> n. 2 * etp_advantage n)" using HCP_adv_neg 
    by (simp add: negligible_cmultI)
  moreover have "\<bar>ot12_party2.advantage n [M2 (b0, b1), C1 \<sigma>] D2\<bar> = ot12_party2.advantage n [M2 (b0, b1), C1 \<sigma>] D2" 
    for n unfolding ot12_party2.advantage_def by simp
  moreover have  "ot12_party2.advantage n [M2 (b0, b1), C1 \<sigma>] D2 \<le> 2 * etp_advantage n"  
    for n
    using P2_security assms
    by blast
  ultimately show ?thesis 
    using assms negligible_le HCP_adv_neg P2_security by presburger
qed

end

end