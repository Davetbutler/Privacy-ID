theory OT_Functionalities imports 
  CryptHOL.CryptHOL
begin

datatype 'a' inputs_ot12 = M2 "('a' \<times> 'a')" | C1 bool

datatype 'a' outputs_ot12 = P_ot12 'a' | U_ot12 unit

fun f_ot12 :: "'a' inputs_ot12 list \<Rightarrow> ('a' outputs_ot12 list) spmf"
  where "f_ot12 [M2 (m0,m1), C1 \<sigma>] = return_spmf ([U_ot12 (), if \<sigma> then (P_ot12 m1) else (P_ot12 m0)])"

datatype 'a' inputs_ot14 = M4 "('a' \<times> 'a' \<times> 'a' \<times> 'a')" | C2 "(bool \<times> bool)"

datatype 'a' outputs_ot14 = P_ot14 'a' | U_ot14 unit

fun f_ot14 :: "'a' inputs_ot14 list \<Rightarrow> ('a' outputs_ot14 list) spmf"
  where "f_ot14 [M4 (m00, m01, m10, m11), C2 (c0,c1)] 
              = return_spmf ([U_ot14 (), if c0 then (if c1 then P_ot14 m11 else P_ot14 m10) else (if c1 then P_ot14 m01 else P_ot14 m00)])"

fun xor_ot12 :: "bool outputs_ot12 \<Rightarrow> bool outputs_ot12 \<Rightarrow> bool"
  where "xor_ot12 (P_ot12 a) (P_ot12 b) = a \<oplus> b"

fun output_ot_rev where "output_ot_rev (P_ot12 n) = n"

lemma f_ot12_if_unfold: "\<forall> a b x.(f_ot12 [M2 (if x then (a,b) else (b,a)), C1 x]) = return_spmf [U_ot12 (), P_ot12 b] "
  by simp

lemma f_ot12_if_unfold_neg: "\<forall> a b x.(f_ot12 [M2 (if (\<not> x) then (a,b) else (b,a)), C1 x]) = return_spmf [U_ot12 (), P_ot12 a] "
  by simp

end

