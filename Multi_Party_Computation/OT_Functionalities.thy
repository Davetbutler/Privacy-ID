subsection \<open>Oblivious Transfer functionalities\<close> 

text\<open>Here we define the functionalities for 1-out-of-2 and 1-out-of-4 OT.\<close>

theory OT_Functionalities imports
  CryptHOL.CryptHOL
begin


definition f_ot12 :: "(('a \<times> 'a) \<times> bool) \<Rightarrow> (unit \<times> 'a) spmf"
  where "f_ot12 inputs = return_spmf ((), if (snd inputs) then (snd (fst inputs)) else (fst (fst inputs)))"

lemma "f_ot12 ((m0,m1), \<sigma>) = return_spmf ((), if \<sigma> then m1 else m0)" 
  by(simp add: f_ot12_def)

lemma lossless_funct_OT_12: "lossless_spmf (f_ot12 ((m0,m1), \<sigma>))"
  by(simp add: f_ot12_def)

definition f_ot14 :: "(('a \<times> 'a \<times> 'a \<times> 'a) \<times> (bool \<times> bool)) \<Rightarrow> (unit \<times> 'a) spmf"
  where "f_ot14 inputs = do {
    let ((m00, m01, m10, m11), (c0,c1)) = inputs;
    return_spmf ((),if c0 then (if c1 then m11 else m10) else (if c1 then m01 else m00))}"

lemma lossless_funct_14_OT: "lossless_spmf (f_ot14 ((m00, m01, m10, m11), (c0,c1)))"
  by(simp add: f_ot14_def Let_def split_def)

end