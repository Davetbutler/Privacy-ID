theory OT12_Funct imports
Semi_Honest
begin
sledgehammer_params[timeout = 1000]
definition "ot12_funct1 M \<sigma> = return_spmf ((), if \<sigma> then (snd M) else (fst M))"

locale semi_honest_ot = 
ot12: semi_honest 1 ot12_funct1 protocol view sim valid_inputs 
for protocol :: "'b \<Rightarrow> (unit \<times> 'a) spmf"
    and view :: "'a \<times> 'a \<Rightarrow> bool \<Rightarrow> 'b spmf"
    and sim :: "'a \<times> 'a \<Rightarrow> unit \<Rightarrow> 'b spmf"
    and valid_inputs :: "'a \<times> 'a \<Rightarrow> bool \<Rightarrow> bool"
+
assumes perfect_sec: "ot12.perfect_security ith_input inputs"
begin

lemma view_unfold: 
  assumes "valid_inputs ith_input inputs"
  shows "ot12.real_view ith_input inputs = ot12.view' ith_input inputs"
  using perfect_sec ot12.perfect_security_def assms by blast 
term "protocol real_view"
lemma 
  assumes "valid_inputs M \<sigma>"
    and "real_view \<in> set_spmf (view M \<sigma>)"
  shows "protocol real_view = ot12_funct1 M \<sigma>"
  using assms view_unfold ot12.real_view_def ot12.view'_def ot12_funct1_def apply(simp add: split_def)