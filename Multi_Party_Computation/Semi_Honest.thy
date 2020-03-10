theory Semi_Honest imports
  CryptHOL.CryptHOL
begin

(*could abstractly define an extract function that gets the party's input from the input tuple*)

locale semi_honest_prob = 
  fixes funct :: "'inputs \<Rightarrow> 'outputs spmf"
    and protocol :: "'inputs \<Rightarrow> 'outputs spmf"
    and real_view_msgs :: "'inputs \<Rightarrow> 'view spmf" \<comment> \<open>the real view of the ith party\<close>
    and sim :: "'ith_input \<Rightarrow> 'ith_output \<Rightarrow> 'view spmf"
    and valid_inputs :: "'inputs \<Rightarrow> bool"
    and extract_input :: "'inputs \<Rightarrow> 'ith_input"
    and extract_output :: "'outputs \<Rightarrow> 'ith_output"
    and D :: "'view \<Rightarrow> bool spmf" \<comment> \<open>the distinguisher that tries to distinguish the real and ideal views\<close>
  assumes "lossless_spmf (D view)" \<comment> \<open>D must be lossless, this is reasonable as the distinguisher is only used to define security, and is not an adversary\<close>
begin

definition real_view :: "'inputs \<Rightarrow> ('view \<times> 'outputs) spmf"
  where "real_view inputs = do {
    outputs :: 'outputs \<leftarrow> protocol inputs;
    view \<leftarrow> real_view_msgs inputs;
    return_spmf (view, outputs)}"

definition ideal_view :: "'inputs \<Rightarrow> ('view \<times> 'outputs) spmf"
  where "ideal_view inputs = do {
   outputs :: 'outputs \<leftarrow> funct inputs;
   view :: 'view \<leftarrow> sim (extract_input inputs) (extract_output outputs);
   return_spmf (view, outputs)}"

definition "perfect_security inputs \<equiv> (valid_inputs inputs \<longrightarrow> real_view inputs = ideal_view inputs)"

definition "correctness inputs \<equiv> (valid_inputs inputs \<longrightarrow> funct inputs = protocol inputs)"

end 

locale semi_honest_det_correctness = 
  fixes funct :: "'inputs \<Rightarrow> 'outputs spmf"
    and protocol :: "'inputs \<Rightarrow> 'outputs spmf"
    and valid_inputs :: "'inputs \<Rightarrow> bool"
begin

definition "correctness inputs \<equiv> (valid_inputs inputs \<longrightarrow> funct inputs = protocol inputs)"

end 

locale semi_honest_det_security = 
  fixes i :: nat
  fixes funct :: "'input list \<Rightarrow> ('output list) spmf"
    and real_view :: "'input list \<Rightarrow> 'view spmf" \<comment> \<open>the real view of the ith party\<close>
    and ideal_view :: "'input \<Rightarrow> 'output \<Rightarrow> 'view spmf"
    and valid_inputs :: "'input list \<Rightarrow> bool"
    and D :: "'view \<Rightarrow> bool spmf" \<comment> \<open>the distinguisher that tries to distinguish the real and ideal views\<close>
  assumes "lossless_spmf (D view)" \<comment> \<open>D must be lossless, this is reasonable as the distinguisher is only used to define security, and is not an adversary\<close>
begin

definition advantage :: "'input list \<Rightarrow> real"
  where "advantage inputs \<equiv> \<bar>spmf (real_view inputs \<bind> D) True 
              - spmf (funct inputs \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i) \<bind> D)) True\<bar>"

definition "perfect_security inputs \<equiv> (valid_inputs inputs \<longrightarrow> real_view inputs = funct inputs \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i)))"

lemma 
  assumes "valid_inputs inputs"
    and "perfect_security inputs" 
  shows " advantage inputs = 0"
  unfolding advantage_def using assms
  by(auto simp add: perfect_security_def advantage_def assms)

end 

end