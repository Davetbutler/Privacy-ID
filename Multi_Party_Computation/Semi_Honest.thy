theory Semi_Honest imports
  CryptHOL.CryptHOL
begin

(*could abstractly define an extract function that gets the party's input from the input tuple*)

locale semi_honest_prob = 
  fixes i :: nat
    and funct :: "'input list \<Rightarrow> ('output list) spmf"
    and protocol :: "'input list \<Rightarrow> ('output list) spmf"
    and outputs :: "'input list \<Rightarrow> 'rand \<Rightarrow> ('output list) spmf"
    and randmoness :: "'rand spmf"
    and real_view_msgs :: "'input list \<Rightarrow> 'rand \<Rightarrow> 'view spmf" \<comment> \<open>the real view of the ith party\<close>
    and sim :: "'input \<Rightarrow> 'output \<Rightarrow> 'view spmf"
    and valid_inputs :: "'input list \<Rightarrow> bool"
begin

definition real_view :: "'input list \<Rightarrow> ('view \<times> 'output list) spmf"
  where "real_view inputs = do {
    rand \<leftarrow> randmoness;
    view \<leftarrow> real_view_msgs inputs rand;
    outputs :: 'output list \<leftarrow> outputs inputs rand;
    return_spmf (view, outputs)}"

definition ideal_view :: "'input list \<Rightarrow> ('view \<times> 'output list) spmf"
  where "ideal_view inputs = do {
   outputs :: 'output list \<leftarrow> funct inputs;
   view :: 'view \<leftarrow> sim (nth inputs i) (nth outputs i);
   return_spmf (view, outputs)}"

definition "perfect_security inputs \<equiv> (valid_inputs inputs \<longrightarrow> real_view inputs = ideal_view inputs)"

definition advantage :: "'input list \<Rightarrow> (('view \<times> 'output list) \<Rightarrow> bool spmf) \<Rightarrow> real"
  where "advantage inputs D \<equiv> \<bar>spmf (real_view inputs \<bind> D) True - spmf (ideal_view inputs \<bind> D) True\<bar>"

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
    and valid_inputs :: "'input list \<Rightarrow> bool" \<comment> \<open>D must be lossless, this is reasonable as the distinguisher is only used to define security, and is not an adversary\<close>
begin

definition advantage :: "'input list \<Rightarrow> ('view \<Rightarrow> bool spmf) \<Rightarrow> real"
  where "advantage inputs D \<equiv> \<bar>spmf (real_view inputs \<bind> D) True 
              - spmf (funct inputs \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i) \<bind> D)) True\<bar>"

definition "perfect_security inputs \<equiv> (valid_inputs inputs \<longrightarrow> real_view inputs = funct inputs \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i)))"

lemma 
  assumes "valid_inputs inputs"
    and "perfect_security inputs" 
  shows " advantage inputs = 0"
  unfolding advantage_def using assms
  by(auto simp add: perfect_security_def advantage_def assms)

end 

subsubsection \<open> Secret sharing schemes \<close>

locale secret_sharing_scheme = 
  fixes share :: "'input_out \<Rightarrow> ('share \<times> 'share) spmf"
    and reconstruct :: "('share \<times> 'share) \<Rightarrow> 'input_out spmf"
    and F :: "('input_out \<Rightarrow> 'input_out \<Rightarrow> 'input_out spmf) set"
begin

definition "sharing_correct input \<equiv> (share input \<bind> (\<lambda> (s1,s2). reconstruct (s1,s2)) = return_spmf input)"

definition "correct_share_eval input1 input2 \<equiv> (\<forall> gate_eval \<in> F. 
              \<exists> gate_protocol :: ('share \<times> 'share) \<Rightarrow> ('share \<times> 'share) \<Rightarrow> ('share \<times> 'share) spmf. 
                  share input1 \<bind> (\<lambda> (s1,s2). share input2 
                      \<bind> (\<lambda> (s3,s4). gate_protocol (s1,s3) (s2,s4) 
                          \<bind> (\<lambda> (S1,S2). reconstruct (S1,S2)))) = gate_eval input1 input2)"

end

end