theory Semi_Honest imports
  CryptHOL.CryptHOL
begin

locale semi_honest_det_correctness = 
  fixes funct :: "'input list \<Rightarrow> 'output list"
    and protocol :: "'input list \<Rightarrow> 'output list spmf"
    and valid_inputs :: "'input list \<Rightarrow> bool"
begin

definition "correctness inputs \<equiv> (valid_inputs inputs \<longrightarrow> return_spmf (funct inputs) = protocol inputs)"

end 

locale semi_honest_det_security = protocol: semi_honest_det_correctness funct protocol valid_inputs
  for funct :: "'input list \<Rightarrow> 'output list"
    and protocol :: "'input list \<Rightarrow> 'output list spmf"
    and valid_inputs :: "'input list \<Rightarrow> bool" 
    +
  fixes i :: nat
    and R :: "'input list \<Rightarrow> 'view spmf" 
    \<comment> \<open>the randomness and messages of the ith party, the real view without the inputs appended to start\<close>
    and S :: "'input \<Rightarrow> 'output \<Rightarrow> 'view spmf"
    \<comment> \<open>the randomness and messages of the ith party conostructed by the simulator\<close>
begin

definition real_view :: "'input list \<Rightarrow> ('input \<times> 'view) spmf"
  where "real_view inputs = do {
            view \<leftarrow> R inputs;
            return_spmf (inputs ! i, view)}"

definition ideal_view :: "'input \<Rightarrow> 'output \<Rightarrow> ('input \<times> 'view) spmf"
  where "ideal_view input out = do {
          view \<leftarrow> S input out;
          return_spmf (input, view)}"

sublocale protocol: semi_honest_det_correctness funct protocol valid_inputs .

definition advantage :: "'input list \<Rightarrow> (('input \<times> 'view) \<Rightarrow> bool spmf) \<Rightarrow> real"
  where "advantage inputs D \<equiv> \<bar>spmf (real_view inputs \<bind> D) True 
              - spmf (return_spmf (funct inputs) \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i) \<bind> D)) True\<bar>"

definition "perfect_security inputs \<equiv> 
                (valid_inputs inputs \<longrightarrow> real_view inputs 
                    = return_spmf (funct inputs) \<bind> (\<lambda> outputs. ideal_view (nth inputs i) (nth outputs i)))"

lemma " R inputs \<bind> (\<lambda> view. return_spmf view) = S (inputs ! i) (funct inputs ! i) \<bind> (\<lambda> view. return_spmf view)
\<longleftrightarrow>  R inputs = S (inputs ! i) (funct inputs ! i)"

lemma assumes "A = B" shows "spmf A X  = spmf B X" using assms by simp

lemma 1:  fixes inputs
  assumes 
"R inputs \<bind> (\<lambda>view :: 'view. return_spmf (inputs ! i, view)) = S (inputs ! i) (funct inputs ! i) \<bind> (\<lambda>view. return_spmf (inputs ! i, view))"
shows   "R inputs = S (input ! i) (funct inputs ! i)"
  using assms oops

(*proof(rule ccontr)
  assume "\<not> (R inputs = S (input ! i) (funct inputs ! i))"
  hence "x \<in> set_spmf (R inputs) \<longrightarrow> x \<notin> set_spmf (S (input ! i) (funct inputs ! i))" for x 
  hence  "spmf (R inputs) X \<noteq> spmf (S (input ! i) (funct inputs ! i)) X" for  X 
  hence "\<not> (R inputs \<bind> (\<lambda>view :: 'view. return_spmf (view)) = S (inputs ! i) (funct inputs ! i) \<bind> (\<lambda>view. return_spmf (view)))"

  then show "False" using assms 
qed
*)


(*lemma views: shows "perfect_security inputs \<longrightarrow> valid_inputs inputs \<longrightarrow> R inputs  
                      = return_spmf (funct inputs) \<bind> (\<lambda>  outputs. S (input ! i) (outputs ! i))"
  unfolding perfect_security_def ideal_view_def real_view_def apply auto using  1 by blast
*)
(*lemma views_all: shows "\<forall> inputs. perfect_security inputs \<longrightarrow> valid_inputs inputs \<longrightarrow> R inputs \<bind> (\<lambda> view. return_s  = return_spmf (funct inputs) \<bind> (\<lambda>  outputs. S (input ! i) (outputs ! i))"
  using views by blast*)
lemma perfect_security_imp_advanage_0:
  assumes "valid_inputs inputs"
    and "perfect_security inputs" 
  shows "advantage inputs = 0"
  unfolding advantage_def using assms
  by(auto simp add: perfect_security_def advantage_def assms)

end 

locale semi_honest_prob = 
  fixes i :: nat
    and funct :: "'input list \<Rightarrow> ('output list) spmf"
    and outputs :: "'input list \<Rightarrow> 'view \<Rightarrow> ('output list) spmf"
    and R :: "'input list \<Rightarrow> 'view spmf"
    \<comment> \<open>the randomness and messages of the ith party, the real view without the inputs appended to start\<close>
    and S :: "'input \<Rightarrow> 'output \<Rightarrow> 'view spmf"
    \<comment> \<open>the randomness and messages of the ith party conostructed by the simulator\<close>
    and valid_inputs :: "'input list \<Rightarrow> bool"
begin

definition real_view :: "'input list \<Rightarrow> ('input \<times> 'view \<times> 'output list) spmf"
  where "real_view inputs = do {
    view \<leftarrow> R inputs;
    outputs :: 'output list \<leftarrow> outputs inputs view;
    return_spmf (inputs ! i, view, outputs)}"

definition ideal_view :: "'input list \<Rightarrow> ('input \<times> 'view \<times> 'output list) spmf"
  where "ideal_view inputs = do {
   outputs :: 'output list \<leftarrow> funct inputs;
   view  \<leftarrow> S (nth inputs i) (nth outputs i);
   return_spmf (inputs ! i, view, outputs)}"

definition "perfect_security inputs \<equiv> (valid_inputs inputs \<longrightarrow> real_view inputs = ideal_view inputs)"

definition advantage :: "'input list \<Rightarrow> (('input \<times> 'view \<times> 'output list) \<Rightarrow> bool spmf) \<Rightarrow> real"
  where "advantage inputs D \<equiv> \<bar>spmf (real_view inputs \<bind> D) True - spmf (ideal_view inputs \<bind> D) True\<bar>"

end 

locale semi_honest_det_imp_non_det = 
  det_protocol_correctness: semi_honest_det_correctness funct protocol valid_inputs +
  det_protocol_security: semi_honest_det_security funct protocol valid_inputs i real_view ideal_view
  for funct :: "'input list \<Rightarrow> 'output list"
    and protocol :: "'input list \<Rightarrow> 'output list spmf"
    and valid_inputs :: "'input list \<Rightarrow> bool" 
    and i :: nat
    and real_view :: "'input list \<Rightarrow> 'view spmf" 
    and ideal_view :: "'input \<Rightarrow> 'output \<Rightarrow> 'view spmf"
    +
  assumes correct: "det_protocol_correctness.correctness inputs"
begin

definition funct_non_det :: "'input list \<Rightarrow> 'output list spmf"
  where "funct_non_det inputs = return_spmf (funct inputs)"

definition outputs :: "'input list \<Rightarrow> 'a \<Rightarrow> 'output list spmf"
  where "outputs inputs view = protocol inputs"

sublocale semi_honest_prob: semi_honest_prob i funct_non_det outputs real_view ideal_view valid_inputs .

lemma correct_sym: "valid_inputs inputs \<longrightarrow> protocol inputs = return_spmf (funct inputs)"
  using correct[unfolded det_protocol_correctness.correctness_def] by simp

(*quote Lindell, p8 (How to simulate it) 
"observe that the distinguisher is given the indices x,y [inputs] of the ensemble and so can compute f(x,y) by itself"*)

definition adversary :: "'input list \<Rightarrow> ('input \<times> 'view \<times> 'output list \<Rightarrow> bool spmf) \<Rightarrow> ('input \<times> 'view) \<Rightarrow> bool spmf"
  where 
    "adversary inputs D view = do {
      let (input,  v) = view;
      D (input, v, funct inputs)}"

lemma det_secure_imp_non_det_secure:
  fixes inputs
  assumes "valid_inputs inputs"
  shows "det_protocol_security.advantage inputs (adversary inputs D) = semi_honest_prob.advantage inputs D"
  unfolding semi_honest_prob.advantage_def det_protocol_security.advantage_def semi_honest_prob.real_view_def 
            semi_honest_prob.ideal_view_def funct_non_det_def outputs_def det_protocol_security.real_view_def 
            det_protocol_security.ideal_view_def adversary_def
  using correct_sym[of inputs] assms by auto 

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