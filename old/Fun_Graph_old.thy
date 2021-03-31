theory Fun_Graph
  imports "Perm" "Graph_Theory.Funpow"
begin

lemma cycles_funpow:
  assumes "z \<in> set_cycle (perm_orbit p x)"
  shows "\<exists>n. (apply_perm p ^^ n) z = x"
proof -
  from assms have "(apply_perm p ^^ n) z \<in> set_cycle (perm_orbit p x)" by simp
  also have "x \<in> set_cycle (perm_orbit p x)" using assms by fastforce
  ultimately show ?thesis
    by (metis apply_perm_power assms funpow_apply_cycle_perm_orbit set_cycle_ex_funpow)
qed

lemma funpow_cycles:
  assumes "(apply_perm p ^^ n) z = x" "z \<noteq> x"
  shows "z \<in> set_cycle (perm_orbit p x)"
proof (cases "n = 0")
  case True then show ?thesis using assms by auto
next
  case False then show ?thesis
    by (metis apply_inj_eq_iff apply_perm_power assms funpow_apply_perm_in_perm_orbit_iff
       id_funpow_id start_in_perm_orbit_iff)
qed

lemma set_perm_subset:
  assumes "(p :: 'a perm) permutes S"
  shows "set_perm p \<subseteq> S"
  by (meson permutes_not_in apply_perm_neq_idI assms subsetI)

text \<open>Graph of a function on a domain, and lemmas about its transitive closure\<close>

definition "Gr A f = {(a, f a) | a. a \<in> A}"

lemma Gr_eq: "(a,b) \<in> Gr A f \<longleftrightarrow> a \<in> A \<and> f a = b"
  unfolding Gr_def by auto

lemma funpow_in_trancl:
  assumes "a \<in> S" "\<forall> x \<in> S. f x \<in> S"
  shows "(a, (f ^^ (Suc n)) a) \<in> (Gr S f)\<^sup>+"
proof (induct n)
  case 0
  then show ?case by (simp add: Gr_eq assms(1) r_into_trancl')
next
  case (Suc n)
  then show ?case by (smt (verit, best) Gr_eq assms(2) funpow_simp_l trancl.simps)
qed

lemma perm_trancl_refl:
  assumes "x \<in> S" "p permutes S" "finite S"
  shows "(x,x) \<in> ((Gr S p)\<^sup>+)"
proof -
  from assms(2) have "bij_betw p S S" by (rule permutes_imp_bij)
  then have "\<exists>n\<in>{0<..card S}. (p ^^ n) x = x" by (metis inj_funpow_cycle_exists assms(1,3))
  then obtain n where "n > 0 \<and> (p ^^ n) x = x" by auto
  then show ?thesis
    by (metis funpow_in_trancl assms(1) assms(2) gr0_implies_Suc permutes_in_image)
qed

corollary perm_trancl_eq_rtrancl:
  assumes "x \<in> S" "p permutes S" "finite S"
  shows "(x,y) \<in> ((Gr S p)\<^sup>+) \<longleftrightarrow> (x,y) \<in> ((Gr S p)\<^sup>*)"
  by (metis assms perm_trancl_refl rtrancl_eq_or_trancl)

lemma Gr_trancl_imp_funpow: "(x,y) \<in> (Gr S p)\<^sup>+ \<longrightarrow> (\<exists>n>0. (p ^^ n) x = y)"
proof
  assume "(x,y) \<in> (Gr S p)\<^sup>+"
  then show "(\<exists>n>0. (p ^^ n) x = y)"
  proof (induct rule: trancl_induct)
    case (base y)
    then have "p x = y" by (metis Gr_eq)
    then show ?case by auto
  next
    case (step y z)
    then show ?case by (metis Gr_eq funpow_simp_l less_Suc_eq)
  qed
qed

lemma funpow_imp_Gr_trancl:
  assumes "p permutes S" "x \<noteq> y" "(p ^^ n) x = y" "n > 0"
  shows "(x,y) \<in> (Gr S p)\<^sup>+"
  by (metis (no_types, lifting) Permutations.permutes_not_in id_funpow_id gr0_implies_Suc
      permutes_in_image funpow_in_trancl assms)

corollary permutation_rel_funpow:
  assumes "p permutes S" "x \<noteq> y"
  shows "(x,y) \<in> (Gr S p)\<^sup>+ \<longleftrightarrow> (\<exists>n>0. (p ^^ n) x = y)"
  by (metis assms funpow_imp_Gr_trancl Gr_trancl_imp_funpow)

lemma perm_trancl_eq_cycles:
  assumes "x \<noteq> y" "(p :: 'a perm) permutes S"
  shows "y \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> (x,y) \<in> (Gr S p)\<^sup>+"
proof
  assume *: "y \<in> set_cycle (perm_orbit p x)"
  then obtain n where "n > 0 \<and> (apply_perm p ^^ n) y = x"
     by (metis cycles_funpow assms(1) funpow_0 gr0I)
  then show "(x,y) \<in> (Gr S p)\<^sup>+"
    by (smt (verit, del_insts) * assms funpow_in_trancl apply_perm_Perm Permutations.permutes_not_in
        apply_perm_power funpow_0 funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff 
        nat_neq_iff not_less0 permutation_rel_funpow set_cycle_ex_funpow start_in_perm_orbit_iff)
next
  assume *: "(x,y) \<in> (Gr S p)\<^sup>+"
  then obtain n where "n > 0 \<and> (apply_perm p ^^ n) y = x" using Gr_trancl_imp_funpow assms
    by (metis cycles_funpow funpow_0 funpow_apply_perm_in_perm_orbit_iff gr0I id_funpow_id start_in_perm_orbit_iff)
  then show "y \<in> set_cycle (perm_orbit p x)"
    by (metis assms(1) funpow_cycles)
qed

lemma perm_trancl_sym:
  assumes "(p :: 'a perm) permutes S"
  shows "sym ((Gr S p)\<^sup>+)"
  by (metis assms funpow_cycles perm_trancl_eq_cycles permutation_rel_funpow symI)

corollary perm_rtrancl_sym:
  assumes "(p :: 'a perm) permutes S"
  shows "sym ((Gr S p)\<^sup>*)"
  by (metis assms perm_trancl_sym rtrancl_trancl_reflcl sym_Id sym_Un)
end
