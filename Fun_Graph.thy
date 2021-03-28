theory Fun_Graph
  imports "Perm" "Graph_Theory.Graph_Theory"
begin

text \<open>Permutations and funpow\<close>
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

text \<open>Digraph extras\<close>
lemma reachable1:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "a \<in> verts G" "b \<in> verts G"
  shows "a\<rightarrow>\<^sup>*\<^bsub>G\<^esub>b"
  by (metis assms reachable_def rtrancl_on.simps)

text \<open>Pair digraph of a function\<close>

definition Gr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a pair_pre_digraph" where
"Gr S f = \<lparr>pverts = S, parcs = {(a, f a) | a. a \<in> S}\<rparr>"

lemma Gr_eq: "a\<rightarrow>\<^bsub>Gr S f\<^esub> b \<longleftrightarrow> a \<in> S \<and> f a = b"
  unfolding Gr_def by auto

lemma funpow_in_rtrancl:
  assumes "a \<in> S" "\<forall> x \<in> S. f x \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S f\<^esub>(f ^^ n) a"
proof (induct n)
  let ?G = "Gr S f"
  case 0
  then show ?case using assms by (simp add: Fun_Graph.Gr_def reachable_def)
next
  case (Suc n)
  then show ?case
    by (smt (verit, del_insts) assms Gr_eq Fun_Graph.Gr_def funpow_simp_l pair_pre_digraph.simps(1)
        reachable_def rtrancl_on.simps with_proj_simps(1))
qed

locale perm_on =
  fixes p :: "'a perm" and S :: "'a set"
  assumes permutes_p: "p permutes S" and finite_S: "finite S"
begin

interpretation pair_wf_digraph "Gr S p"
  by (simp add: Fun_Graph.Gr_def pair_wf_digraph_def permutes_p permutes_in_image)

lemma reach_iff_funpow:
  assumes "a \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>b \<longleftrightarrow> (\<exists>n. (((\<langle>$\<rangle>) p) ^^ n) a = b)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
  proof (induct rule: reachable_induct)
    case base
    then show ?case by (meson funpow_0)
  next
    case (step x y)
    then obtain n where "(((\<langle>$\<rangle>) p) ^^ n) a = x" by auto
    also have "p x = y" by (metis Gr_eq step.hyps(2) with_proj_simps(3))
    ultimately show ?case by (metis funpow_simp_l)
  qed
next
  assume *: ?R
  then obtain n where "((\<langle>$\<rangle>) p ^^ n) a = b" by auto
  then show ?L using assms funpow_in_rtrancl
    by (metis (no_types, lifting) Fun_Graph.Gr_def Gr_eq in_arcsD2 pair_pre_digraph.simps(1) with_proj_simps(3))
qed

lemma perm_cycles_iff_reach:
  assumes "x \<noteq> y"
  shows "y \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y" (is "?L \<longleftrightarrow> ?R")
proof
  assume *: ?L
  then obtain n where "(apply_perm p ^^ n) y = x"
     using cycles_funpow by fast
   then show ?R
     by (smt (verit, del_insts) * perm_on.permutes_p perm_on_axioms reach_iff_funpow Permutations.permutes_not_in
        apply_perm_power funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff 
        set_cycle_ex_funpow start_in_perm_orbit_iff)
next
  assume *: ?R
  then obtain n where "(apply_perm p ^^ n) x = y"
    by (metis (no_types, lifting) Fun_Graph.Gr_def reach_iff_funpow pair_pre_digraph.simps(1) reachable_in_verts(1))
  then show ?L
    by (metis assms funpow_apply_perm_in_perm_orbit_iff id_funpow_id start_in_perm_orbit_iff)
qed

lemma perm_reach_sym: "x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>x"
proof (induct rule: reachable_induct)
case base
  then show ?case by simp
next
  let ?G = "Gr S p"
  case (step x y)
  then have "y \<rightarrow>\<^sup>*\<^bsub>?G\<^esub> x"
    by (smt (verit, best) Fun_Graph.Gr_def adj_in_verts(2) apply_perm_power funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff pair_pre_digraph.simps(1) perm_cycles_iff_reach reach_iff_funpow reachable_adjI reachable_in_verts(1) reachable_refl set_cycle_ex_funpow)
  then show ?case by (meson reachable_trans step.hyps(3))
qed

end
end