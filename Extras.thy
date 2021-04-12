theory Extras
    imports "Perm" "Graph_Theory.Graph_Theory"
begin

section \<open>Permutations and funpow\<close>
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

lemma permutes_perm:
  assumes "finite S" "f permutes S"
  shows "(Perm f) permutes S"
  by (metis (no_types, lifting) Perm_inverse assms mem_Collect_eq permutation permutation_permutes)

lemma size_perm_type_eq_card: "size (perm_type p) = card (cycles_of_perm p)"
  by (simp add: perm_type_def)

section \<open>Digraph extras\<close>
lemma reachable1:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "a \<in> verts G" "b \<in> verts G"
  shows "a\<rightarrow>\<^sup>*\<^bsub>G\<^esub>b"
  by (metis assms reachable_def rtrancl_on.simps)

lemma reach_sym_arc:
  assumes "a \<rightarrow>\<^sup>*\<^bsub>g\<^esub> b \<Longrightarrow> b \<rightarrow>\<^sup>*\<^bsub>g\<^esub> a" "wf_digraph g"
  shows "a \<rightarrow>\<^bsub>g\<^esub> b \<Longrightarrow> b \<rightarrow>\<^sup>*\<^bsub>g\<^esub> a"
  by (simp add: assms wf_digraph.reachable_adjI)

definition pair_union :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
"pair_union g h \<equiv> \<lparr> pverts = pverts g \<union> pverts h, parcs = parcs g \<union> parcs h\<rparr>"

lemma with_proj_union[simp]: "with_proj (pair_union g h) = union (with_proj g) (with_proj h)"
  by (simp add: pair_union_def)

lemma comm_pair_union: "pair_union g h = pair_union h g"
  unfolding pair_union_def by auto

lemma wf_pair_union:
  assumes "pair_wf_digraph g" "pair_wf_digraph h"
  shows "pair_wf_digraph (pair_union g h)"
  by (metis assms compatibleI_with_proj wellformed_union wf_digraph_wp_iff with_proj_union)

lemma pair_union_arcs_disj: "x\<rightarrow>\<^bsub>pair_union g h\<^esub>y \<longleftrightarrow> x\<rightarrow>\<^bsub>g\<^esub>y \<or> x\<rightarrow>\<^bsub>h\<^esub>y"
  by (simp add: pair_union_def)

lemma arc_in_union: "x\<rightarrow>\<^bsub>with_proj g\<^esub>y \<Longrightarrow> x\<rightarrow>\<^bsub>pair_union g h\<^esub>y"
  by (metis Un_iff arcs_union with_proj_simps(2) with_proj_simps(3) with_proj_union)

lemma reach_in_union:
  assumes "wf_digraph g" "wf_digraph h" "compatible g h" "x\<rightarrow>\<^sup>*\<^bsub>g\<^esub>y"
  shows "x\<rightarrow>\<^sup>*\<^bsub>union g h\<^esub>y"
by (meson assms pre_digraph.reachable_mono rtrancl_subset_rtrancl subgraphs_of_union(1))

definition reverse :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" ("(_\<^sup>R)" [1000] 999) where
"reverse a = \<lparr>pverts = pverts a, parcs = (parcs a)\<inverse>\<rparr>"

lemma wf_reverse: "pair_wf_digraph g \<Longrightarrow> pair_wf_digraph (g\<^sup>R)"
  unfolding reverse_def
  by (smt (verit, ccfv_SIG) converseE fst_swap pair_pre_digraph.select_convs(1)
      pair_pre_digraph.select_convs(2) pair_wf_digraph_def swap_simp)

lemma arc_reverse: "x\<rightarrow>\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def)

lemma reach_reverse: "x\<rightarrow>\<^sup>*\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def reachable_def rtrancl_on_converseI)

end

