theory Extras
    imports "Perm" "Graph_Theory.Graph_Theory" "List-Index.List_Index"
begin

section \<open>Appears before\<close>

definition "appears_before l x y \<equiv> y \<in> set (drop (index l x) l)"

lemma appears_before_in:
  assumes "appears_before l x y"
  shows "x \<in> set l" "y \<in> set l"
   apply (metis appears_before_def assms in_set_dropD index_conv_size_if_notin last_index_drop
      last_index_less_size_conv)
  by (meson appears_before_def assms in_set_dropD)

lemma not_appears_before_fst: "x \<notin> set l  \<Longrightarrow> \<not> appears_before l x y"
  by (meson appears_before_in(1))

lemma not_appears_before_snd: "y \<notin> set l \<Longrightarrow> \<not> appears_before l x y"
  by (meson appears_before_in(2))

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

lemma permutes_perm:
  assumes "finite S" "f permutes S"
  shows "(Perm f) permutes S"
  by (metis (no_types, lifting) Perm_inverse assms mem_Collect_eq permutation permutation_permutes)

lemma size_perm_type_eq_card: "size (perm_type p) = card (cycles_of_perm p)"
  by (simp add: perm_type_def)

locale perm_on =
  fixes p :: "'a perm" and S :: "'a set"
  assumes permutes_p: "p permutes S" 
begin

lemma set_perm_subset:
  shows "set_perm p \<subseteq> S"
  by (meson permutes_not_in apply_perm_neq_idI permutes_p subsetI)

lemma count_cycles_on_eq_card:
 "count_cycles_on S p = card (cycles_of_perm p) + card (S - set_perm p)"
  unfolding count_cycles_on_def by (simp add: perm_type_on_def size_perm_type_eq_card)

lemma inverse_permutes: "(inverse p) permutes S"
  by (smt (verit, del_insts) apply_perm_inverse_not_in_set eq_apply_perm_inverse_iff
      perm.inverse_inverse permutes_def permutes_subset set_perm_subset)
end

locale finite_perm_on = perm_on +
  assumes finite_S: "finite S"
begin

lemma count_cycles_on_nonempty:
  assumes "S \<noteq> {}" shows "count_cycles_on S p \<noteq> 0"
  by (simp add: assms count_cycles_on_eq_card finite_S finite_cycles_of_perm)
end


section \<open>Digraph extras\<close>

lemma reachable1:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "a \<in> verts G" "b \<in> verts G"
  shows "a\<rightarrow>\<^sup>*\<^bsub>G\<^esub>b"
  by (metis assms reachable_def rtrancl_on.simps)

definition (in wf_digraph) "connect_sym \<equiv> (\<forall>a b. a \<rightarrow>\<^sup>* b \<longrightarrow> b \<rightarrow>\<^sup>* a)"

lemma (in wf_digraph) reach_sym_arc:
  assumes "connect_sym"
  shows  "a \<rightarrow>\<^bsub>G\<^esub> b \<Longrightarrow> b \<rightarrow>\<^sup>* a"
  using assms connect_sym_def by blast

lemma arc_to_ends_pair [simp]: "arc_to_ends (with_proj g) e = e"
  by simp

lemma (in wf_digraph) card_sccs_1: "card sccs = 1 \<Longrightarrow> sccs = {G}"
  by (smt (verit, del_insts) card_1_singletonE card_sccs_verts empty_iff image_empty
        in_scc_of_self in_sccs_verts_conv_reachable in_verts_sccsD_sccs induce_eq_iff_induced
        induced_subgraph_refl scc_of_in_sccs_verts sccs_verts_conv_scc_of singleton_iff 
        wf_digraph.reachable_in_verts(1) wf_digraph_axioms)

lemma (in wf_digraph) card_sccs_connected: "(card sccs = 1) = strongly_connected G"
  by (metis One_nat_def card.empty card.insert empty_iff finite.emptyI
      strongly_connected_eq_iff card_sccs_1)

lemma (in fin_digraph) finite_sccs: "finite sccs"
  using finite_imageD finite_sccs_verts inj_on_verts_sccs sccs_verts_conv by auto

lemma comm_graph_union: "compatible g h \<Longrightarrow> union g h = union h g"
  by (simp add: Un_commute compatible_head compatible_tail)

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

lemma (in pair_wf_digraph) wf_reverse: "pair_wf_digraph (G\<^sup>R)"
  unfolding reverse_def by (simp add: in_arcsD1 in_arcsD2 pair_wf_digraph_def)

lemma arc_reverse: "x\<rightarrow>\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def)

lemma reach_reverse: "x\<rightarrow>\<^sup>*\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def reachable_def rtrancl_on_converseI)

lemma (in pre_digraph) "scc_of x \<subseteq> verts G"
  using pre_digraph.scc_of_def reachable_in_vertsE by fastforce

section \<open>Lemmas about graph union\<close>

locale compatible_digraphs = G: wf_digraph G + H: wf_digraph H
  for G :: "('a, 'b) pre_digraph" and H :: "('a, 'b) pre_digraph" +
  assumes "compatible G H"
begin

interpretation graph_union: pre_digraph "union G H" .

lemma sccs_union_subgraph: "x \<in> G.sccs \<Longrightarrow> \<exists>x' \<in> graph_union.sccs. subgraph x x'"
  sorry

lemma sccs_union: "\<exists>S. \<Union>S = G.sccs \<union> H.sccs \<and> G.Union ` S = graph_union.sccs"
  sorry

end
end
