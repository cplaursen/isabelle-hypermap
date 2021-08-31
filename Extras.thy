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

lemma appears_before_empty: "\<not> appears_before [] x y"
  by (metis appears_before_in(1) empty_iff empty_set)

lemma not_appears_before_in: "x \<notin> set l \<or> y \<notin> set l \<Longrightarrow> \<not> appears_before l x y"
  by (meson appears_before_in)

lemma appears_before_id: "appears_before l x x \<longleftrightarrow> x \<in> set l"
  apply (auto simp add: appears_before_in(1))
  by (metis Cons_nth_drop_Suc appears_before_def index_less_size_conv list.set_intros(1) nth_index)

lemma appears_before_cons:
 "appears_before (x#l) y z \<longleftrightarrow>
  (if x = y then z \<in> set (x#l) else appears_before l y z)"
  by (simp add: appears_before_def)

lemma appears_before_append: 
  assumes "appears_before p x y \<or> appears_before q x y \<or> x \<in> set p \<and> y \<in> set q"
  shows "appears_before (p@q) x y"
proof -
  {
    assume "appears_before p x y"
    then have "y \<in> set (drop (index p x) p)"
      by (meson appears_before_def)
    also have "index p x = index (p@q) x"
      by (metis \<open>appears_before p x y\<close> appears_before_in(1) index_append)
    then have "set (drop (index p x) p) \<subseteq> set (drop (index (p@q) x) (p@q))"
      by simp
    ultimately have "appears_before (p @ q) x y"
      by (meson appears_before_def in_mono)
  } note 1 = this
  {
    assume "appears_before q x y"
    then have "y \<in> set (drop (index q x) q)"
      by (meson appears_before_def)
    also have "length p + index q x \<ge> index (p@q) x"
      by (simp add: index_append index_le_size trans_le_add1)
    then have "set (drop (index q x) q) \<subseteq> set (drop (index (p@q) x) (p@q))"
      by (metis add_diff_cancel_left' append_Nil drop_all drop_append 
          le_add1 set_drop_subset_set_drop)
    ultimately have ?thesis
      by (meson appears_before_def subsetD)
  } note 2 = this
  {
    assume "x \<in> set p" "y \<in> set q"
    then have "set q \<subseteq> set (drop (index (p@q) x) (p@q))"
      by (simp add: index_append index_le_size)
    then have ?thesis
      by (metis \<open>y \<in> set q\<close> appears_before_def subset_iff)
  } note 3 = this
  from 1 2 3 assms show ?thesis by auto
qed

section \<open>Permutations and funpow\<close>
lemma cycles_funpow:
  assumes "z \<in> set_cycle (perm_orbit p x)"
  shows "\<exists>n. (apply_perm p ^^ n) z = x"
proof -
  from assms have "(apply_perm p ^^ n) z \<in> set_cycle (perm_orbit p x)" for n
    by simp
  also have "x \<in> set_cycle (perm_orbit p x)" 
    using assms by fastforce
  ultimately show ?thesis
    by (metis apply_perm_power assms funpow_apply_cycle_perm_orbit set_cycle_ex_funpow)
qed

lemma funpow_cycles:
  assumes "(apply_perm p ^^ n) z = x" "z \<noteq> x"
  shows "z \<in> set_cycle (perm_orbit p x)"
  by (metis apply_perm_eq_idI apply_perm_neq_idI apply_perm_power apply_set_perm assms 
      funpow_apply_perm_in_perm_orbit_iff set_perm_powerD start_in_perm_orbit_iff)

lemma permutes_perm:
  assumes "finite S" "f permutes S"
  shows "(Perm f) permutes S"
  by (metis (no_types, lifting) Perm_inverse assms mem_Collect_eq permutation permutation_permutes)

lemma size_perm_type_eq_card: "size (perm_type p) = card (cycles_of_perm p)"
  by (simp add: perm_type_def)

lemma perm_orbit_set_comm: "a \<in> set_cycle (perm_orbit p b) \<Longrightarrow> b \<in> set_cycle (perm_orbit p a)"
  by (metis apply_cycle_perm_orbit apply_cycle_same_iff cycles_funpow
      funpow_apply_perm_in_perm_orbit_iff start_in_perm_orbit_iff)

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

lemma count_cycles_on_empty: "S = {} \<Longrightarrow> count_cycles_on S p = 0"
  using count_cycles_on_eq_card set_perm_subset by auto

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

lemma vpath_sublist: 
  assumes "vpath (p @ q) G"
  shows "p \<noteq> [] \<Longrightarrow> vpath p G"  "q \<noteq> [] \<Longrightarrow> vpath q G"
  by (meson assms distinct_append vpath_def vwalkI_append_l vwalkI_append_r)+

lemma (in wf_digraph) sccs_empty: "verts G = {} \<Longrightarrow> sccs = {}"
  using sccs_verts_conv sccs_verts_conv_scc_of by force

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

end
