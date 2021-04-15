theory Walkup
  imports Hypermap Skip
begin

section \<open>Skip edge\<close>
text \<open>Special case for triangular identity - either merge two cycles or split a cycle
         - If z and node z are on different e cycles walkupE merges them
         - Otherwise, walkupE splits this cycle\<close>

definition skip_edge where
"skip_edge z h x \<equiv> if z = x then z else
                  (if (edge h z) = z then edge h x else
                  (if (face h (edge h x)) = z then edge h z else
                  (if edge h x = z then edge h (node h z) else edge h x)))"

text \<open>This definition follows Stahl's 1983 paper, with P and Q swapped\<close>
definition skip_edge_alt where
"skip_edge_alt z h x \<equiv>
 skip z (edge h * cycle_perm (cycle_of_list [z, node h (face h z), node h z])) x"

lemma (in hypermap) skip_edge_altdef:
  assumes "node H z \<noteq> z"
  shows "skip_edge z H = skip_edge_alt z H" (is "?L = ?R")
proof
  fix x consider
    (id) "x = z"
    | (edge_z) "x \<noteq> z \<and> (edge H z) = z" 
    | (face_edge)"x \<noteq> z \<and> (edge H z) \<noteq> z \<and> face H (edge H x) = z" 
    | (edge_x) "x \<noteq> z \<and> (edge H z) \<noteq> z \<and> face H (edge H x) \<noteq> z \<and> edge H x = z" 
    | (no_match) "x \<noteq> z \<and> (edge H z) \<noteq> z \<and> face H (edge H x) \<noteq> z \<and> edge H x \<noteq> z"
    by auto
  then show "?L x = ?R x"
proof cases
  case id then show ?thesis
    by (simp add: skip_edge_def skip_edge_alt_def)
next
  case edge_z
  then have "?L x = edge H x" by (metis skip_edge_def)
  also have "?R x = edge H x"
    by (metis skip_z_eq_fz cycle_of_list_not_distinct cycle_perm_id distinct_length_2_or_more
        edge_z mult.right_neutral nodeK skip_edge_alt_def)
  finally show ?thesis by simp
next
  case face_edge then show ?thesis
    by (smt (verit, ccfv_threshold) apply_inj_eq_iff apply_perm_sequence apply_perm_swap(2)
 cycle_of_list_not_distinct cycle_perm_cycle_of_list_doubleton cycle_perm_id skip_edge_alt_def
 cycle_perm_of_list_Cons_Cons distinct_length_2_or_more edgeK mult.right_neutral skip_def skip_edge_def)
next
  case edge_x
  then have "skip_edge z H x = edge H (node H z)"
    by (metis skip_edge_def)
  moreover {
    from edge_x have "edge H x = z" by simp
    then have "x = node H (face H z)"
      using nodeK by force
    then have "(cycle_perm (cycle_of_list [z, node H (face H z), node H z])) x = node H z"
      using assms edge_x by force
    hence "?R x = edge H (node H z)"
      by (metis \<open>x = (node H) \<langle>$\<rangle> (face H) \<langle>$\<rangle> z\<close> apply_inj_eq_iff 
          apply_perm_sequence edge_x skip_invariant skip_edge_alt_def)
  }
  ultimately show ?thesis by simp
next
  case no_match 
  then have "?L x = edge H x" by (metis skip_edge_def)
  also 
  { have "cycle_perm (cycle_of_list [z, node H (face H z), node H z]) x = x"
      by (smt (verit, ccfv_SIG) apply_cycle_of_list apply_perm_cycle apply_perm_swap(3)
          cycle_lookup_hd cycle_perm_cycle_of_list_doubleton cycle_perm_same_iff
          distinct_length_2_or_more hypermap.edgeK hypermap.faceK hypermap_axioms insert_iff
          list.simps(15) no_match perm_eq_iff set_cycle_code)
    then have "?R x = edge H x" unfolding skip_edge_alt_def
      by (simp add: apply_perm_times no_match skip_def)
  }
  finally show ?thesis by simp
qed
qed

lemma skip_edge_id [simp]: "skip_edge z h z = z"
  unfolding skip_edge_def by simp

context hypermap 
begin
lemma skip_edge_Perm: "(\<langle>$\<rangle>) (Perm (skip_edge z H)) = skip_edge z H"
proof
  obtain A where "A = darts H" by auto
  fix x show "(Perm (skip_edge z H)) \<langle>$\<rangle> x = skip_edge z H x"
  proof (rule apply_perm_Perm)
    show "finite (A - {z})"
      by (simp add: \<open>A = darts H\<close> finite_darts)
    show "inj_on (skip_edge z H) (A - {z})"
      by (smt (z3) apply_inj_eq_iff faceK inj_on_def skip_edge_def)
    show "\<And>x. x \<in> (A - {z}) \<Longrightarrow> skip_edge z H x \<in> (A - {z})"
      by (smt (z3) Diff_iff \<open>A = darts H\<close> apply_inj_eq_iff empty_iff faceK perm_edge perm_face insert_iff permutes_in_image skip_edge_def)
    show "\<And>x. x \<notin> (A - {z}) \<Longrightarrow> skip_edge z H x = x"
      by (smt (z3) Diff_empty Diff_insert0 Permutations.permutes_not_in \<open>A = darts H\<close> perm_edge perm_face insert_Diff insert_iff skip_edge_def)
  qed
qed

lemma skip_edge_permutes: "skip_edge z H permutes darts H - {z}"
  unfolding permutes_def
proof
  have "\<And>x. x \<notin> darts H - {z} \<Longrightarrow> skip_edge z H x = x"
  proof -
    fix x assume "x \<notin> darts H - {z}"
    then have disj: "x \<notin> darts H \<or> x = z" by simp
    have "x = z \<Longrightarrow> skip_edge z H x = x" by simp
    also have "x \<notin> darts H \<Longrightarrow> skip_edge z H x = x"
      by (metis Permutations.permutes_not_in perm_edge perm_face skip_edge_def)
    ultimately show "skip_edge z H x = x"
      using disj by linarith
    qed
    then show "\<forall>x. x \<notin> darts H - {z} \<longrightarrow> skip_edge z H x = x" by simp
next
  show "\<forall>y. \<exists>!x. skip_edge z H x = y"
    by (metis skip_edge_Perm UNIV_I bij_apply bij_imp_permutes permutes_univ)
qed
end

locale not_degenerate_walkup = hypermap +
  fixes z
  assumes z_dart: "z \<in> darts H"
      and z_not_glink: "\<not>z\<rightarrow>\<^bsub>glink H\<^esub>z"
begin

lemma skip_edge_edge: "skip_edge z H (node H (face H z)) = (edge H (node H z))"
  unfolding skip_edge_def
  by (metis Gr_eq cedge_def cface_def edgeK glink_def not_degenerate_walkup.axioms(2) 
      not_degenerate_walkup_axioms not_degenerate_walkup_axioms_def pair_union_arcs_disj)

lemma skip_edge_node: "skip_edge z H (node H z) = (edge H z)"
  unfolding skip_edge_def
  by (metis Gr_eq cnode_def edgeK faceK glink_def not_degenerate_walkup.axioms(2) 
      not_degenerate_walkup_axioms not_degenerate_walkup_axioms_def pair_union_arcs_disj
      skip_edge_def skip_edge_edge)

lemma skip_edge_invariant:
  fixes x
  assumes "x \<noteq> z" "face H (edge H x) \<noteq> z" "edge H x \<noteq> z"
  shows "skip_edge z H x = edge H x"
  unfolding skip_edge_def using assms by auto
end

text "Degenerate case for walkup where one of the permutations is an identity on z"
lemma (in hypermap) glink_skip_edge:
  assumes "z\<rightarrow>\<^bsub>glink H\<^esub>z"
  shows "skip_edge z H = skip z (edge H)"
proof
  fix x
  from assms have z_eq: "z = edge H z \<or> z = node H z \<or> z = face H z"
    unfolding glink_def cedge_def cnode_def cface_def by (metis Gr_eq pair_union_arcs_disj)
  have "z = edge H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    by (simp add: skip_def skip_edge_def)
  also have "z = node H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    unfolding skip_edge_def skip_def using assms nodeK by fastforce
  moreover have "z = face H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    unfolding skip_edge_def skip_def using assms faceK by auto
  ultimately show "skip_edge z H x = skip z (edge H) x"
    using z_eq by blast
qed

section \<open>WalkupE\<close>

definition walkupE :: "'a pre_hypermap \<Rightarrow> 'a \<Rightarrow> 'a pre_hypermap" where
"walkupE h z = 
  \<lparr>darts = darts h - {z},
   edge = Perm (skip_edge z h),
   node = skip_perm z (node h),
   face = skip_perm z (face h)\<rparr>"

theorem (in hypermap) hypermap_walkupE:
  shows "hypermap (walkupE H z)" (is "hypermap ?E")
proof
  have "finite (darts H)" by (rule finite_darts)
  also have "(darts ?E) = (darts H) - {z}"
    by (simp add: walkupE_def)
  ultimately show "finite (darts ?E)" by auto
  show "edge (walkupE H z) permutes darts (walkupE H z)"
    by (simp add: finite_darts hypermap_axioms permutes_perm skip_edge_permutes walkupE_def)
  show "(node (walkupE H z)) permutes darts (walkupE H z)"
    by (simp add: walkupE_def apply_skip_perm perm_node skip_permutes)
  show "(face (walkupE H z)) permutes darts (walkupE H z)"
    by (simp add: walkupE_def apply_skip_perm perm_face skip_permutes)
next
  fix x have "skip_edge z H (skip z (node H) (skip z (face H) x)) = x"
  proof (cases "x = z")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by (smt (z3) apply_inj_eq_iff faceK skip_def skip_edge_def)
  qed
  then show "(edge (walkupE H z)) \<langle>$\<rangle> (node (walkupE H z)) \<langle>$\<rangle> (face (walkupE H z)) \<langle>$\<rangle> x = x"
    by (simp add: apply_skip_perm skip_edge_Perm walkupE_def)
qed

text \<open>(From fourcolour.walkup.v)
 cross_edge z <=> z and node z are on the same edge cycle. This edge cycle 
                 will be split in two in WalkupE z if z is not degenerate,
                 i.e., ~~ glink z z. Conversely, if cross_edge z does not
                 hold or if z if degenerate, the genus and hence the Euler
                 planarity condition are invariant.
\<close>

definition cross_edge where
"cross_edge h z \<equiv> z\<rightarrow>\<^sup>*\<^bsub>cedge h\<^esub>node h z"

lemma (in hypermap) cross_edge_path_edge:
  "cross_edge H z \<longleftrightarrow> edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z" (is "?L = ?R")
proof
  assume ?L show ?R
  proof (rule wf_digraph.reachable_trans)
    show "wf_digraph (cedge H)"
      by (simp add: wf_cedge wf_digraph_wp_iff)
    then show "(edge H) \<langle>$\<rangle> z \<rightarrow>\<^sup>*\<^bsub>with_proj (cedge H)\<^esub> z"
      by (metis (no_types, lifting) \<open>cross_edge H z\<close> Gr_eq Permutations.permutes_not_in cedge_def
          hypermap.cedge_reachable_sym cross_edge_def hypermap_axioms perm_edge
          reach_sym_arc wf_digraph.reachable_in_verts(1) wf_digraph.reachable_refl)
    show "z \<rightarrow>\<^sup>*\<^bsub>with_proj (cedge H)\<^esub> (node H) \<langle>$\<rangle> z"
      using \<open>cross_edge H z\<close> unfolding cross_edge_def by simp
  qed
next
  assume ?R show ?L
    by (metis Gr_eq Permutations.permutes_not_in cedge_def cross_edge_def
        \<open>(edge H) \<langle>$\<rangle> z \<rightarrow>\<^sup>*\<^bsub>with_proj (cedge H)\<^esub> (node H) \<langle>$\<rangle> z\<close> perm_edge wf_cedge 
        wf_digraph.adj_reachable_trans wf_digraph_wp_iff)
qed

locale degenerate_walkup = hypermap +
  fixes z
  assumes z_glink: "z\<rightarrow>\<^bsub>glink H\<^esub> z"
begin

lemma z_dart: "z \<in> darts H"
  by (metis z_glink Gr_eq cedge_def cface_def cnode_def glink_def pair_union_arcs_disj)

lemma degenerate_euler:
  defines "H' \<equiv> walkupE H z"
  shows "euler_lhs H - euler_lhs H' = euler_rhs H - euler_rhs H'"
proof (cases "edge H z = z \<and> node H z = z \<and> face H z = z")
interpret face_perm_on: finite_perm_on "face H" "darts H"
  by (rule finite_perm_on_face)
interpret node_perm_on: finite_perm_on "node H" "darts H"
  by (rule finite_perm_on_node)
interpret edge_perm_on: finite_perm_on "edge H" "darts H"
  by (rule finite_perm_on_edge)
  case True
  have "euler_rhs H' = euler_rhs H - 3"
  proof -
    have "count_cycles_on (darts H) (node H) = count_cycles_on (darts H') (node H') + 1"
        by (metis True assms node_perm_on.cycle_count_skip_singleton finite_darts
            pre_hypermap.select_convs(1) pre_hypermap.select_convs(3) walkupE_def z_dart)
    also have "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H') + 1"
        by (metis True assms face_perm_on.cycle_count_skip_singleton finite_darts
            pre_hypermap.select_convs(1) pre_hypermap.select_convs(4) walkupE_def z_dart)
    moreover have "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 1"
      by (metis True apply_skip_perm assms finite_darts glink_skip_edge perm.apply_perm_inverse
          perm_edge perm_on.cycle_count_skip_singleton perm_on.intro pre_hypermap.select_convs(1)
          pre_hypermap.select_convs(2) walkupE_def z_glink z_dart)
    ultimately show ?thesis
      by (simp add: euler_rhs_def)
  qed
  also have "euler_lhs H' = euler_lhs H - 3"
  proof -
    have dart_count: "card (darts H') = card (darts H) - 1"
      by (simp add: assms node_perm_on.finite_S walkupE_def z_dart)
    have "card (pre_digraph.sccs (glink H')) = card (pre_digraph.sccs (glink H)) - 1"
      sorry
    then have "card (darts H') + 2 * (card (pre_digraph.sccs (glink H'))) =
             card (darts H) - 1 + 2 * (card (pre_digraph.sccs (glink H)) - 1)"
      using dart_count by presburger
    hence "card (darts H') + 2 * card (pre_digraph.sccs (glink H')) =
            card (darts H) + 2 * card (pre_digraph.sccs (glink H)) - 3"
      try0
    then show ?thesis
      using euler_lhs_def sledgehammer
         sorry
  ultimately show ?thesis
    by (metis diff_diff_cancel empty_iff euler_lhs_ge_3 euler_rhs_ge_3 z_dart)
next
  case False
  then show ?thesis sorry
qed
end

context not_degenerate_walkup begin

lemma walkup_node_cycle_count:
  defines "H' \<equiv> walkupE H z"
  shows "count_cycles_on (darts H) (node H) = count_cycles_on (darts H') (node H')"
proof -
  interpret perm_on "(node H)" "(darts H)"
    using perm_node perm_on.intro by blast
  have "count_cycles_on (darts H) (node H) =
        count_cycles_on (darts H - {z}) (skip_perm z (node H))"
    apply (rule cycle_count_skip)
      apply (simp_all add: z_dart finite_darts)
      apply (metis z_not_glink Gr_eq arc_in_union cedge_def glink_def
            skip_edge_id skip_edge_node z_dart)
    done
  then show ?thesis
    by (simp add: assms walkupE_def)
qed

lemma walkup_face_cycle_count:
  defines "H' \<equiv> walkupE H z"
  shows "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H')"
proof -
  interpret perm_on "(face H)" "(darts H)"
    using perm_face perm_on.intro by blast
  have "count_cycles_on (darts H) (face H) =
        count_cycles_on (darts H - {z}) (skip_perm z (face H))"
    apply (rule cycle_count_skip)
      apply (simp_all add: z_dart finite_darts)
      apply (metis Gr_eq arc_in_union cedge_def edgeK glink_def
            skip_edge_edge skip_edge_node z_dart z_not_glink)
    done
  then show ?thesis
    by (simp add: assms walkupE_def)
qed

text \<open>cross_edge does not hold, so the edge cycles are merged and edge z is in the same edge cycle
      as node z\<close>
lemma merge_walkup_path:
  assumes "\<not> cross_edge H z"
  shows "edge H z\<rightarrow>\<^sup>*\<^bsub>cedge (walkupE H z)\<^esub>node H z"
  by (smt (z3) Gr_eq Permutations.permutes_not_in assms cedge_def cross_edge_def
      hypermap.cedge_reachable_sym hypermap.skip_edge_permutes hypermap.wf_cedge hypermap_axioms
      hypermap_walkupE not_degenerate_walkup.axioms(2) not_degenerate_walkup_axioms
      not_degenerate_walkup_axioms_def pre_hypermap.select_convs(1) pre_hypermap.select_convs(2) 
      reach_sym_arc skip_edge_Perm skip_edge_node walkupE_def wf_digraph_wp_iff)

lemma merge_walkup_edge_cycles:
  assumes  "\<not> cross_edge H z"
  defines "H' \<equiv> walkupE H z"
  shows "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 1"
 sorry

lemma not_cross_edge_euler_lhs:
  assumes "\<not> cross_edge H z"
  defines "H' \<equiv> walkupE H z"
  shows "euler_rhs H = euler_rhs H' + 1"
proof -
  have "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H')"
    by (simp add: assms walkup_face_cycle_count)
  also have "count_cycles_on (darts H) (node H) = count_cycles_on (darts H') (node H')"
    by (simp add: assms walkup_node_cycle_count)
  moreover have "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 1"
    by (simp add: assms merge_walkup_edge_cycles)
  ultimately show ?thesis
    unfolding euler_rhs_def by simp
qed

lemma cross_edge_euler_rhs:
  assumes "cross_edge H z"
  defines "H' \<equiv> walkupE H z"
  shows "euler_rhs H = euler_rhs H' + 3"
proof -
  have "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H')"
    by (simp add: assms walkup_face_cycle_count)
  also have "count_cycles_on (darts H) (node H) = count_cycles_on (darts H') (node H')"
    by (simp add: assms walkup_node_cycle_count)
  moreover have "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 3"
    sorry
  ultimately show ?thesis
    unfolding euler_rhs_def by simp
qed

text \<open>cross_edge does not hold, so the edge cycle is split\<close>
lemma (in not_degenerate_walkup) cross_edge_walkup:
  assumes "cross_edge H z"
  shows "\<not>edge H z\<rightarrow>\<^sup>*\<^bsub>cedge (walkupE H z)\<^esub>node H (face H z)"
  (*by (metis assms Gr_eq apply_inj_eq_iff apply_skip_perm arc_in_union cedge_def cface_def cnode_def
      glink_def perm.apply_perm_inverse perm_eq_iff pre_hypermap.select_convs(2) skip_edge_Perm 
      skip_id walkupE_def with_proj_simps(3))*)
  sorry


section \<open>Jordan and Euler\<close>
lemma le_genus_walkupE:
  assumes "z \<in> darts H"
  shows "genus (walkupE H z) \<le> genus H"
  oops

lemma Jordan_WalkupE:
  assumes "z \<in> darts H"
  shows "jordan H \<Longrightarrow> jordan (walkupE H z)"
  oops

end
end