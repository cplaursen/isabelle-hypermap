theory Walkup
  imports Hypermap
begin         

context hypermap begin
text \<open>Special case for triangular identity - either merge two cycles or split a cycle
         - If z and node z are on different e cycles walkupE merges them
         - Otherwise, walkupE splits this cycle\<close>

definition skip_edge where
"skip_edge z h x \<equiv> if z = x then z else
                  (if (edge h z) = z then edge h x else
                  (if (face h (edge h x)) = z then edge h z else
                  (if edge h x = z then edge h (node h z) else edge h x)))"

lemma skip_edge_id: "skip_edge z h z = z"
  unfolding skip_edge_def by simp

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
    have "x = z \<Longrightarrow> skip_edge z H x = x" by (simp add: skip_edge_id)
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

text "Degenerate case for walkup where one of the permutations is an identity on z"
lemma glink_skip_edge:
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

definition cross_edge where
"cross_edge h z \<equiv> z\<rightarrow>\<^sup>*\<^bsub>cedge h\<^esub>(node h z)"

definition cross_edge_alt where
"cross_edge_alt h z \<equiv> z\<rightarrow>\<^sup>*\<^bsub>cedge h\<^esub>(hypermap.node_inv h z)"

lemma cross_edge_split:
  assumes "\<not> cross_edge_alt H z" "\<not> z\<rightarrow>\<^bsub>glink H\<^esub>z" "z \<in> darts H"
  shows "edge H z \<in> set_cycle (perm_orbit (Perm (skip_edge z H)) (node_inv H z))"
  using assms oops

definition walkupE :: "'a pre_hypermap \<Rightarrow> 'a \<Rightarrow> 'a pre_hypermap" where
"walkupE h z = 
  \<lparr>darts = darts h - {z},
   edge = Perm (skip_edge z h),
   node = Perm (skip z (node h)),
   face = Perm (skip z (face h))\<rparr>"

theorem hypermap_walkupE:
  shows "hypermap (walkupE H z)" (is "hypermap ?E")
proof
  have "finite (darts H)" by (rule finite_darts)
  also have "(darts ?E) = (darts H) - {z}"
    by (simp add: walkupE_def)
  ultimately show "finite (darts ?E)" by auto
  show "edge (walkupE H z) permutes darts (walkupE H z)"
    by (simp add: finite_darts hypermap_axioms permutes_perm skip_edge_permutes walkupE_def)
  show "(node (walkupE H z)) permutes darts (walkupE H z)"
    by (simp add: perm_node skip_perm skip_permutes walkupE_def)
  show "(face (walkupE H z)) permutes darts (walkupE H z)"
    by (simp add: perm_face skip_perm skip_permutes walkupE_def)
next
  fix x have "skip_edge z H (skip z (node H) (skip z (face H) x)) = x"
  proof (cases "x = z")
    case True
    then show ?thesis
      by (auto simp add: skip_id skip_edge_id)
  next
    case False
    then show ?thesis
      by (smt (z3) apply_inj_eq_iff faceK skip_def skip_edge_def)
  qed
  then show "(edge (walkupE H z)) \<langle>$\<rangle> (node (walkupE H z)) \<langle>$\<rangle> (face (walkupE H z)) \<langle>$\<rangle> x = x"
    by (simp add: hypermap_axioms skip_perm walkupE_def skip_edge_Perm)
qed


text \<open>(From fourcolour.walkup.v)
 cross_edge z <=> z and node z are on the same edge cycle. This edge cycle 
                 will be split in two in WalkupE z if z is not degenerate,
                 i.e., ~~ glink z z. Conversely, if cross_edge z does not
                 hold or if z if degenerate, the genus and hence the Euler
                 planarity condition are invariant.
\<close>

text \<open>cross_edge does not hold, so the edge cycles are merged and edge z is in the same edge cycle
      as node z\<close>
lemma not_cross_edge_walkup:
  assumes "z \<in> darts H" "\<not> cross_edge H z" "\<not> z\<rightarrow>\<^bsub>glink H\<^esub>z"
  shows "edge H z\<rightarrow>\<^sup>*\<^bsub>cedge (walkupE H z)\<^esub>node H z"
  by (smt (verit, ccfv_threshold) assms Gr_eq Gr_wf apply_perm_image arc_in_union cedge_def
      cross_edge_def darts_face edgeK fst_conv glink_def hypermap.cedge_reachable_sym
      hypermap.perm_edge hypermap_axioms hypermap_walkupE imageE insert_Diff insert_iff
      pair_wf_digraph.arc_fst_in_verts permutes_in_image pre_hypermap.select_convs(1)
      pre_hypermap.select_convs(2) reachable_def rtrancl_on.simps skip_edge_Perm skip_edge_def
      walkupE_def wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(1) with_proj_simps(3))

text \<open>cross_edge does not hold, so the edge cycle is split\<close>
lemma cross_edge_walkup:
  assumes "z \<in> darts H" "cross_edge H z" "\<not> z\<rightarrow>\<^bsub>glink H\<^esub>z"
  shows "\<not>face H z\<rightarrow>\<^sup>*\<^bsub>cedge (walkupE H z)\<^esub>node H z"
  oops

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