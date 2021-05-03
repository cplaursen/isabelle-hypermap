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
      by (smt (z3) Diff_iff \<open>A = darts H\<close> apply_inj_eq_iff empty_iff faceK
          perm_edge perm_face insert_iff permutes_in_image skip_edge_def)
    show "\<And>x. x \<notin> (A - {z}) \<Longrightarrow> skip_edge z H x = x"
      by (smt (z3) Diff_empty Diff_insert0 Permutations.permutes_not_in \<open>A = darts H\<close>
          perm_edge perm_face insert_Diff insert_iff skip_edge_def)
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

lemma skip_edgeK: "skip_edge z H (skip z (node H) (skip z (face H) x)) = x"
  by (smt (z3) edgeK faceK nodeK skip_def skip_edge_def)

lemma skip_edge_noteq_z: "x \<noteq> z \<Longrightarrow> skip_edge z H x \<noteq> z"
  by (metis apply_inj_eq_iff skip_edge_Perm skip_edge_id)

lemma (in hypermap) glink_skip_edge: "z\<rightarrow>\<^bsub>glink H\<^esub>z \<Longrightarrow> skip_edge z H = skip z (edge H)"
proof
  fix x assume *: "z\<rightarrow>\<^bsub>glink H\<^esub>z"
  then have z_eq: "z = edge H z \<or> z = node H z \<or> z = face H z"
    unfolding glink_def cedge_def cnode_def cface_def by (metis Gr_eq pair_union_arcs_disj)
  have "z = edge H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    by (simp add: skip_def skip_edge_def)
  also have "z = node H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    unfolding skip_edge_def skip_def using * nodeK by fastforce
  moreover have "z = face H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    unfolding skip_edge_def skip_def using * faceK by auto
  ultimately show "skip_edge z H x = skip z (edge H) x"
    using z_eq by blast
qed
end

section \<open>WalkupE\<close>

definition walkupE :: "'a pre_hypermap \<Rightarrow> 'a \<Rightarrow> 'a pre_hypermap" where
"walkupE h z = 
  \<lparr>darts = darts h - {z},
   edge = Perm (skip_edge z h),
   node = skip_perm z (node h),
   face = skip_perm z (face h)\<rparr>"

locale walkup = hypermap +
  fixes z
  assumes z_dart: "z \<in> darts H"
begin
  definition "H' \<equiv> walkupE H z"

lemma walkup_edge: "edge H' = Perm (skip_edge z H)"
  by (simp add: H'_def walkupE_def)

lemma walkup_node: "node H' = skip_perm z (node H)"
  by (simp add: H'_def walkupE_def)

lemma walkup_face: "face H' = skip_perm z (face H)"
  by (simp add: H'_def walkupE_def)
end

locale not_degenerate_walkup = walkup +
  fixes u v
  assumes z_not_glink: "\<not>z\<rightarrow>\<^bsub>glink H\<^esub>z"
      and dart_u: "u \<in> darts H'"
      and dart_v: "v \<in> darts H'"
begin

lemma u_noteq_z: "u \<noteq> z"
  by (metis dart_u DiffE H'_def insert_iff pre_hypermap.select_convs(1) walkupE_def)

lemma v_noteq_z: "v \<noteq> z"
  by (metis dart_v DiffE H'_def insert_iff pre_hypermap.select_convs(1) walkupE_def)

lemma skip_edge_edge: "skip_edge z H (node H (face H z)) = (edge H (node H z))"
  unfolding skip_edge_def
  by (metis Gr_eq cedge_def cface_def edgeK glink_def pair_union_arcs_disj z_dart z_not_glink)

lemma skip_edge_node: "skip_edge z H (node H z) = (edge H z)"
  unfolding skip_edge_def
  by (smt (z3) Gr_eq apply_perm_image cnode_def darts_face edgeK glink_def imageE
      pair_union_arcs_disj skip_edge_def skip_edge_edge z_dart z_not_glink)

lemma skip_edge_invariant:
  fixes x
  assumes "x \<noteq> z" "face H (edge H x) \<noteq> z" "edge H x \<noteq> z"
  shows "skip_edge z H x = edge H x"
  unfolding skip_edge_def using assms by auto

lemma walkup_darts_subset: "darts H' \<subseteq> darts H"
  unfolding H'_def walkupE_def by simp
end

context walkup 
begin
theorem hypermap_walkupE:
  shows "hypermap H'"
proof
  have "finite (darts H)" by (rule finite_darts)
  also have "(darts H') = (darts H) - {z}"
    by (simp add: H'_def walkupE_def)
  ultimately show "finite (darts H')" by auto
  show "edge H' permutes darts (H')"
    by (simp add: H'_def finite_darts hypermap_axioms permutes_perm skip_edge_permutes walkupE_def)
  show "(node (H')) permutes darts (H')"
    by (simp add: H'_def walkupE_def apply_skip_perm perm_node skip_permutes)
  show "(face (H')) permutes darts (H')"
    by (simp add: H'_def walkupE_def apply_skip_perm perm_face skip_permutes)
  fix x show "(edge (H')) \<langle>$\<rangle> (node (H')) \<langle>$\<rangle> (face (H')) \<langle>$\<rangle> x = x"
    by (simp add: H'_def skip_edgeK apply_skip_perm skip_edge_Perm walkupE_def)
qed

lemma card_darts_walkup: "card (darts H') = card (darts H) - 1"
  by (simp add: H'_def finite_darts walkupE_def z_dart)

text \<open>(From fourcolour.walkup.v)
 cross_edge z <=> z and node z are on the same edge cycle. This edge cycle 
                 will be split in two in WalkupE z if z is not degenerate,
                 i.e., ~~ glink z z. Conversely, if cross_edge z does not
                 hold or if z if degenerate, the genus and hence the Euler
                 planarity condition are invariant.
\<close>

definition "cross_edge \<equiv> z\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z"

lemma cross_edge_path_edge:
  "cross_edge \<longleftrightarrow> edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z" (is "?L = ?R")
proof
  assume ?L show ?R
  proof (rule wf_digraph.reachable_trans)
    show "wf_digraph (cedge H)"
      by (simp add: wf_cedge wf_digraph_wp_iff)
    then show "(edge H) \<langle>$\<rangle> z \<rightarrow>\<^sup>*\<^bsub>with_proj (cedge H)\<^esub> z"
      by (metis Gr_eq cedge_connect_sym cedge_def wf_digraph.reach_sym_arc z_dart)
    show "z \<rightarrow>\<^sup>*\<^bsub>with_proj (cedge H)\<^esub> (node H) \<langle>$\<rangle> z"
      using \<open>cross_edge\<close> unfolding cross_edge_def by simp
  qed
next
  assume ?R then show ?L
    by (metis Gr_eq cedge_def cross_edge_def wf_cedge wf_digraph.adj_reachable_trans 
        wf_digraph_wp_iff z_dart)
qed

interpretation clink: fin_digraph "clink H"
  by (simp add: finite_clink)

definition z_comp where
"z_comp \<equiv> (clink H') \<restriction> (clink.scc_of z - {z})"

lemma wf_z_comp: "wf_digraph z_comp"
   by (simp add: fin_digraph.axioms(1) hypermap.finite_clink hypermap_walkupE 
        wf_digraph.wellformed_induce_subgraph z_comp_def)

interpretation z_comp: fin_digraph z_comp
proof intro_locales
  show "wf_digraph z_comp" using wf_z_comp .
  have "finite (verts z_comp)"
    by (metis clink.finite_verts clink.scc_of_empty_conv clink.scc_of_in_sccs_verts 
        clink.sccs_verts_subsets finite_Diff finite_subset induce_subgraph_verts 
        infinite_imp_nonempty z_comp_def)
  also {
    have "clink.scc_of z \<subseteq> verts (clink H)"
      using clink.scc_of_empty_conv clink.scc_of_in_sccs_verts clink.sccs_verts_subsets by blast
    then have "clink.scc_of z - {z} \<subseteq> verts (clink H)"
      using calculation by blast
    then have "arcs z_comp \<subseteq> arcs (clink H')"
      by (simp add: z_comp_def)
    then have "finite (arcs z_comp)"
      by (meson fin_digraph.finite_arcs finite_subset hypermap.finite_clink hypermap_walkupE)
  }
  ultimately show "fin_digraph_axioms z_comp"
    using fin_digraph_axioms.intro by blast
qed

definition z_barb where
"z_barb \<equiv> clink.scc_of z = {z}"

lemma z_barb_z: "z_barb = (edge H z = z \<and> node H z = z \<and> face H z = z)"
proof
  assume *: "z_barb"
  then show "edge H z = z \<and> node H z = z \<and> face H z = z"
    by (smt (verit) DiffD2 apply_inj_eq_iff clink.in_sccs_verts_conv_reachable
        clink.scc_of_in_sccs_verts clinkN clink_connect_sym fst_conv hypermap.clinkF hypermap_axioms
        insert_Diff insert_iff nodeK pair_wf_digraph.arc_fst_in_verts wf_clink
        wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(1) with_proj_simps(3)
        z_barb_def z_dart clink.wf_digraph_axioms wf_digraph.reach_sym_arc)
next
  assume assms: "(edge H z = z \<and> node H z = z \<and> face H z = z)"
  then have "node H z = z \<and> face H z = z"
    by simp
  {
    fix x assume *: "x \<in> clink.scc_of z" "x \<noteq> z"
    then have "False" 
    proof -
      have "x\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>z"
        using *(1) clink.scc_of_def by blast
      then obtain y where "y \<noteq> z \<and> y\<rightarrow>\<^bsub>clink H\<^esub>z"
        by (smt (verit) "*"(2) clink.awalk_ends clink.reachable_awalk wf_clink 
              wf_digraph.converse_reachable_induct wf_digraph_wp_iff)
      also have "\<And>u. u \<rightarrow>\<^bsub>clink H\<^esub>z \<Longrightarrow> u = z"
        unfolding clink_def
        by (metis Gr_eq assms apply_inj_eq_iff cface_def cnode_def converse_iff
            pair_pre_digraph.simps(2) pair_union_arcs_disj reverse_def with_proj_simps(3))
      ultimately show ?thesis
        by auto
    qed
    then have "x \<in> clink.scc_of z \<Longrightarrow> x = z"
      by blast
  }
  then show "z_barb"
    using clink.wf_digraph_axioms clinkF pre_digraph.scc_of_def wf_digraph.adj_in_verts(1)
      z_barb_def z_dart by fastforce
qed
                                                    
lemma z_barb_comp: "z_barb = (pre_digraph.sccs z_comp = {})"
proof
  assume z_barb
  then have "verts z_comp = {}"
    unfolding z_barb_def z_comp_def by simp
  moreover have "arcs z_comp = {}"
    by (metis wf_z_comp calculation ex_in_conv wf_digraph.wellformed(2))
  ultimately show "pre_digraph.sccs z_comp = {}"
    by (metis antisym_conv bot.extremum equals0I pre_digraph.in_sccsE
        pre_digraph.induced_subgraph_altdef strongly_connected_def subgraph_def)
next
  assume "pre_digraph.sccs z_comp = {}"
  then have "verts z_comp = {}"
    by (metis empty_iff equals0I wf_digraph.in_verts_sccsD_sccs 
        wf_digraph.scc_of_in_sccs_verts wf_z_comp) 
  then have "clink.scc_of z - {z} = {}"
    using z_comp_def by force 
  then have "clink.scc_of z = {z}"
    by (metis clink.adj_in_verts(2) clink.in_scc_of_self
        clinkN insert_Diff walkup.z_dart walkup_axioms)
  then show z_barb
    unfolding H'_def z_comp_def z_barb_def by blast
qed


definition "disconnected \<equiv> card (pre_digraph.sccs z_comp) > 1"

lemma disconnected_not_glink: "disconnected \<Longrightarrow> \<not> z\<rightarrow>\<^bsub>glink H\<^esub>z"
proof
  assume *: disconnected "z\<rightarrow>\<^bsub>glink H\<^esub>z"
  then have "\<not>z_barb"
    using disconnected_def z_barb_comp by force
  have "strongly_connected z_comp"
  proof
    show "verts z_comp \<noteq> {}"
      using \<open>\<not> z_barb\<close> z_barb_comp z_comp.sccs_conv_sccs_verts z_comp.sccs_verts_conv_scc_of
      by force
    show "u \<in> verts z_comp \<Longrightarrow> v \<in> verts z_comp \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>z_comp\<^esub> v" for u v
      sorry
  qed
  then have "card (pre_digraph.sccs z_comp) = 1"
    using wf_digraph.card_sccs_connected wf_z_comp by blast
  then show False
    using *(1) disconnected_def by linarith
qed

lemma disconnected_cross_edge: "disconnected \<Longrightarrow> cross_edge"
  sorry

corollary not_cross_connected: "\<not> cross_edge \<Longrightarrow> \<not> disconnected"
  using disconnected_cross_edge by auto

lemma (in not_degenerate_walkup) clink_at_G': "u \<rightarrow>\<^bsub>clink H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^bsub>clink H'\<^esub>v"
proof -
  assume "u \<rightarrow>\<^bsub>clink H\<^esub>v"
  then have "(v\<rightarrow>\<^bsub>cnode H\<^esub> u \<or> u \<rightarrow>\<^bsub>cface H\<^esub> v)" (is "?N \<or> ?F")
    by (metis clink_def converse_iff pair_pre_digraph.simps(2) pair_union_arcs_disj
        reverse_def with_proj_simps(3))
  also have "v\<rightarrow>\<^bsub>cnode H\<^esub> u \<Longrightarrow> v\<rightarrow>\<^bsub>cnode H'\<^esub> u"
    by (metis Gr_eq H'_def apply_skip_perm cnode_def dart_v pre_hypermap.select_convs(3)
        skip_def u_noteq_z v_noteq_z walkupE_def)
  moreover have "u \<rightarrow>\<^bsub>cface H\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>cface H'\<^esub> v"
    by (metis Gr_eq H'_def apply_skip_perm cface_def dart_u pre_hypermap.select_convs(4)
        skip_def u_noteq_z v_noteq_z walkupE_def)
  ultimately show ?thesis
    by (meson dart_u dart_v hypermap.clinkP hypermap_walkupE)
qed

lemma (in not_degenerate_walkup) clink_at_H:
  shows "u \<rightarrow>\<^sup>*\<^bsub>clink H'\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v"
proof -
  interpret clink': wf_digraph "clink H'"
    using hypermap.wf_clink hypermap_walkupE wf_digraph_wp_iff by blast
  interpret clink: wf_digraph "clink H"
    by (simp add: wf_clink wf_digraph_wp_iff)
  assume "u \<rightarrow>\<^sup>*\<^bsub>clink H'\<^esub>v"
  then obtain p' where "clink'.awalk u p' v"
    using clink'.reachable_awalk by blast
  then have "\<exists>p. clink.awalk u p v"
  proof (induct rule: clink'.awalk_induct_raw)
    case Base
    then show ?case
      by (simp add: \<open>clink'.awalk u p' v\<close>)
  next
    case (Cons w)
    then have "w \<in> darts H'"
      unfolding clink_def cface_def cnode_def by (simp add: reverse_def)
    then have "w \<in> verts (clink H)"
      unfolding clink_def cface_def cnode_def reverse_def 
      using walkup_darts_subset by auto
    then have "clink.awalk w [] w"
      by (simp add: clink.awalk_Nil_iff)
    then show ?case by blast
  next
    fix w1 w2 e es
    assume e: "e \<in> arcs (clink H')" "arc_to_ends (with_proj (clink H')) e = (w1, w2)"
    assume IH: "(clink'.awalk w2 es v \<Longrightarrow> \<exists>p. clink.awalk w2 p v)"
    assume clink'_walk:"clink'.awalk w1 (e # es) v"
    from e have disj: "w2\<rightarrow>\<^bsub>cnode H'\<^esub>w1 \<or> w1\<rightarrow>\<^bsub>cface H'\<^esub>w2"
      unfolding clink_def reverse_def 
      by (metis pair_union_arcs_disj arc_to_ends_pair converse_iff pair_pre_digraph.select_convs(2)
          with_proj_simps(2) with_proj_simps(3))
    then have "node H' w2 = w1 \<or> face H' w1 = w2"
      by (metis Gr_eq cface_def cnode_def)
    have "clink'.awalk w2 es v"
      using clink'.awalk_Cons_iff clink'_walk e(2) by fastforce
    then obtain p_ind where p_ind: "clink.awalk w2 p_ind v"
      using IH by blast
    consider "w1 = node H z \<and> node H' w2 = w1"
      | "w1 \<noteq> node H z \<and> node H' w2 = w1"
      | "w2 = face H z \<and> face H' w1 = w2"
      | "w2 \<noteq> face H z \<and> face H' w1 = w2"
      using \<open>(node H') \<langle>$\<rangle> w2 = w1 \<or> (face H') \<langle>$\<rangle> w1 = w2\<close> by fastforce
    then show "\<exists>p. clink.awalk w1 p v"
    proof cases
      case 1
      then have "node H w2 = z"
        by (metis apply_skip_perm faceK skip_id skip_invariant walkup_node)
      then show ?thesis 
        by (metis "1" IH \<open>clink'.awalk w2 es v\<close> arc_to_ends_pair clink.awalk_ConsI clinkN 
            hypermap.perm_node hypermap_axioms permutes_in_image with_proj_simps(2)
            with_proj_simps(3) z_dart)
    next
      case 2
      then have "node H w2 = w1"
        by (metis DiffE Gr_eq H'_def disj apply_skip_perm cface_def cnode_def
            pre_hypermap.select_convs(1) singletonI skip_fz skip_id skip_perm_invariant
            walkupE_def walkup_node)
      then have "w1\<rightarrow>\<^bsub>(cnode H)\<^sup>R\<^esub>w2"
        unfolding cnode_def apply (auto simp add: Gr_def reverse_def Gr_eq)
        by (metis Gr_verts UnE cface_def clink.awalk_hd_in_verts clink_def cnode_def p_ind
            perm_node perm_on.Gr_reverse_eq_inv perm_on.intro verts_union with_proj_union)
      then have "clink.awalk w1 (e#p_ind) v"
        using p_ind apply auto
        by (metis arc_to_ends_pair clink.awalk_Cons_iff clink_def e(2) pair_union_arcs_disj
            prod.sel(1) prod.sel(2) with_proj_simps(2) with_proj_simps(3) with_proj_simps(4) 
            with_proj_simps(5)) 
      then show ?thesis by auto
    next
      case 3
      then have "face H w1 = z"
        by (metis apply_inj_eq_iff apply_skip_perm skip_id skip_invariant walkup_face)
      then show ?thesis 
        by (metis 3 IH \<open>clink'.awalk w2 es v\<close> arc_to_ends_pair clink.awalk_ConsI clinkF 
            hypermap.perm_face hypermap_axioms permutes_in_image with_proj_simps(2)
            with_proj_simps(3) z_dart)
    next
      case 4
      then have "face H w1 = w2"
        by (metis DiffE Gr_eq H'_def disj apply_skip_perm cface_def cnode_def
            pre_hypermap.select_convs(1) singletonI skip_fz skip_id skip_perm_invariant
            walkupE_def walkup_face)
      then have "w1\<rightarrow>\<^bsub>cface H\<^esub>w2"
        unfolding cface_def apply (auto simp add: Gr_def reverse_def Gr_eq)
        by (metis Gr_eq Permutations.permutes_not_in cface_def cnode_def disj perm_face subset_eq 
            walkup_darts_subset)
      then have "clink.awalk w1 (e#p_ind) v"
        using p_ind apply auto
        by (metis arc_to_ends_pair clink.awalk_Cons_iff clink_def e(2) pair_union_arcs_disj
            prod.sel(1) prod.sel(2) with_proj_simps(2) with_proj_simps(3) with_proj_simps(4) 
            with_proj_simps(5)) 
      then show ?thesis by auto
    qed
  qed
  then obtain p where "clink.awalk u p v"
     by blast
  then show ?thesis
    using clink.reachable_awalk by blast
qed

definition "skip_edge_domain \<equiv> {x. x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>z \<or> x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z}"

lemma eCedom: "x \<in> skip_edge_domain \<Longrightarrow> edge H x \<in> skip_edge_domain"
  apply (auto simp: skip_edge_domain_def)
  by (metis Gr_eq Gr_verts cedge_connect_sym cedge_def pre_digraph.converse_reachable_cases wf_cedge 
      wf_digraph.reach_sym_arc wf_digraph_wp_iff)+
end

context not_degenerate_walkup
begin

lemma same_cskip_edge:
  assumes "u \<notin> skip_edge_domain"
  shows "u\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<longleftrightarrow> u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
proof -
  have "(((\<langle>$\<rangle>) (edge H')^^m) u = ((\<langle>$\<rangle>) (edge H)^^m) u)" for m
  proof (induct m)
    case 0 then show ?case by simp
  next
    case (Suc m)
    then show ?case
      by (smt (verit, best) assms cedge_def dart_u funpow_simp_l in_mono mem_Collect_eq nodeK
          not_degenerate_walkup.skip_edge_invariant not_degenerate_walkup_axioms perm_edge
          perm_on.intro perm_on.reach_iff_funpow_perm skip_edge_Perm skip_edge_domain_def
          walkup_darts_subset walkup_edge)
  qed
  then show ?thesis
    by (smt (verit, del_insts) cedge_def dart_u hypermap.perm_edge hypermap_walkupE
        not_degenerate_walkup.walkup_darts_subset not_degenerate_walkup_axioms perm_edge
        perm_on.intro perm_on.reach_iff_funpow_perm subsetD)
qed

lemma sub_cskip_edge: "\<not> cross_edge \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
  sorry

lemma cskip_edge_merge: 
  assumes "\<not> cross_edge" "u \<in> skip_edge_domain"
  shows "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v \<longleftrightarrow> v \<in> skip_edge_domain"
proof
  show "v \<in> skip_edge_domain" if "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
    by (smt (verit, ccfv_SIG) hypermap.wf_cedge assms(2) that dart_u dart_v wf_digraph_wp_iff 
    hypermap_walkupE mem_Collect_eq not_degenerate_walkup.intro not_degenerate_walkup.same_cskip_edge 
    not_degenerate_walkup_axioms.intro skip_edge_domain_def walkup_axioms wf_cedge z_not_glink
    wf_digraph.reachable_trans wf_digraph.connect_sym_def hypermap.cedge_connect_sym)
  assume *: "v \<in> skip_edge_domain"
  have "node H (face H z) \<noteq> z"
      by (metis Gr_eq assms(1) cedge_def cross_edge_path_edge edgeK skip_edge_node skip_edge_noteq_z 
          wf_cedge wf_digraph.reachable_adjI wf_digraph_wp_iff z_dart)
  then have "edge H z \<noteq> z"
      by (metis nodeK)
  then show "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
      using * assms apply_inj_eq_iff apply_skip_perm perm.apply_perm_inverse pre_hypermap.select_convs(2) skip_edge_Perm skip_id u_noteq_z walkupE_def sorry
qed

lemma fcard_skip_edge:
  defines "Sez \<equiv> if z \<rightarrow>\<^bsub>glink H\<^esub> z 
                 then (if edge H z = z then 2 else 1) 
                 else (if cross_edge then 0 else 2)"
  shows "count_cycles_on (darts H') (edge H') + Sez = count_cycles_on (darts H) (edge H) + 1"
  apply (auto simp: Sez_def)
  using with_proj_simps(3) z_not_glink apply blast
  apply (metis Gr_eq arc_in_union cedge_def glink_def with_proj_simps(3) z_dart)
  apply (metis Gr_eq cedge_def cross_edge_def skip_edge_node skip_edge_noteq_z wf_cedge
      wf_digraph.reachable_adjI wf_digraph_wp_iff z_dart)
  using with_proj_simps(3) z_not_glink apply blast
  defer
  using with_proj_simps(3) z_not_glink apply blast
  sorry

end
subsection \<open>Degenerate walkup\<close>
text \<open>Degenerate case for walkup where one of the permutations is an identity on z\<close>

locale degenerate_walkup = walkup +
  assumes z_glink: "z\<rightarrow>\<^bsub>glink H\<^esub> z"
begin

lemma degenerate_euler:
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
        by (metis True H'_def node_perm_on.cycle_count_skip_singleton finite_darts
            pre_hypermap.select_convs(1) pre_hypermap.select_convs(3) walkupE_def z_dart)
    also have "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H') + 1"
        by (metis True H'_def face_perm_on.cycle_count_skip_singleton finite_darts
            pre_hypermap.select_convs(1) pre_hypermap.select_convs(4) walkupE_def z_dart)
    moreover have "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 1"
      by (metis True apply_skip_perm H'_def finite_darts glink_skip_edge perm.apply_perm_inverse
          perm_edge perm_on.cycle_count_skip_singleton perm_on.intro pre_hypermap.select_convs(1)
          pre_hypermap.select_convs(2) walkupE_def z_glink z_dart)
    ultimately show ?thesis
      by (simp add: euler_rhs_def)
  qed
  also have "euler_lhs H' = euler_lhs H - 3"
  proof -
    have "card (darts H') = card (darts H) - (1::int)" (is "?cdh' = ?cdh - 1")
      using card_darts_walkup int_ops(6) node_perm_on.finite_S z_dart by auto
    also have "int (card (pre_digraph.sccs (glink H'))) = int (card (pre_digraph.sccs (glink H))) - 1"
      (is "?scch' = ?scch - 1")
      sorry
    then have "?scch' * (2::int) + ?cdh' = ?scch * (2::int) + ?cdh - (3::int)"
      using calculation by fastforce
    then show ?thesis
      unfolding euler_lhs_def by presburger
  qed
  ultimately show ?thesis
    by (metis diff_diff_cancel euler_lhs_ge_3 euler_rhs_ge_3 insert_absorb insert_not_empty z_dart)
next
  case False
  then show ?thesis sorry
qed
end

subsection \<open>Not degenerate walkup\<close>
context not_degenerate_walkup begin

lemma walkup_node_cycle_count:
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
    by (simp add: H'_def walkupE_def)
qed

lemma walkup_face_cycle_count:
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
    by (simp add: H'_def walkupE_def)
qed

text \<open>cross_edge does not hold, so the edge cycles are merged and edge z is in the same edge cycle
      as node z\<close>

lemma not_cross_edge_Walkup:
  assumes "\<not> cross_edge"
  shows "edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>node H (face H z)"
  unfolding H'_def 
  sorry

lemma merge_walkup_path:
  assumes "\<not> cross_edge"
  shows "edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>node H z"
  by (metis Gr_eq Gr_verts H'_def assms cedge_def hypermap.cedge_connect_sym hypermap.perm_edge
      hypermap.wf_cedge hypermap_walkupE not_cross_edge_Walkup permutes_in_image reachable_in_vertsE
      skip_edge_Perm skip_edge_node walkup_edge wf_digraph.reach_sym_arc wf_digraph_wp_iff)

lemma merge_walkup_edge_cycles:
  assumes  "\<not> cross_edge"
  shows "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 1"
 sorry

lemma not_cross_edge_euler_lhs:
  assumes "\<not> cross_edge"
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
  assumes "cross_edge"
  shows "euler_rhs H = euler_rhs H' + 3"
proof -
  have "count_cycles_on (darts H) (face H) = count_cycles_on (darts H') (face H')"
    by (simp add: assms walkup_face_cycle_count)
  also have "count_cycles_on (darts H) (node H) = count_cycles_on (darts H') (node H')"
    by (simp add: assms walkup_node_cycle_count)
  moreover have "count_cycles_on (darts H) (edge H) = count_cycles_on (darts H') (edge H') + 3"
    oops

text \<open>cross_edge does not hold, so the edge cycle is split\<close>
lemma (in not_degenerate_walkup) cross_edge_walkup:
  assumes "cross_edge"
  shows "\<not>edge H z\<rightarrow>\<^sup>*\<^bsub>cedge (walkupE H z)\<^esub>node H (face H z)"
   using assms Gr_eq apply_inj_eq_iff apply_skip_perm arc_in_union cedge_def cface_def cnode_def
      glink_def perm.apply_perm_inverse perm_eq_iff pre_hypermap.select_convs(2) skip_edge_Perm 
      skip_id walkupE_def with_proj_simps(3) sorry
end

section \<open>Jordan and Euler\<close>
context walkup
begin

definition "n_comp_z disc \<equiv> if z\<rightarrow>\<^bsub>glink H\<^esub>z
                              then (if z_barb then 2 else 1)
                              else (if disc then 0 else 1)"
                                         
lemma euler_lhs_walkupE: "n_comp_z disconnected * 2 + euler_lhs H' = euler_lhs H + 1"
  apply (auto simp: n_comp_z_def)
  using disconnected_not_glink with_proj_simps(3) apply blast
  apply (simp add: disconnected_def walkup.z_barb_comp walkup_axioms)
  defer
  apply (metis Gr_eq arc_in_union cedge_def glink_def with_proj_simps(3) z_barb_z z_dart)
  using disconnected_not_glink apply auto
  sorry

lemma euler_rhs_walkupE: "n_comp_z disconnected * 2 + euler_rhs H' = euler_rhs H + 1"
  apply (auto simp: n_comp_z_def)
  using disconnected_not_glink with_proj_simps(3) apply blast
  apply (simp add: disconnected_def walkup.z_barb_comp walkup_axioms)
  defer
  apply (metis Gr_eq arc_in_union cedge_def glink_def with_proj_simps(3) z_barb_z z_dart)
  using disconnected_not_glink with_proj_simps(3) apply blast
  sorry

lemma genus_walkupE_eq: "z\<rightarrow>\<^bsub>glink H\<^esub>z \<or> \<not> cross_edge \<Longrightarrow> genus H' = genus H"
  apply auto
  sorry

lemma le_genus_walkupE: "genus H' \<le> genus H"
proof (cases "z\<rightarrow>\<^bsub>glink H\<^esub>z \<or> \<not> cross_edge")
  case True
  then show ?thesis using genus_walkupE_eq by force
next
  case False
  then have "\<not>z\<rightarrow>\<^bsub>glink H\<^esub>z \<and> cross_edge" by auto
  then have "disconnected" sorry
  then show ?thesis
    sorry
qed

lemma planar_walkupE: "planar H \<Longrightarrow> planar H'"
  by (metis bot.extremum_unique bot_nat_def le_genus_walkupE planar_def)

lemma even_genus_walkupE: "even (genus H') \<Longrightarrow> even (genus H)"
  sorry
  (*by (smt (verit) euler_lhs_walkupE euler_rhs_walkupE genus_def)*)

lemma Jordan_WalkupE: "jordan H \<Longrightarrow> jordan H'"
  sorry
end
end