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
                  (if x = node h z then edge h z else
                  (if edge h x = z then edge h (node h z) else edge h x)))"

lemma skip_edge_id [simp]: "skip_edge z h z = z"
  unfolding skip_edge_def by simp

lemma skip_edge_noteq_z: "x \<noteq> z \<Longrightarrow> skip_edge z H x \<noteq> z"
  by (metis apply_inj_eq_iff skip_edge_def)

lemma (in hypermap) skip_edge_base:
  assumes "x \<noteq> z" "x \<noteq> node H (face H z)" "x \<noteq> node H z"
  shows "edge H x = skip_edge z H x"
  by (metis assms nodeK skip_edge_def)

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
    have "set_perm (node H) \<subseteq> darts H"
      by (simp add: perm_node perm_on.intro perm_on.set_perm_subset)
    then show "\<And>x. x \<notin> (A - {z}) \<Longrightarrow> skip_edge z H x = x"
      by (smt (z3) Diff_iff Permutations.permutes_not_in \<open>A = darts H\<close> apply_perm_image
          empty_iff imageI insert_iff perm_edge skip_edge_def)
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
      by (metis (no_types, lifting) Permutations.permutes_not_in
          faceK perm_edge perm_face skip_edge_def)
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

lemma (in hypermap) glink_fp_skip_edge: "z\<rightarrow>\<^bsub>glink H\<^esub>z \<Longrightarrow> skip_edge z H = skip z (edge H)"
proof
  fix x assume *: "z\<rightarrow>\<^bsub>glink H\<^esub>z"
  then have z_eq: "z = edge H z \<or> z = node H z \<or> z = face H z"
    unfolding glink_def cedge_def cnode_def cface_def by (metis Gr_eq pair_union_arcs_disj)
  have "z = edge H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    by (simp add: skip_def skip_edge_def)
  also have "z = node H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x"
    unfolding skip_edge_def skip_def using * nodeK by fastforce
  moreover have "z = face H z \<Longrightarrow> skip_edge z H x = skip z (edge H) x" 
    by (smt (z3) skip_edge_def skip_def * faceK edgeK nodeK)
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

theorem (in hypermap) hypermap_walkupE:
  shows "hypermap (walkupE H z)"
proof
  define H' where "H' \<equiv> walkupE H z"
  have "finite (darts H)" by (rule finite_darts)
  also have "darts H' = darts H - {z}"
    by (simp add: H'_def walkupE_def)
  ultimately show "finite (darts H')" by auto
  show "edge H' permutes darts H'"
    by (simp add: H'_def finite_darts hypermap_axioms permutes_perm skip_edge_permutes walkupE_def)
  show "node H' permutes darts H'"
    by (simp add: H'_def walkupE_def apply_skip_perm perm_node skip_permutes)
  show "face H' permutes darts H'"
    by (simp add: H'_def walkupE_def apply_skip_perm perm_face skip_permutes)
  fix x show "(edge H') \<langle>$\<rangle> (node H') \<langle>$\<rangle> (face H') \<langle>$\<rangle> x = x"
    by (simp add: H'_def skip_edgeK apply_skip_perm skip_edge_Perm walkupE_def)
qed

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

lemma walkup_darts_subset: "darts H' \<subseteq> darts H"
  unfolding H'_def walkupE_def by simp
end
(*
locale not_degenerate_walkup = walkup +
  assumes z_not_glink: "\<not>z\<rightarrow>\<^bsub>glink H\<^esub>z"
begin

lemma skip_edge_edge: "skip_edge z H (node H (face H z)) = (edge H (node H z))"
  by (smt (z3) Gr_eq arc_in_union cedge_def darts_permF edgeK faceK glink_def permF_def permF_glink
      pre_hypermap.select_convs(2) skip_edge_def z_dart z_not_glink)

lemma skip_edge_node: "skip_edge z H (node H z) = (edge H z)"
  unfolding skip_edge_def
  by (smt (z3) Gr_eq apply_perm_image cnode_def darts_face edgeK glink_def imageE
      pair_union_arcs_disj skip_edge_def skip_edge_edge z_dart z_not_glink)

lemma skip_edge_invariant:
  fixes x
  assumes "x \<noteq> z" "node H z \<noteq> x" "edge H x \<noteq> z"
  shows "skip_edge z H x = edge H x"
  unfolding skip_edge_def using assms by auto

lemma walkup_darts_subset: "darts H' \<subseteq> darts H"
  unfolding H'_def walkupE_def by simp
end
*)

context walkup 
begin
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

(*
lemma cross_edge_path_edge: "cross_edge \<longleftrightarrow> edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z"
  by (metis (no_types, hide_lams) Gr_eq cedge_connect_sym cedge_def cross_edge_def wf_cedge
      wf_digraph.connect_sym_def wf_digraph.reachable_adjI wf_digraph.reachable_trans 
      wf_digraph_wp_iff z_dart)*)

interpretation clink: fin_digraph "clink H"
  by (simp add: finite_clink)

definition z_comp where
"z_comp \<equiv> (clink H') \<restriction> (clink.scc_of z - {z})"

lemma wf_z_comp: "wf_digraph z_comp"
  by (simp add: H'_def hypermap.wf_clink hypermap_walkupE 
      wf_digraph.wellformed_induce_subgraph wf_digraph_wp_iff z_comp_def)

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
    by (metis H'_def fin_digraph.finite_arcs hypermap.finite_clink hypermap_walkupE rev_finite_subset)
    }
  ultimately show "fin_digraph_axioms z_comp"
    using fin_digraph_axioms.intro by blast
qed

definition z_barb where
"z_barb \<equiv> clink.scc_of z = {z}"

lemma z_barb_z: "z_barb = (edge H z = z \<and> node H z = z \<and> face H z = z)"
proof
  assume "z_barb"
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

lemma clink_at_H':
  assumes "u \<in> darts H'" "v \<in> darts H'"
  shows "u \<rightarrow>\<^bsub>clink H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^bsub>clink H'\<^esub>v"
proof -
  assume "u \<rightarrow>\<^bsub>clink H\<^esub>v"
  then have "(v\<rightarrow>\<^bsub>cnode H\<^esub> u \<or> u \<rightarrow>\<^bsub>cface H\<^esub> v)" (is "?N \<or> ?F")
    by (metis clink_def converse_iff pair_pre_digraph.simps(2) pair_union_arcs_disj
        reverse_def with_proj_simps(3))
  also have "v\<rightarrow>\<^bsub>cnode H\<^esub> u \<Longrightarrow> v\<rightarrow>\<^bsub>cnode H'\<^esub> u"
    by (metis DiffD2 Gr_eq H'_def apply_skip_perm assms cnode_def insertCI 
        pre_hypermap.select_convs(1) skip_invariant walkupE_def walkup_node)
  moreover have "u \<rightarrow>\<^bsub>cface H\<^esub> v \<Longrightarrow> u \<rightarrow>\<^bsub>cface H'\<^esub> v"
    by (metis DiffD2 Gr_eq H'_def apply_skip_perm assms(1) assms(2) cface_def 
        pre_hypermap.select_convs(1) singleton_iff skip_invariant walkupE_def walkup_face)
  ultimately show ?thesis
    by (metis H'_def hypermap.clinkP hypermap_walkupE)
qed

lemma clink_at_H:
  assumes "u \<in> darts H'" "v \<in> darts H'"
  shows "u \<rightarrow>\<^sup>*\<^bsub>clink H'\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v"
proof -
  interpret clink': wf_digraph "clink H'"
    by (simp add: H'_def hypermap.wf_clink hypermap_walkupE wf_digraph_wp_iff)
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
    then have "w \<in> darts H"
      using walkup_darts_subset by force
    then have "w \<in> verts (clink H)"
      using verts_clink by blast
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

lemma z_comp_clink: "x \<in> verts z_comp \<longleftrightarrow> (x\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>z \<and> x \<noteq> z)"
proof safe
  show "x \<in> verts z_comp \<Longrightarrow> x \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub> z"
    by (simp add: pre_digraph.scc_of_def z_comp_def)
  show "z \<in> verts z_comp \<Longrightarrow> x = z \<Longrightarrow> False"
    by (simp add: z_comp_def)
  then have "x \<in> clink.scc_of z" if "x\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>z"
    using clink.connect_sym_def clink.scc_of_def clink_connect_sym that by blast
  then show "x \<in> verts z_comp" if "x \<noteq> z" "x\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>z"
    by (simp add: that z_comp_def)
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

lemma not_cross_edge_Walkup:
  assumes "\<not> cross_edge" "edge H z \<in> darts H'"
  shows "edge H z\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>node H (face H z)"
proof -
  have "z \<noteq> edge H z"
    by (metis DiffD2 H'_def assms(2) insert_iff pre_hypermap.select_convs(1) walkupE_def)
  then obtain p0 where p0_def: "vpath p0 (cedge H) \<and> hd p0 = edge H z \<and> last p0 = z"
    by (metis Gr_eq cedge_connect_sym cedge_def wf_cedge wf_digraph.connect_sym_def
        wf_digraph.reachable_adjI wf_digraph.reachable_vpath_conv wf_digraph_wp_iff z_dart)
  then obtain p where p_def: "p0 = (p @ [z])"
    by (smt (verit, ccfv_threshold) \<open>z \<noteq> (edge H) \<langle>$\<rangle> z\<close> last.simps last_appendR list.sel(1) 
        neq_Nil_conv rev_exhaust vpathE vwalk_def)
  then have "hd p = edge H z"
    by (metis \<open>z \<noteq> (edge H) \<langle>$\<rangle> z\<close> hd_append list.sel(1) p0_def p_def)
  then have vpath_p: "vpath p (cedge H)"
    by (metis \<open>z \<noteq> (edge H) \<langle>$\<rangle> z\<close> hd_append list.sel(1) p0_def p_def vpath_sublist(1))
  then have cedge_p: "x \<in> set p \<Longrightarrow> x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>z" for x
  proof -
    assume "x \<in> set p"
    then obtain h q where "p = h @ (x#q)"
      by (meson split_list)
    then have "vpath (x#q) (cedge H)"
      using vpath_p vpath_sublist(2) by auto
    also have "last p\<rightarrow>\<^bsub>cedge H\<^esub> z"
      by (metis \<open>p = h @ x # q\<close> p_def p0_def append_is_Nil_conv insert_subset list.distinct(1)
          set_vwalk_arcs_snoc vpathE vwalk_def)
    then have "vpath (x#q@[z]) (cedge H)"
      using \<open>p = h @ x # q\<close> p0_def p_def vpath_sublist(2) by auto
    then show ?thesis
      by (metis append_is_Nil_conv last.simps last_snoc list.distinct(1) list.sel(1) wf_cedge
          wf_digraph.reachable_vpath_conv wf_digraph_wp_iff)
  qed
  then have "z \<notin> set p"
    using p_def p0_def vpath_def by auto
  have "edge H (last p) = z"
    by (metis p_def vpath_p p0_def Gr_eq cedge_def insert_subset set_vwalk_arcs_snoc vpathE vwalkE)
  then have "last p = (node H (face H z))"
    by (metis nodeK)
  also have "vpath p (cedge H')"
  proof (auto simp: vpath_def intro!: vwalkI)
    show x_vert: "x \<in> set p \<Longrightarrow> x \<in> pverts (cedge H')" for x
      by (metis Gr_verts H'_def \<open>z \<notin> set p\<close> cedge_def insert_Diff insert_iff
          pre_hypermap.select_convs(1) vpathE vpath_p vwalk_verts_in_verts walkupE_def
          with_proj_simps(1) z_dart)
    show "p = [] \<Longrightarrow> False" "distinct p"
      using vpath_p by blast+
    fix a b assume *: "(a,b) \<in> set (vwalk_arcs p)"
    then have "(a,b) \<in> parcs (cedge H)"
      by (metis in_mono vpathE vpath_p vwalkE with_proj_simps(3))
    then have "edge H a = b"
      by (simp add: cedge_def)
    also have "a \<noteq> node H (face H z)"
      by (metis * \<open>z \<notin> set p\<close> calculation edgeK in_set_vwalk_arcsE)
    moreover have "a \<noteq> z"
      by (metis * \<open>z \<notin> set p\<close> in_set_vwalk_arcsE)
    moreover have "a \<noteq> node H z"
      by (metis assms(1) cedge_p "*" cedge_connect_sym cross_edge_def in_set_vwalk_arcsE wf_cedge
          wf_digraph.connect_sym_def wf_digraph_wp_iff)
    ultimately have "edge H' a = b"
      using skip_edge_Perm skip_edge_base walkup_edge by force
    then show "(a,b) \<in> parcs (cedge H')"
      by (metis Gr_eq Gr_verts * \<open>\<And>x. x \<in> set p \<Longrightarrow> x \<in> pverts (cedge H')\<close> cedge_def 
          in_set_vwalk_arcsE with_proj_simps(1) with_proj_simps(3))
  qed
  ultimately show ?thesis
    by (metis H'_def \<open>hd p = (edge H) \<langle>$\<rangle> z\<close> hypermap.wf_cedge hypermap_walkupE
        wf_digraph.reachable_vpath_conv wf_digraph_wp_iff)
qed


definition "disconnected \<equiv> card (pre_digraph.sccs z_comp) > 1"

lemma disconnected_cross_edge: "disconnected \<Longrightarrow> \<not> z\<rightarrow>\<^bsub>glink H\<^esub>z \<and> cross_edge"
proof -
  assume *: "disconnected"
  {
    assume "\<not> (\<not> z\<rightarrow>\<^bsub>glink H\<^esub>z \<and> cross_edge)"
    then obtain x where "x\<rightarrow>\<^bsub>clink H\<^esub>z \<and> x \<noteq> z"
      by (metis "*" bot.extremum_strict bot_nat_def card.empty clinkN disconnected_def 
          hypermap.clinkF hypermap.faceK hypermap_axioms perm_face permutes_in_image
          walkup.z_barb_comp walkup.z_barb_z walkup.z_dart walkup_axioms)
    then have "x \<in> darts H'"
      by (metis H'_def fin_digraph.axioms(1) finite_clink insert_Diff insert_iff 
          pre_hypermap.select_convs(1) verts_clink walkupE_def wf_digraph.adj_in_verts(1) z_dart)
    then have "v \<in> darts H' \<Longrightarrow> v \<in> verts z_comp = (v\<rightarrow>\<^sup>*\<^bsub>clink H'\<^esub> x)" for v
      sorry
    then have "card (pre_digraph.sccs z_comp) = 1"
      sorry
  }
  then show ?thesis
    using "*" disconnected_def by force
qed

corollary not_cross_connected: "\<not> cross_edge \<Longrightarrow> \<not> disconnected"
  using disconnected_cross_edge by auto

definition "skip_edge_domain \<equiv> {x. x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>z \<or> x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>node H z}"

lemma eCedom: "x \<in> skip_edge_domain \<Longrightarrow> edge H x \<in> skip_edge_domain"
  apply (auto simp: skip_edge_domain_def)
  by (metis Gr_eq Gr_verts cedge_connect_sym cedge_def pre_digraph.converse_reachable_cases wf_cedge 
      wf_digraph.reach_sym_arc wf_digraph_wp_iff)+

lemma same_cskip_edge:
  assumes "u \<notin> skip_edge_domain" "u \<in> darts H'"
  shows "u\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<longleftrightarrow> u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
proof (cases "z\<rightarrow>\<^bsub>glink H\<^esub>z")
  case True
  then show ?thesis sorry
next
  case False
  have *: "((\<langle>$\<rangle>) (edge H')^^m) u = ((\<langle>$\<rangle>) (edge H)^^m) u" for m
  proof (induct m)
    case 0 then show ?case by simp
  next
    case (Suc m)
    then show ?case
      by (smt (verit, best) assms cedge_def funpow_simp_l in_mono mem_Collect_eq perm_edge
          perm_on.intro perm_on.reach_iff_funpow_perm skip_edge_Perm skip_edge_def
          skip_edge_domain_def walkup_darts_subset walkup_edge)
  qed
  then show ?thesis
    by (smt (verit) H'_def assms(2) cedge_def hypermap.perm_edge hypermap_walkupE *
     walkup_darts_subset perm_edge perm_on.intro perm_on.reach_iff_funpow_perm subsetD)
qed

lemma sub_cskip_edge:
  assumes "\<not> cross_edge" "u \<in> darts H'" "v \<in> darts H'"
  shows "u\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
  sorry

lemma cskip_edge_merge: 
  assumes "\<not> cross_edge" "u \<in> skip_edge_domain" "u \<in> darts H'" "v \<in> darts H'"
  shows "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v \<longleftrightarrow> v \<in> skip_edge_domain"
proof
  show "v \<in> skip_edge_domain" if "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
    sorry
  assume *: "v \<in> skip_edge_domain"
  have "node H (face H z) \<noteq> z"
    sorry
  then have "edge H z \<noteq> z"
    by (metis nodeK)
  then show "u\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>v"
    using assms sorry
qed


lemma fcard_skip_edge:
  defines "Sez \<equiv> if z \<rightarrow>\<^bsub>glink H\<^esub> z 
                 then (if edge H z = z then 2 else 1) 
                 else (if cross_edge then 0 else 2)"
  shows "count_cycles_on (darts H') (edge H') + Sez = count_cycles_on (darts H) (edge H) + 1"
proof (cases "z\<rightarrow>\<^bsub>glink H\<^esub>z")
  case True
  then show ?thesis
    apply (case_tac "edge H z = z")
    apply (auto simp add: Sez_def)
    by (smt (z3) H'_def Suc_eq_plus1 add.right_neutral True apply_perm_inject apply_skip_perm 
        finite_darts hypermap.glink_fp_skip_edge hypermap.skip_edge_Perm hypermap_axioms perm_edge
        perm_on.cycle_count_skip perm_on.intro pre_hypermap.select_convs(1) walkupE_def 
        walkup_edge z_dart)+
next
  case False
  then have neq_z: "edge H z \<noteq> z \<and> node H z \<noteq> z \<and> face H z \<noteq> z \<and> node H (face H z) \<noteq> z"
    by (metis Gr_eq arc_clink cedge_def clinkP edgeK glink_def pair_union_arcs_disj z_dart)
  interpret H': hypermap "H'"
    by (simp add: H'_def hypermap_walkupE)
  have eCG: "x\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>x" for x y
    using cedge_connect_sym wf_cedge wf_digraph.connect_sym_def wf_digraph_wp_iff by blast
  have eCG': "x\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>cedge H'\<^esub>x" for x y
    using H'.cedge_connect_sym H'.wf_cedge wf_digraph.connect_sym_def wf_digraph_wp_iff by blast
  then show ?thesis sorry
qed

section \<open>Jordan and Euler\<close>

definition "n_comp_z disc \<equiv> if z\<rightarrow>\<^bsub>glink H\<^esub>z
                              then (if z_barb then 2 else 1)
                              else (if disc then 0 else 1)"

lemma n_comp_glink_Walkup: "n_comp_z disconnected + card (pre_digraph.sccs (glink H'))
                          = card (pre_digraph.sccs (glink H)) + 1"
  sorry

lemma euler_lhs_walkupE: "n_comp_z disconnected * 2 + euler_lhs H' = euler_lhs H + 1"
  apply (simp add: euler_lhs_def)
  by (metis One_nat_def Suc_pred add_2_eq_Suc add_Suc_right card_darts_walkup card_gt_0_iff
      empty_iff finite_darts left_add_mult_distrib mult_2_right n_comp_glink_Walkup nat_1_add_1 z_dart)

lemma genus_walkupE_eq: "z\<rightarrow>\<^bsub>glink H\<^esub>z \<or> \<not> cross_edge \<Longrightarrow> genus H' = genus H"
  sorry

lemma le_genus_walkupE: "genus H' \<le> genus H"
proof (cases "z\<rightarrow>\<^bsub>glink H\<^esub>z \<or> \<not> cross_edge")
  case True
  then show ?thesis using genus_walkupE_eq by force
next
  case False
  have "count_cycles_on (darts H') (edge H') = count_cycles_on (darts H) (edge H) + 1"
    using fcard_skip_edge False by presburger
  moreover have "count_cycles_on (darts H') (node H') = count_cycles_on (darts H) (node H)"
    by (smt (z3) False H'_def add.right_neutral arc_clink clinkP finite_darts glink_def 
        pair_union_arcs_disj perm_node perm_on.cycle_count_skip perm_on.intro 
        pre_hypermap.select_convs(1) pre_hypermap.select_convs(3) walkupE_def z_dart)
  moreover have "count_cycles_on (darts H') (face H') = count_cycles_on (darts H) (face H)"
    by (smt (z3) False H'_def add.right_neutral arc_clink clinkP finite_darts glink_def
        pair_union_arcs_disj perm_face perm_on.cycle_count_skip perm_on.intro
        pre_hypermap.select_convs(1) walkupE_def walkup_face z_dart)
  ultimately have rhs_h': "euler_rhs H' = euler_rhs H + 1"
    by (simp add: euler_rhs_def)
  then consider (disconnected) "disconnected" | (connected) "\<not> disconnected" by auto
  then show ?thesis
  proof cases
    case disconnected
    then have "card (pre_digraph.sccs (glink H')) = card (pre_digraph.sccs (glink H)) + 1"
      by (metis False n_comp_glink_Walkup add.commute add.right_neutral n_comp_z_def)
    then have "euler_lhs H' = euler_lhs H + 1"
      by (metis False \<open>disconnected\<close> add.commute add.right_neutral
          euler_lhs_walkupE mult_2_right n_comp_z_def)
    then show ?thesis
      by (simp add: genus_def rhs_h')
  next
    case connected
    then have "card (pre_digraph.sccs (glink H')) = card (pre_digraph.sccs (glink H))"
      by (metis False add.commute add_right_imp_eq n_comp_glink_Walkup n_comp_z_def)
    then have "euler_lhs H' + 1 = euler_lhs H"
      using euler_lhs_walkupE n_comp_glink_Walkup by auto
    then show ?thesis
      by (simp add: genus_def rhs_h')
  qed
qed

lemma planar_walkupE: "planar H \<Longrightarrow> planar H'"
  by (metis bot.extremum_unique bot_nat_def le_genus_walkupE planar_def)

lemma even_genus_walkupE: "even (genus H') \<Longrightarrow> even (genus H)"
sorry


lemma Jordan_WalkupE: "jordan \<Longrightarrow> hypermap.jordan H'"
proof -
  assume assm: "jordan"
  obtain t where "node H t = z"
      using nodeK by blast
  then have "z\<rightarrow>\<^bsub>clink H\<^esub>t"
    by (simp add: parcs_clink z_dart)
  define clink1 where "clink1 \<equiv> pair_union (Gr (darts H') (skip_perm z (face H))) ((cnode H)\<^sup>R)"
  then have clink1_verts: "verts clink1 = darts H"
    by (metis (no_types, hide_lams) walkup_darts_subset pair_union_def  Gr_verts Un_iff cnode_def 
        pair_pre_digraph.select_convs(1) reverse_def subset_antisym subset_iff with_proj_simps(1))
  have cpath1I: "x \<noteq> z \<Longrightarrow> vwalk (x#p) (clink H') \<Longrightarrow> t \<notin> set p \<Longrightarrow> vwalk (x#p) clink1" for x p
  proof (rule vwalkI; safe)
    assume *: "x \<noteq> z" "vwalk (x # p) (clink H')" "t \<notin> set p"
    show in_verts: "xa \<in> set (x # p) \<Longrightarrow> xa \<in> verts (with_proj clink1)" for xa
      by (metis *(2) H'_def clink1_verts hypermap.hypermap_walkupE hypermap.verts_clink
          hypermap_axioms subsetD vwalkE walkup_darts_subset with_proj_simps(1))
    show "(a, b) \<in> set (vwalk_arcs (x # p)) \<Longrightarrow> a \<rightarrow>\<^bsub>clink1\<^esub> b" for a b
    proof -
      assume "(a, b) \<in> set (vwalk_arcs (x # p))"
      have "a \<noteq> z \<and> b \<noteq> z"
        by (metis "*"(2) DiffE H'_def \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close> hypermap.hypermap_walkupE 
            hypermap.verts_clink hypermap_axioms in_set_vwalk_arcsE pre_hypermap.select_convs(1)
            singletonI vwalk_verts_in_verts walkupE_def)
      have "b \<noteq> t"
        by (smt (verit, best) *(3) Pair_inject \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close> 
            in_set_vwalk_arcsE list.distinct(1) list.inject list.set_cases list.set_intros(1)
            vwalk_arcs.elims)
      have "face H' a = b \<or> node H' b = a"
        by (metis (no_types, lifting) "*"(2) H'_def \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close> 
            hypermap.arc_clink hypermap.hypermap_walkupE hypermap.verts_clink hypermap_axioms 
            in_set_vwalk_arcsE subsetD vwalkE)
      moreover have "face H' a = b \<Longrightarrow> (a,b) \<in> parcs clink1"
        by (metis (no_types, lifting) *(2) Gr_eq H'_def \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close>
            arc_in_union clink1_def hypermap.hypermap_walkupE hypermap.verts_clink hypermap_axioms
            in_mono in_set_vwalk_arcsE vwalkE walkup_face with_proj_simps(3))
      moreover have "node H' b = a \<Longrightarrow> node H b = a"
        by (metis \<open>(node H) \<langle>$\<rangle> t = z\<close> \<open>a \<noteq> z \<and> b \<noteq> z\<close> \<open>b \<noteq> t\<close> faceK skip_perm_invariant walkup_node)
      ultimately show ?thesis
        by (smt (z3) "*"(2) Gr_eq H'_def \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close> \<open>a \<noteq> z \<and> b \<noteq> z\<close>
            arc_clink arc_reverse cface_def clink1_def clinkP hypermap.hypermap_walkupE 
            hypermap.verts_clink hypermap_axioms in_mono in_set_vwalk_arcsE pair_union_arcs_disj 
            skip_perm_invariant vwalkE walkup_darts_subset with_proj_simps(3))
    qed
  qed    
  have cpathI: "x \<noteq> z \<Longrightarrow> vwalk (x#p) clink1 \<Longrightarrow> face H z \<notin> set p \<Longrightarrow> vwalk (x#p) (clink H)" for x p
  proof (rule vwalkI; safe)
    assume *: "x \<noteq> z" "vwalk (x # p) clink1" "face H z \<notin> set p"
    show in_verts: "xa \<in> set (x # p) \<Longrightarrow> xa \<in> verts (clink H)" for xa
      by (metis *(2) clink1_verts hypermap.verts_clink 
          hypermap_axioms subsetD vwalkE with_proj_simps(1))
    show "(a, b) \<in> set (vwalk_arcs (x # p)) \<Longrightarrow> a \<rightarrow>\<^bsub>clink H\<^esub> b" for a b
    proof -
      assume arc: "(a, b) \<in> set (vwalk_arcs (x # p))"
      have "b \<noteq> face H z"
        by (smt (verit, best) *(3) Pair_inject \<open>(a, b) \<in> set (vwalk_arcs (x # p))\<close> 
            in_set_vwalk_arcsE list.distinct(1) list.inject list.set_cases list.set_intros(1)
            vwalk_arcs.elims)
      have "a\<rightarrow>\<^bsub>(Gr (darts H') (skip_perm z (face H)))\<^esub>b \<or> a\<rightarrow>\<^bsub>(cnode H)\<^sup>R\<^esub>b"
        by (metis (no_types, lifting) arc *(2) clink1_def in_mono pair_union_arcs_disj vwalkE)
      moreover have "a\<rightarrow>\<^bsub>(cnode H)\<^sup>R\<^esub>b \<Longrightarrow> (a,b) \<in> parcs (clink H)"
        by (metis clink_def pair_union_arcs_disj with_proj_simps(3))
      moreover have "a\<rightarrow>\<^bsub>(Gr (darts H') (skip_perm z (face H)))\<^esub>b \<Longrightarrow> (a,b) \<in> parcs (clink H)"
        by (metis DiffE Gr_eq H'_def \<open>b \<noteq> (face H) \<langle>$\<rangle> z\<close> apply_skip_perm hypermap.arc_clink 
            hypermap_axioms pre_hypermap.select_convs(1) singletonI skip_fz skip_perm_invariant
            walkupE_def with_proj_simps(3))
      ultimately show ?thesis
        using with_proj_simps(3) by blast
    qed
  qed    
  have cpath1P: "x \<noteq> z \<Longrightarrow> vwalk (x#p) clink1 \<Longrightarrow> \<not> vwalk (x#p) (clink H) \<Longrightarrow> distinct p \<Longrightarrow>
              \<exists> p1 p2. face H z \<in> set p \<and> p = p1 @ p2 \<and> last (z#p2) = last (x#p) \<and> 
    vwalk (x#p1@[z]) (clink H) \<and> vwalk (z#p2) (clink H)" for p x
    sorry
  {
    assume *: "\<not> hypermap.jordan H'"
    then obtain p where p_def: "hypermap.moebius_path H' p"
      using H'_def hypermap.jordan_def hypermap_walkupE by auto
    then obtain x q where "p = x#q"
      by (metis H'_def hypermap.moebius_path.simps(1) hypermap_walkupE neq_Nil_conv)
    then obtain y where "node H' y = last p"
      by (meson eq_apply_perm_inverse_iff)
    from this p_def have moebius_p: "appears_before q y (node H' x)" "vpath p (clink H')"
      apply (smt (z3) \<open>p = x # q\<close> H'_def hypermap.faceK last_ConsR
         hypermap.moebius_path.elims(1) hypermap.moebius_path.simps(2) hypermap_walkupE list.inject)
      using H'_def hypermap.moebius_path.elims(2) hypermap_walkupE p_def by auto
    then have Lp: "last p = (if y = t then node H z else node H y)"
      by (metis DiffE H'_def \<open>(node H') \<langle>$\<rangle> y = last p\<close> \<open>(node H) \<langle>$\<rangle> t = z\<close> apply_inj_eq_iff 
          apply_skip_perm hypermap.verts_clink hypermap_walkupE in_mono last_in_set 
          pre_hypermap.select_convs(1) singletonI skip_fz skip_id skip_perm_invariant vpathE 
          vwalkE walkupE_def walkup_node)
    have pynx: "appears_before q y (if x = t then node H z else node H x)"
      by (smt (z3) H'_def \<open>(node H) \<langle>$\<rangle> t = z\<close> \<open>p = x # q\<close> appears_before_in(2) apply_inj_eq_iff
          apply_skip_perm distinct.simps(2) hypermap.moebius_path.elims(2) hypermap_walkupE
          moebius_p(1) p_def skip_fz skip_id skip_perm_invariant vpathE walkup_node)
    have "z \<notin> set p"
      by (metis Diff_insert_absorb H'_def hypermap.hypermap_walkupE hypermap.verts_clink
          hypermap_axioms mk_disjoint_insert moebius_p(2) pre_hypermap.select_convs(1) vpathE 
          vwalk_verts_in_verts walkupE_def z_dart)
    then have "distinct (z#p)"
      using moebius_p(2) by auto
    have "x \<noteq> y"
      by (metis \<open>p = x # q\<close> appears_before_in(1) distinct.simps(2) moebius_p vpathE)
    have "\<not> vwalk p (clink H)"
    proof
      assume "vwalk p (clink H)"
      then have "vpath p (clink H)"
        using moebius_p by blast
      consider (x) "x = t \<and> y \<noteq> t" | (y) "x \<noteq> t \<and> y = t" | (neither) "x \<noteq> t \<and> y \<noteq> t"
        using \<open>x \<noteq> y\<close> by auto
      then have "\<exists>p. moebius_path p"
      proof cases
        case x
        then have "appears_before q y (node H z)"
          using pynx by auto
        also have "vpath (z#p) (clink H)"
          by (metis \<open>distinct (z # p)\<close> \<open>p = x # q\<close> \<open>vwalk p (clink H)\<close> \<open>z \<rightarrow>\<^bsub>with_proj (clink H)\<^esub> t\<close>
              vpathI wf_clink wf_digraph.vwalk_Cons_Cons wf_digraph_wp_iff x)
        ultimately have "moebius_path (z#p)"
          by (metis Lp \<open>p = x # q\<close> appears_before_cons faceK moebius_path.simps(3) x)
        then show ?thesis by blast
      next
        case y
        then have "last p = node H z"
          by (meson Lp)
        then have "vpath (p@[z]) (clink H)"
          using \<open>vpath p (clink H)\<close> \<open>z \<notin> set p\<close> clinkN disjoint_insert(1) 
            distinct_append distinct_singleton insert_subset list.simps(15) set_vwalk_arcs_snoc
            verts_clink vpath_def vwalk_def walkup.z_dart walkup_axioms by fastforce
        also have "appears_before q y (node H x)"
          using pynx y by auto
        then have "appears_before (q@[z]) y (node H x)"
          by (simp add: appears_before_append)
        ultimately have "moebius_path (p@[z])"
          by (smt (verit, del_insts) \<open>(node H) \<langle>$\<rangle> t = z\<close> \<open>p = x # q\<close> append_Cons 
              append_is_Nil_conv hypermap.faceK hypermap.moebius_path.elims(1) hypermap_axioms
              last_snoc list.distinct(1) list.inject y)
        then show ?thesis by auto
      next
        case neither
        then have "moebius_path p"
          by (smt (z3) H'_def Lp \<open>p = x # q\<close> \<open>vpath p (clink H)\<close> \<open>vwalk p (clink H)\<close> hypermap.faceK
              hypermap.moebius_path.elims(1) hypermap.moebius_path.simps(2) hypermap_axioms
              hypermap_walkupE last_ConsR list.inject p_def pynx vwalk_def)
        then show ?thesis by auto
      qed
      then show False
        using assm jordan_def by auto
    qed

    have "\<not>vwalk p clink1"
      sorry

    then have "t \<in> set p"
      using \<open>distinct (z # p)\<close> \<open>p = x # q\<close> cpath1I moebius_p(2) by auto

    then have "appears_before q y (node H x)"
      by (metis (mono_tags, hide_lams) \<open>\<not> vwalk p (with_proj clink1)\<close> \<open>p = x # q\<close> 
          cpath1I distinct.simps(2) moebius_p(2) pynx vpathE)

    obtain p1 p2 where p12_def: "p1 @ (t#p2) = q"
      by (metis \<open>\<not> vwalk p clink1\<close> \<open>distinct (z # p)\<close> \<open>p = x # q\<close> cpath1I 
          distinct_length_2_or_more moebius_p(2) split_list vpathE)
    then have "set p1 \<inter> set p2 = {}"
      using \<open>distinct (z # p)\<close> \<open>p = x # q\<close> by force
    have "vpath (t#p2) clink1"
      by (metis \<open>p = x # q\<close> \<open>t \<in> set p\<close> \<open>z \<notin> set p\<close> append_is_Nil_conv cpath1I distinct.simps(2)
        distinct_append list.distinct(1) moebius_p(2) vpath_def vwalkI_append_r vwalk_consE p12_def)
    have "vpath (x#p1) clink1"
      unfolding vpath_def apply auto
        apply (rule cpath1I)
          using \<open>p = x # q\<close> \<open>z \<notin> set p\<close> apply force
          apply (metis \<open>p = x # q\<close> p12_def moebius_p(2) append_Cons
                       list.discI vpath_def vwalkI_append_l)
          using \<open>distinct (z # p)\<close> \<open>p = x # q\<close> \<open>p1 @ t # p2 = q\<close> apply fastforce+
    done
    have Lp1: "last (x#p1) = node H z"
      sorry
    have Lp2: "last (t#p2) = node H y \<and> y \<noteq> t"
      by (metis Lp Lp1 \<open>p = x # q\<close> append_is_Nil_conv disjoint_insert(1) distinct.simps(2) 
          distinct_append insert_Diff last.simps last_appendR last_in_set list.distinct(1) 
          moebius_p(2) p12_def vpathE)
    have xCp1: "vpath (x#p1) (clink H)"
      sorry

    have "\<not> vpath (t#p2) (clink H)"
    proof
      assume "vpath (t # p2) (clink H)"
      then have "vpath (z#t#p2) (clink H)"
        by (metis Un_iff \<open>distinct (z # p)\<close> \<open>p = x # q\<close> \<open>z \<rightarrow>\<^bsub>with_proj (clink H)\<^esub> t\<close>
            distinct.simps(2) distinct_length_2_or_more fin_digraph.axioms(1) finite_clink p12_def 
            set_append vpath_def wf_digraph.vwalk_Cons_Cons)
      also have "vwalk (x#p1@[z]) (clink H)"
        by (smt (verit, ccfv_threshold) Lp1 xCp1 Un_insert_right append_Cons append_Nil2 clinkN 
            insert_subset list.distinct(1) list.simps(15) set_append set_vwalk_arcs_snoc
            verts_clink vpathE vwalk_def walkup.z_dart walkup_axioms)
      ultimately have "vpath (x#p1@(z#t#p2)) (clink H)"
        sorry
      then have "moebius_path (x#p1@(z#t#p2))"
        sorry
      then show False
        using assm jordan_def by blast
    qed
    obtain q1 q2 where "p2 = q1 @ q2"
      by blast

    have "y \<notin> set (t # q1)"
      sorry

    have "node H x \<in> set (t # q1)"
      sorry

    have "y \<in> set p1"
      sorry

    then have False
      sorry
  }
    then show ?thesis
      by blast
qed

end

section \<open>Other walkups\<close>


definition "walkupN H z \<equiv> permF (walkupE (permN H) z)"

definition "walkupF H z \<equiv> permN (walkupE (permF H) z)"

definition skip_node where
"skip_node z h x \<equiv> if z = x then z else
                  (if (node h z) = z then node h x else
                  (if x = face h z then node h z else
                  (if node h x = z then node h (face h z) else node h x)))"

definition skip_face where
"skip_face z h x \<equiv> if z = x then z else
                  (if (face h z) = z then face h x else
                  (if x = edge h z then face h z else
                  (if face h x = z then face h (edge h z) else face h x)))"

context walkup begin

lemma darts_walkupN: "darts (walkupN H z) = darts H - {z}"
  by (simp add: permF_def permN_def walkupE_def walkupN_def)

lemma darts_walkupF: "darts (walkupF H z) = darts H - {z}"
  by (simp add: permF_def permN_def walkupE_def walkupF_def)

lemma card_walkupN: "card (darts (walkupN H z)) = card (darts H) - 1"
  by (simp add: darts_walkupN finite_darts z_dart)

lemma card_walkupF: "card (darts (walkupF H z)) = card (darts H) - 1"
  by (simp add: darts_walkupF finite_darts z_dart)

lemma edge_walkupN: "edge (walkupN H z) = skip_perm z (edge H)"
  by (simp add: permF_def permN_def walkupE_def walkupN_def)

lemma node_walkupN: "node (walkupN H z) x = skip_node z H x"
  by (smt (z3) hypermap.skip_edge_Perm hypermap_permN permF_def permN_def 
      pre_hypermap.select_convs(2) pre_hypermap.select_convs(3) skip_edge_def 
      skip_node_def walkupE_def walkupN_def)

lemma face_walkupN: "face (walkupN H z) = skip_perm z (face H)"
  by (simp add: permF_def permN_def walkupE_def walkupN_def)

lemma edge_walkupF: "edge (walkupF H z) = skip_perm z (edge H)"
  by (simp add: permF_def permN_def walkupE_def walkupF_def)

lemma node_walkupF: "node (walkupF H z) = skip_perm z (node H)"
  by (simp add: permF_def permN_def walkupE_def walkupF_def)

lemma face_walkupF: "face (walkupF H z) x = skip_face z H x"
  by (smt (z3) hypermap.skip_edge_Perm hypermap_permF permF_def permN_def 
      pre_hypermap.select_convs(2) pre_hypermap.select_convs(3) pre_hypermap.select_convs(4)
      skip_edge_def skip_face_def walkupE_def walkupF_def)

lemma planar_walkupN: "planar H \<Longrightarrow> planar (walkupN H z)"
proof -
  assume *: "planar H"
  then have "planar (walkupE (permN H) z)"
    by (metis hypermap_permN permN_def planar_permN pre_hypermap.select_convs(1) walkup.H'_def
        walkup.planar_walkupE walkup_axioms.intro walkup_def z_dart)
  then show ?thesis
    by (simp add: hypermap.genus_permF hypermap.hypermap_walkupE hypermap_permN planar_def walkupN_def)
qed

lemma planar_walkupF: "planar H \<Longrightarrow> planar (walkupF H z)"
proof -
  assume *: "planar H"
  then have "planar (walkupE (permF H) z)"
    by (metis hypermap_permF permF_def planar_permF pre_hypermap.select_convs(1) walkup.H'_def
        walkup.planar_walkupE walkup_axioms.intro walkup_def z_dart)
  then show ?thesis
    by (simp add: hypermap.genus_permN hypermap.hypermap_walkupE
        hypermap_permF planar_def walkupF_def)
qed

end

end