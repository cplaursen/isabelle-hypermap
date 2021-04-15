theory Hypermap
  imports "Fun_Graph"
begin

section \<open>Hypermap\<close>

record 'a pre_hypermap =
  darts :: "'a set"
  edge :: "'a perm"
  node :: "'a perm"
  face :: "'a perm"

locale pre_hypermap =
  fixes H :: "'a pre_hypermap" (structure)

locale hypermap = pre_hypermap +
  assumes edgeK: "edge H (node H (face H x)) = x"
  and finite_darts: "finite (darts H)"
  and perm_edge: "edge H permutes darts H"
  and perm_node: "node H permutes darts H"
  and perm_face: "face H permutes darts H"
begin

text \<open>Basic properties of the functions\<close>
lemma nodeK: "\<And>x. node H (face H (edge H x)) = x"
  by (meson apply_inj_eq_iff edgeK)

lemma faceK: "\<And>x. face H (edge H (node H x)) = x"
  by (meson apply_inj_eq_iff nodeK)

lemma finite_perm_on_edge: "finite_perm_on (edge H) (darts H)"
  by (simp add: finite_darts finite_perm_on_axioms.intro finite_perm_on_def perm_edge perm_on.intro)

lemma finite_perm_on_node: "finite_perm_on (node H) (darts H)"
  by (simp add: finite_darts finite_perm_on_axioms.intro finite_perm_on_def perm_node perm_on.intro)

lemma finite_perm_on_face: "finite_perm_on (face H) (darts H)"
  by (simp add: finite_darts finite_perm_on_axioms.intro finite_perm_on_def perm_face perm_on.intro)
  
lemma darts_edge: "set_perm (edge H) \<subseteq> darts H"
  by (simp add: perm_edge perm_on.intro perm_on.set_perm_subset)

lemma darts_node: "set_perm (node H) \<subseteq> darts H"
  by (simp add: perm_node perm_on.intro perm_on.set_perm_subset)

lemma darts_face: "set_perm (face H) \<subseteq> darts H"
  by (simp add: perm_face perm_on.intro perm_on.set_perm_subset)

lemma edge_inv: "inv (edge H) = node H * face H"
  by (metis apply_perm_sequence inverse_perm.rep_eq nodeK perm_edge perm_eqI
      permutes_surj surj_iff_all)

lemma node_inv: "inv (node H) = face H * edge H"
  by (metis apply_perm_sequence inverse_perm.rep_eq faceK perm_node perm_eqI
      permutes_surj surj_iff_all)

lemma face_inv: "inv (face H) = edge H * node H"
  by (metis apply_perm_sequence inverse_perm.rep_eq edgeK perm_face perm_eqI
      permutes_surj surj_iff_all)
end

text \<open>Paths in the function graphs\<close>
definition cedge where
 "cedge h \<equiv> (Gr (darts h) (edge h))"

lemma (in hypermap) wf_cedge: "pair_wf_digraph (cedge H)"
  unfolding cedge_def by (simp add: perm_edge Gr_wf_perm)

definition cnode where
 "cnode h \<equiv> (Gr (darts h) (node h))"

lemma (in hypermap) wf_cnode: "pair_wf_digraph (cnode H)"
  unfolding cnode_def by (simp add: perm_node Gr_wf_perm wf_digraph_wp_iff)

definition cface where
  "cface h \<equiv> (Gr (darts h) (face h))"

lemma (in hypermap) wf_cface: "pair_wf_digraph (cface H)"
  unfolding cface_def by (simp add: perm_face Gr_wf_perm)

definition glink
  where "glink h = pair_union (cedge h) (pair_union (cnode h) (cface h))"

lemma (in hypermap) glink_wf: "pair_wf_digraph (glink H)"
  unfolding glink_def by (simp add: wf_cface wf_cnode wf_cedge wf_pair_union)

context hypermap begin
lemma cedge_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub> u "
  by (metis cedge_def perm_edge perm_on.intro perm_on.perm_reach_sym)

lemma cnode_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> u "
  by (metis cnode_def perm_node perm_on.intro perm_on.perm_reach_sym)

lemma cface_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> u "
  by (metis cface_def perm_face perm_on.intro perm_on.perm_reach_sym)


lemma glink_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> u"
proof -
  interpret pair_wf_digraph "glink H" by (simp add: glink_wf)
  assume "u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" then show ?thesis
  proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    then have "y = edge H x \<or> y = node H x \<or> y = face H x"
      by (metis glink_def Gr_eq cedge_def cface_def cnode_def pair_union_arcs_disj with_proj_simps(3))
    also have "y = edge H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub> x"
      by (metis cedge_reachable_sym Gr_eq Gr_wf cedge_def cface_def cnode_def glink_def local.step(2) pair_union_arcs_disj perm_edge permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3))
    moreover have "y = node H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x"
      by (metis cnode_reachable_sym Gr_eq Gr_wf cedge_def cface_def cnode_def glink_def local.step(2) pair_union_arcs_disj perm_node permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3))
    moreover have "y = face H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by (metis cface_reachable_sym Gr_eq Gr_wf cedge_def cface_def cnode_def glink_def local.step(2) pair_union_arcs_disj perm_face permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3))
    ultimately have "y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>x \<or> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x \<or> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by auto
    then have "y \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> x"
      unfolding glink_def by (metis (no_types, hide_lams) reach_in_union comm_pair_union
          with_proj_union Gr_wf cedge_def cface_def cnode_def compatibleI_with_proj perm_edge
          perm_face perm_node permutes_in_image wellformed_union wf_digraph_wp_iff)
    then show "y \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> u"
      by (meson reachable_trans step.hyps(3))
  qed
qed

definition connected_hypermap :: "'a pre_hypermap \<Rightarrow> bool" where
"connected_hypermap h \<equiv> strongly_connected (glink h)"
end

text \<open>All connected components are in the same equivalence class\<close>
section \<open>Genus\<close>
definition euler_rhs :: "'a pre_hypermap \<Rightarrow> nat" where
"euler_rhs h = count_cycles_on (darts h) (edge h) +
               count_cycles_on (darts h) (node h) +
               count_cycles_on (darts h) (face h)"

text \<open>Needed for subtraction on naturals\<close>
lemma (in hypermap) euler_rhs_ge_3: "darts H \<noteq> {} \<Longrightarrow> euler_rhs H \<ge> 3"
proof -
  assume "darts H \<noteq> {}"
  then have "count_cycles_on (darts H) (edge H) \<noteq> 0"
            "count_cycles_on (darts H) (node H) \<noteq> 0"
            "count_cycles_on (darts H) (face H) \<noteq> 0"
      using finite_perm_on.count_cycles_on_nonempty finite_perm_on_face finite_perm_on_node
        finite_perm_on_edge by blast+
    then show "euler_rhs H \<ge> 3"
      by (smt (verit, del_insts) add_leD2 add_le_same_cancel1 bot_nat_0.extremum_uniqueI
          euler_rhs_def le_SucE not_less_eq_eq numeral_3_eq_3)
qed

definition euler_lhs :: "'a pre_hypermap \<Rightarrow> nat" where
"euler_lhs h = card (pre_digraph.sccs (glink h)) * 2 + card (darts h)"

lemma (in hypermap) euler_lhs_ge_3: "darts H \<noteq> {} \<Longrightarrow> euler_lhs H \<ge> 3"
proof -
  interpret glink_gr: pre_digraph "glink H" .
  assume "darts H \<noteq> {}"
  then obtain x where "x \<in> darts H" by auto
  then have "pre_digraph.sccs (glink H) \<noteq> {}"
    sorry
  hence "card (pre_digraph.sccs (glink H)) \<ge> 1"
    using finite_darts sorry
  also have "card (darts H) \<ge> 1"
    by (meson \<open>darts H \<noteq> {}\<close> card_eq_0_iff finite_darts less_one not_less)
  ultimately show ?thesis
    unfolding euler_lhs_def by linarith
qed

definition genus where
"genus h \<equiv> (euler_lhs h - euler_rhs h) div 2"

definition planar where
"planar h \<equiv> genus h = 0"

section \<open>Jordan\<close>

definition clink where
"clink h \<equiv> pair_union (cface h) ((cnode h)\<^sup>R)"

context hypermap
begin

lemma wf_clink: "pair_wf_digraph (clink H)"
  unfolding clink_def by (simp add: wf_cface wf_cnode wf_reverse wf_pair_union)

lemma clinkP:
  assumes "x \<in> darts H" and "y \<in> darts H"
  shows "(y\<rightarrow>\<^bsub>cnode H\<^esub> x \<or> x \<rightarrow>\<^bsub>cface H\<^esub> y) \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub> y"
  unfolding clink_def by (meson arc_reverse pair_union_arcs_disj)

lemma clinkN: "x \<in> darts H \<Longrightarrow> node H x\<rightarrow>\<^bsub>clink H\<^esub>x"
  by (metis Gr_eq clinkP cnode_def perm_node permutes_in_image)

lemma clinkF: "x \<in> darts H \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub>face H x"
  by (metis Gr_eq cface_def hypermap.clinkP hypermap_axioms perm_face permutes_in_image)

text \<open>Copies the glink_rtrancl_sym proof\<close>
lemma clink_rtrancl_sym: "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub> u"
proof -
  interpret pair_wf_digraph "clink H" by (rule wf_clink)
  assume "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v" then show ?thesis
  proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    have "y = node H x \<Longrightarrow> x \<rightarrow>\<^sup>*\<^bsub>(cnode H)\<^sup>R\<^esub> y"
      using cnode_reachable_sym Gr_eq Gr_wf cface_def cnode_def local.step(2) pair_union_arcs_disj perm_node permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3) reach_reverse
      by (metis clink_def wf_reverse) 
    also have face_reach: "y = face H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      using cface_reachable_sym Gr_eq Gr_wf cface_def cnode_def local.step(2) pair_union_arcs_disj perm_face permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3)
      by (metis clink_def converse_iff pair_pre_digraph.simps(2) reverse_def)
    ultimately have "x \<rightarrow>\<^sup>*\<^bsub>(cnode H)\<^sup>R\<^esub> y \<or> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by (metis step.hyps(2) clink_def  Gr_eq Gr_wf cface_def cnode_def pair_union_arcs_disj perm_node permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff wf_reverse with_proj_simps(3))
    then have "y \<rightarrow>\<^sup>*\<^bsub>(clink H)\<^esub> x"
      using step.hyps(2) reach_in_union comm_pair_union
          with_proj_union Gr_wf cface_def cnode_def compatibleI_with_proj
          perm_face perm_node permutes_in_image wf_digraph_wp_iff wf_reverse
      by (metis (no_types, lifting) Gr_eq face_reach clink_def cnode_reachable_sym converse_iff
          pair_pre_digraph.simps(2) pair_union_arcs_disj reach_reverse reverse_def wf_digraph.reachable_adjI with_proj_simps(3))
    then show "y \<rightarrow>\<^sup>*\<^bsub>with_proj (clink H)\<^esub> u"
      by (meson step.hyps(3) reachable_trans)
  qed
qed

lemma clink_glink: "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
    sorry
next
  assume ?R then show ?L sorry
(*  have "u\<rightarrow>\<^bsub>glink H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v"
    proof
      fix z assume "z \<in> glink H"
      then obtain x y where "(x,y) = z" by (metis surj_pair)
      then have "y = edge H x \<or> y = node H x \<or> y = face H x"
        by (metis Gr_eq UnE \<open>z \<in> glink H\<close> glink_def)
      also have "y = edge H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        by (smt (verit, ccfv_SIG) clinkF clinkN clink_rtrancl_sym converse.intros darts_edge hypermap.nodeK hypermap_axioms in_mono in_set_permI perm_node permutes_in_image rtrancl.simps rtrancl_converse sym_conv_converse_eq)
      moreover have "y = node H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        by (metis apply_perm_eq_same_iff(2) clinkN clink_rtrancl_sym darts_node r_into_rtrancl rtrancl_eq_or_trancl subset_iff sym_def)
      moreover have "y = face H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        by (metis clinkF darts_edge darts_node faceK in_mono in_set_permI rtrancl.simps)
      ultimately show "z \<in> (clink H)\<^sup>*" using \<open>(x,y) = z\<close> by blast
    qed
    then show "u\<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v \<Longrightarrow> u\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v"
      by (rule rtrancl_subset_rtrancl)*)
qed                           

context begin
interpretation pair_wf_digraph "clink H" by (rule wf_clink)

lemma connected_clink:
  assumes "connected_hypermap H" "x \<in> (darts H)" "y \<in> (darts H)"
  shows "\<exists>p. apath x p y"
proof -
  from assms(1) have "x \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> y" using connected_hypermap_def assms strongly_connected_def
    by (metis (no_types, lifting) Gr_eq clinkP clink_glink cnode_def glink_wf perm_node permutes_in_image reachable_adjI wf_digraph.reachable_in_verts(2) wf_digraph_wp_iff with_proj_simps(3))
  then show ?thesis using clink_glink reachable_apath by simp
qed

definition appears_before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"appears_before p x y = (y \<in> set (dropWhile (\<lambda> z. z \<noteq> x) p))"

text \<open>A "Moebius path" is a contour that cannot appear in a planar map, as it goes from the inside
      of a ring to the outside\<close>

fun moebius_path :: "'a pre_hypermap \<Rightarrow> ('a\<times>'a) awalk  \<Rightarrow> bool" where
  "moebius_path _ [] = False"
| "moebius_path h p = (\<exists> x y. apath x p y \<and> 
            (\<exists>n. n\<rightarrow>\<^bsub>cnode h\<^esub>y \<and> appears_before (awalk_verts x p) n (node h (awhd x p))))"

definition jordan :: "'a pre_hypermap \<Rightarrow> bool" where
"jordan h = (\<forall>p. \<not> (moebius_path h p))"
end

end
end
