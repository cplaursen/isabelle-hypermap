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
lemma nodeK: "node H (face H (edge H x)) = x"
  by (meson apply_inj_eq_iff edgeK)

lemma faceK: "face H (edge H (node H x)) = x"
  by (meson apply_inj_eq_iff nodeK)

lemma edge_inv: "inv (edge H) = node H * face H"
  by (metis apply_perm_sequence inverse_perm.rep_eq nodeK perm_edge perm_eqI
      permutes_surj surj_iff_all)

lemma node_inv: "inv (node H) = face H * edge H"
  by (metis Perm.apply_perm_inverse apply_perm_sequence faceK perm_eq_iff 
      perm_node permutes_surj surj_iff_all)

lemma face_inv: "inv (face H) = edge H * node H"
  by (metis apply_perm_sequence inverse_perm.rep_eq edgeK perm_face perm_eqI
      permutes_surj surj_iff_all)
end

text \<open>Paths in the function graphs\<close>
definition cedge where
 "cedge h \<equiv> (Gr (darts h) (edge h))"

lemma (in hypermap) wf_cedge: "pair_wf_digraph (cedge H)"
  unfolding cedge_def by (simp add: perm_edge Gr_wf_perm)

lemma cedge_eq: "x \<in> darts h \<Longrightarrow> x\<rightarrow>\<^bsub>cedge h\<^esub>y \<longleftrightarrow> (edge h x = y)"
  by (metis Gr_eq cedge_def)

definition cnode where
 "cnode h \<equiv> (Gr (darts h) (node h))"

lemma (in hypermap) wf_cnode: "pair_wf_digraph (cnode H)"
  unfolding cnode_def by (simp add: perm_node Gr_wf_perm wf_digraph_wp_iff)

lemma cnode_eq: "x \<in> darts h \<Longrightarrow> x\<rightarrow>\<^bsub>cnode h\<^esub>y \<longleftrightarrow> (node h x = y)"
  by (metis Gr_eq cnode_def)

definition cface where
  "cface h \<equiv> (Gr (darts h) (face h))"

lemma (in hypermap) wf_cface: "pair_wf_digraph (cface H)"
  unfolding cface_def by (simp add: perm_face Gr_wf_perm)

lemma cface_eq: "x \<in> darts H \<Longrightarrow> x\<rightarrow>\<^bsub>cface H\<^esub>y \<longleftrightarrow> (face H x = y)"
  by (metis Gr_eq cface_def)

definition glink
  where "glink h = pair_union (cedge h) (pair_union (cnode h) (cface h))"

lemma (in hypermap) wf_glink: "pair_wf_digraph (glink H)"
  unfolding glink_def by (simp add: wf_cface wf_cnode wf_cedge wf_pair_union)

lemma verts_glink: "verts (glink H) = darts H"
  by (simp add: cedge_def cface_def cnode_def glink_def)

lemma (in hypermap) glink_enf:
  assumes "x \<in> darts H"
  shows "x\<rightarrow>\<^bsub>glink H\<^esub>y \<longleftrightarrow> edge H x = y \<or> node H x = y \<or> face H x = y" 
  apply (rule iffI)
   apply (metis Gr_eq assms cedge_eq cface_def cnode_def glink_def pair_union_arcs_disj)
  by (metis assms cedge_eq cface_eq cnode_eq glink_def pair_union_arcs_disj)

context hypermap begin
lemma cedge_connect_sym: "wf_digraph.connect_sym (cedge H)"
  by (metis cedge_def perm_edge perm_on.intro perm_on.perm_connect_sym)

lemma cnode_connect_sym: "wf_digraph.connect_sym (cnode H)"
  by (metis cnode_def perm_node perm_on.intro perm_on.perm_connect_sym)

lemma cface_connect_sym: "wf_digraph.connect_sym (cface H)"
  by (metis cface_def perm_face perm_on.intro perm_on.perm_connect_sym)

lemma glink_connect_sym: "wf_digraph.connect_sym (glink H)"
proof -
  interpret pair_wf_digraph "glink H" by (simp add: wf_glink)
  have "v \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>u" if "u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" for u v
  using that proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    then have "y = edge H x \<or> y = node H x \<or> y = face H x"
      by (metis glink_def Gr_eq cedge_def cface_def cnode_def pair_union_arcs_disj with_proj_simps(3))
    also have "(y = edge H x \<longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub> x) \<and>
               (y = node H x \<longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x) \<and>
               (y = face H x \<longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x)"
      by (metis Gr_eq cedge_connect_sym cnode_connect_sym cface_connect_sym cedge_def cface_def
          cnode_def glink_def pair_union_arcs_disj step.hyps(2) wf_cedge wf_cnode wf_cface 
          wf_digraph.reach_sym_arc wf_digraph_wp_iff with_proj_simps(3))
    ultimately have "y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>x \<or> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x \<or> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by fastforce
    then have "y \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> x"
      unfolding glink_def by (metis (no_types, hide_lams) reach_in_union comm_pair_union
          with_proj_union Gr_wf cedge_def cface_def cnode_def compatibleI_with_proj perm_edge
          perm_face perm_node permutes_in_image wellformed_union wf_digraph_wp_iff)
    then show "y \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> u"
      by (meson reachable_trans step.hyps(3))
  qed
  then show ?thesis unfolding connect_sym_def by blast
qed

definition "connected_hypermap \<equiv> strongly_connected (glink H)"
end

text \<open>All connected components are in the same equivalence class\<close>
section \<open>Genus\<close>
definition euler_rhs :: "'a pre_hypermap \<Rightarrow> nat" where
"euler_rhs h = count_cycles_on (darts h) (edge h) +
               count_cycles_on (darts h) (node h) +
               count_cycles_on (darts h) (face h)"

definition euler_lhs :: "'a pre_hypermap \<Rightarrow> nat" where
"euler_lhs h = card (pre_digraph.sccs (glink h)) * 2 + card (darts h)"

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
  by (simp add: clink_def pair_wf_digraph.wf_reverse wf_cface wf_cnode wf_pair_union)

lemma finite_clink: "fin_digraph (clink H)"
  apply (auto simp add: fin_digraph_def wf_clink wf_digraph_wp_iff)
  by (simp add: cface_def clink_def cnode_def fin_digraph_axioms_def finite_darts 
      perm_node perm_on.Gr_reverse_eq_inv perm_on.intro)

lemma verts_clink [simp]: "verts (clink H) = darts H"
  by (simp add: cface_def clink_def cnode_def perm_node perm_on.Gr_reverse_eq_inv perm_on.intro)

lemma clinkP: "(y\<rightarrow>\<^bsub>cnode H\<^esub> x \<or> x \<rightarrow>\<^bsub>cface H\<^esub> y) \<longleftrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub> y"
  unfolding clink_def apply (rule iffI)
   apply (meson arc_reverse pair_union_arcs_disj)
  by (metis converse_iff pair_pre_digraph.select_convs(2) 
      pair_union_arcs_disj reverse_def with_proj_simps(3))

lemma arc_clink: "x \<in> darts H \<Longrightarrow> x \<rightarrow>\<^bsub>clink H\<^esub>y \<longleftrightarrow> y = face H x \<or> x = node H y"
proof
  show "x \<rightarrow>\<^bsub>clink H\<^esub> y \<Longrightarrow> y = (face H) \<langle>$\<rangle> x \<or> x = (node H) \<langle>$\<rangle> y"
    by (metis Gr_eq cface_def clink_def cnode_def converse.cases pair_pre_digraph.select_convs(2)
      pair_union_arcs_disj reverse_def with_proj_simps(3))
  assume *:"x \<in> darts H" "y = face H x \<or> x = node H y"
  then show "x \<rightarrow>\<^bsub>clink H\<^esub>y"
    by (metis Gr_eq cface_def clinkP cnode_def perm_face perm_node permutes_in_image)
qed

lemma parcs_clink:
  assumes "a \<in> darts H"
  shows "(a,b) \<in> parcs (clink H) \<longleftrightarrow> a = node H b \<or> b = face H a"
  apply rule
   apply (metis arc_clink pair_wf_digraph.in_arcsD1 verts_clink wf_clink with_proj_simps(1,3))
  using assms arc_clink with_proj_simps(3) by blast

lemma clinkN: "x \<in> darts H \<Longrightarrow> node H x\<rightarrow>\<^bsub>clink H\<^esub>x"
  by (metis Gr_eq clinkP cnode_def)

lemma clinkF: "x \<in> darts H \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub>face H x"
  by (metis Gr_eq cface_def hypermap.clinkP hypermap_axioms)

lemma clink_connect_sym: "wf_digraph.connect_sym (clink H)"
proof -
  interpret pair_wf_digraph "clink H" by (rule wf_clink)
  have "v \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>u \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v" for u v
  proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    then consider (node) "x = node H y" | (face) "y = face H x"
      by (metis parcs_clink reachable_in_vertsE verts_clink)
    then have "y\<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>x"
    proof cases
      case node
      then have "y \<rightarrow>\<^sup>*\<^bsub>(cnode H)\<^sup>R\<^esub> x"
        by (metis cnode_connect_sym cnode_eq head_in_verts reach_reverse snd_conv step.hyps(2) 
            verts_clink wf_cnode wf_digraph.reach_sym_arc wf_digraph_wp_iff with_proj_simps(1))
      then show ?thesis
        by (metis (no_types, hide_lams) clink_def comm_pair_union compatibleI_with_proj 
            pair_wf_digraph.wf_reverse reach_in_union wf_cface wf_cnode wf_digraph_wp_iff 
            with_proj_union)
    next
      case face
      then have "y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
        by (metis Gr_eq cface_connect_sym cface_def reachable_in_vertsE step.hyps(3) verts_clink
            wf_cface wf_digraph.reach_sym_arc wf_digraph_wp_iff)
      then show ?thesis
        by (smt (verit, ccfv_threshold) clinkP in_arcsD2 reachable_adj_trans reachable_refl 
            step.hyps(2) wf_cface wf_digraph.reachable_induct wf_digraph_wp_iff with_proj_simps(3))
    qed
    then show "y \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub> v"
      by (meson reachable_trans step.hyps(3))
  qed
  then show ?thesis unfolding connect_sym_def by blast
qed

lemma clink_glink: "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" (is "?L \<longleftrightarrow> ?R")
proof
  interpret pair_wf_digraph "clink H" by (rule wf_clink)
  assume ?L then show ?R
  proof (induct rule: reachable_induct)
    case base
    then have "u \<in> darts H"
      by (metis Gr_pverts cface_def clink_def cnode_def pair_pre_digraph.simps(1) pair_union_def
          perm_node perm_on.Gr_reverse_eq_inv perm_on.intro sup.idem)
    then have "u \<in> pverts (glink H)"
      by (simp add: cedge_def glink_def pair_union_def)
    then show ?case
      by (simp add: wf_glink wf_digraph.reachable_refl wf_digraph_wp_iff)
  next
    case (step x y)
    then show ?case
      by (smt (verit, ccfv_SIG) clink_def converse_iff glink_connect_sym glink_def wf_glink
     pair_pre_digraph.simps(2) pair_union_arcs_disj reverse_def wf_digraph.reach_sym_arc
     wf_digraph.reachable_adj_trans wf_digraph.reachable_trans wf_digraph_wp_iff with_proj_simps(3))
  qed
next
  interpret pair_wf_digraph "glink H" by (rule wf_glink)
  assume ?R then show ?L
  proof (induct rule: reachable_induct)
    case base
    then show ?case
      by (metis Gr_verts Un_iff cedge_def cface_def clink_def cnode_def glink_def
          pair_pre_digraph.simps(1) pair_union_def wf_clink wf_digraph.reachable_refl
          wf_digraph_wp_iff with_proj_simps(1))
  next
    case (step x y)
    then consider (edge) "x\<rightarrow>\<^bsub>cedge H\<^esub>y" | (node) "x\<rightarrow>\<^bsub>cnode H\<^esub>y" | (face) "x\<rightarrow>\<^bsub>cface H\<^esub>y"
      by (metis with_proj_simps(3) glink_def pair_union_arcs_disj)
    then show ?case
      proof cases
        case edge
        then show ?thesis
          by (metis (no_types, hide_lams) step.hyps(3) wf_digraph.reachable_trans Gr_eq cedge_def
            clinkF clinkN clink_connect_sym fin_digraph.axioms(1) finite_clink hypermap.nodeK 
            hypermap_axioms perm_edge perm_node permutes_in_image wf_digraph.adj_reachable_trans
            wf_digraph.reach_sym_arc)
      next
        case node
        then show ?thesis
          by (meson clinkP clink_connect_sym fin_digraph.axioms(1) finite_clink step.hyps(3)
              wf_digraph.adj_reachable_trans wf_digraph.connect_sym_def)
      next
        case face
        then show ?thesis
          by (metis Gr_eq cface_def clinkF fin_digraph.axioms(1) finite_clink step.hyps(3)
              wf_digraph.reachable_adj_trans)
      qed
   qed
qed

context begin
interpretation clink: pair_wf_digraph "clink H" by (rule wf_clink)

lemma connected_clink:
  assumes "connected_hypermap" "x \<in> (darts H)" "y \<in> (darts H)"
  shows "\<exists>p. clink.apath x p y"
proof -
  from assms have "x \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> y"
    by (metis connected_hypermap_def strongly_connected_def verts_glink)
  then show ?thesis
    using clink_glink clink.reachable_apath by simp
qed

text \<open>A "Moebius path" is a contour that cannot appear in a planar map, as it goes from the inside
      of a ring to the outside\<close>

fun moebius_path where
  "moebius_path [] = False"
| "moebius_path (_ # []) = False"
| "moebius_path (x # p) = (vpath (x#p) (clink H)
                    \<and> appears_before p (face H (edge H (last p))) (node H x))"

lemma moebius_path_length: "moebius_path p \<Longrightarrow> length p \<ge> 3"
proof -
  assume *: "moebius_path p"
  then have less_2: "False" if "length p < 2"
    using that hypermap.moebius_path.elims(2) hypermap_axioms by fastforce
  {
    assume "length p = 2"
    then obtain x y where "p = [x,y]"
      by (metis (no_types, hide_lams) One_nat_def Suc_1 length_0_conv length_Suc_conv)
    then have "x \<noteq> y"
      by (metis * distinct_length_2_or_more hypermap.moebius_path.simps(3) hypermap_axioms vpath_def)
    also have "appears_before [y] (face H (edge H y)) (node H x)"
      using * \<open>p = [x, y]\<close> by auto
    then have "x = y"
      by (metis appears_before_in empty_set faceK list.simps(15) singletonD)
    ultimately have False by simp
  }
  then show ?thesis
    using less_2 by force
qed

definition "jordan = (\<forall>p. \<not> (moebius_path p))"
end
end

section \<open>Dual walkups\<close>
definition "permN h \<equiv> \<lparr>darts = darts h, edge = node h, node = face h, face = edge h\<rparr>"

definition "permF h \<equiv> \<lparr>darts = darts h, edge = face h, node = edge h, face = node h\<rparr>"

context hypermap begin

lemma hypermap_permN: "hypermap (permN H)"
  by (simp add: finite_darts hypermap_def nodeK permN_def perm_edge perm_face perm_node)

lemma darts_permN: "darts (permN H) = darts H"
  by (simp add: permN_def)

lemma permN_connect1_glink: "x\<rightarrow>\<^bsub>glink H\<^esub>y \<longleftrightarrow> x\<rightarrow>\<^bsub>glink (permN H)\<^esub>y"
  by (metis (no_types, lifting) cedge_def cface_def cnode_def glink_def pair_union_arcs_disj 
      permN_def pre_hypermap.select_convs(1-4))

lemma permN_glink: "glink H = glink (permN H)"
proof -
  have "verts (glink H) = verts (glink (permN H))"
    by (simp add: cedge_def cface_def cnode_def glink_def permN_def)
  also have "arcs (glink H) = arcs (glink (permN H))"
    apply (simp add: set_eq_iff)
    using permN_connect1_glink by auto
  ultimately show ?thesis
    by simp
qed

lemma connected_permN: "connected_hypermap \<Longrightarrow> hypermap.connected_hypermap (permN H)"
  by (simp add: connected_hypermap_def hypermap.connected_hypermap_def hypermap_permN permN_glink)

lemma genus_permN: "genus H = genus (permN H)"
proof -
  have "euler_lhs H = euler_lhs (permN H)"
    by (simp add: euler_lhs_def permN_def permN_glink)
  moreover have "euler_rhs H = euler_rhs (permN H)"
    by (simp add: euler_rhs_def permN_def)
  ultimately show ?thesis
    by (simp add: genus_def)
qed

lemma planar_permN: "planar H = planar (permN H)"
  by (simp add: genus_permN planar_def)

lemma hypermap_permF: "hypermap (permF H)"
  by (simp add: finite_darts hypermap_def faceK permF_def perm_edge perm_face perm_node)

lemma darts_permF: "darts (permF H) = darts H"
  by (simp add: permF_def)

lemma permF_connect1_glink: "x\<rightarrow>\<^bsub>glink H\<^esub>y \<longleftrightarrow> x\<rightarrow>\<^bsub>glink (permF H)\<^esub>y"
  by (metis (no_types, lifting) cedge_def cface_def cnode_def glink_def pair_union_arcs_disj 
      permF_def pre_hypermap.select_convs(1,2,3,4))

lemma permF_glink: "glink H = glink (permF H)"
proof -
  have "verts (glink H) = verts (glink (permF H))"
    by (simp add: cedge_def cface_def cnode_def glink_def permF_def)
  also have "arcs (glink H) = arcs (glink (permF H))"
    apply (simp add: set_eq_iff)
    using permF_connect1_glink by auto
  ultimately show ?thesis
    by simp
qed

lemma connected_permF: "connected_hypermap \<Longrightarrow> hypermap.connected_hypermap (permF H)"
  by (simp add: connected_hypermap_def hypermap.connected_hypermap_def hypermap_permF permF_glink)

lemma genus_permF: "genus H = genus (permF H)"
proof -
  have "euler_lhs H = euler_lhs (permF H)"
    by (simp add: euler_lhs_def permF_def permF_glink)
  moreover have "euler_rhs H = euler_rhs (permF H)"
    by (simp add: euler_rhs_def permF_def)
  ultimately show ?thesis
    by (simp add: genus_def)
qed

lemma planar_permF: "planar H = planar (permF H)"
  by (simp add: genus_permF planar_def)

(*
definition dual :: "'a pre_hypermap" where
"dual = \<lparr>darts = darts H, edge = inverse (edge H), node = inverse (face H), face = inverse (node H)\<rparr>"

lemma "hypermap dual"
proof
  show "(edge dual) \<langle>$\<rangle> (node dual) \<langle>$\<rangle> (face dual) \<langle>$\<rangle> x = x" for x
    using dual_def nodeK by auto
  show "finite (darts dual)"
    by (simp add: dual_def finite_darts)
  show "edge dual permutes darts dual"
       "node dual permutes darts dual"
       "face dual permutes darts dual"
    by (simp_all add: perm_on.inverse_permutes dual_def perm_edge perm_node perm_face perm_on_def)
qed*)
end
end