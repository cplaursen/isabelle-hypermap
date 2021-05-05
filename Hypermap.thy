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

lemma (in hypermap) wf_glink: "pair_wf_digraph (glink H)"
  unfolding glink_def by (simp add: wf_cface wf_cnode wf_cedge wf_pair_union)

context hypermap begin
lemma cedge_connect_sym: "wf_digraph.connect_sym (cedge H)"
  by (metis cedge_def perm_edge perm_on.intro perm_on.perm_reach_sym)

lemma cnode_connect_sym: "wf_digraph.connect_sym (cnode H)"
  by (metis cnode_def perm_node perm_on.intro perm_on.perm_reach_sym)

lemma cface_connect_sym: "wf_digraph.connect_sym (cface H)"
  by (metis cface_def perm_face perm_on.intro perm_on.perm_reach_sym)

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
    also have "y = edge H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub> x"
              "y = node H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x"
              "y = face H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by (metis cedge_connect_sym cnode_connect_sym cface_connect_sym wf_cedge wf_cface wf_cnode
          wf_digraph.connect_sym_def Gr_eq cedge_def cface_def cnode_def glink_def local.step(2)
          pair_union_arcs_disj wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3))+
    ultimately have "y \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>x \<or> y \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> x \<or> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by auto
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

text \<open>Needed for subtraction on naturals\<close>
lemma (in hypermap) euler_rhs_ge_3: "darts H \<noteq> {} \<Longrightarrow> euler_rhs H \<ge> 3"
proof -
  assume "darts H \<noteq> {}"
  then have "count_cycles_on (darts H) (edge H) > 0"
            "count_cycles_on (darts H) (node H) > 0"
            "count_cycles_on (darts H) (face H) > 0"
      using finite_perm_on.count_cycles_on_nonempty finite_perm_on_face finite_perm_on_node
        finite_perm_on_edge by blast+
    then show "euler_rhs H \<ge> 3"
      by (smt (z3) Suc_pred add.assoc add_mono_thms_linordered_field(3) euler_rhs_def leD le_add1 
          linorder_cases not_less_eq_eq numeral_3_eq_3 plus_1_eq_Suc)
qed

definition euler_lhs :: "'a pre_hypermap \<Rightarrow> nat" where
"euler_lhs h = card (pre_digraph.sccs (glink h)) * 2 + card (darts h)"

lemma (in hypermap) euler_lhs_ge_3: "darts H \<noteq> {} \<Longrightarrow> euler_lhs H \<ge> 3"
  sorry(*proof -
  interpret glink_gr: pre_digraph "glink H" .
  assume "darts H \<noteq> {}"
  then have "pre_digraph.sccs (glink H) \<noteq> {}"
  proof (simp add: glink_def cedge_def cnode_def cface_def)
    
    unfolding glink_def using compatible_digraphs.sccs_union with_proj_union perm_on.sccs_perm sledgehammer
  hence "card (pre_digraph.sccs (glink H)) \<ge> 1"
    using finite_darts sorry
  also have "card (darts H) \<ge> 1"
    by (meson \<open>darts H \<noteq> {}\<close> card_eq_0_iff finite_darts less_one not_less)
  ultimately show ?thesis
    unfolding euler_lhs_def by linarith
qed*)

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
  apply unfold_locales
  by (simp add: clink_def pair_wf_digraph.arc_fst_in_verts pair_wf_digraph.wf_reverse
      wf_cface wf_cnode wf_pair_union pair_wf_digraph.arc_snd_in_verts)+

lemma finite_clink: "fin_digraph (clink H)"
proof
  fix e assume "e \<in> arcs (clink H)"
  then show "tail (clink H) e \<in> verts (clink H)" "head (clink H) e \<in> verts (clink H)"
     apply (metis clink_def pair_wf_digraph.wf_reverse wf_cface wf_cnode wf_digraph.tail_in_verts
        wf_digraph_wp_iff wf_pair_union)
    by (metis \<open>e \<in> arcs (with_proj (clink H))\<close> clink_def pair_wf_digraph.wf_reverse wf_cface
        wf_cnode wf_digraph.head_in_verts wf_digraph_wp_iff wf_pair_union)
next
  show "finite (verts (clink H))"
    by (simp add: finite_darts cface_def clink_def cnode_def perm_node
        perm_on.Gr_reverse_eq_inv perm_on.intro)
  then have "finite (arcs (cface H))"
    by (simp add: cface_def finite_darts)
  also have "finite (arcs ((cnode H)\<^sup>R))"
    by (simp add: cnode_def finite_darts perm_node perm_on.Gr_reverse_eq_inv perm_on.intro)
  ultimately show "finite (arcs (clink H))"
    by (simp add: clink_def)
qed

lemma clinkP:
  assumes "x \<in> darts H" and "y \<in> darts H"
  shows "(y\<rightarrow>\<^bsub>cnode H\<^esub> x \<or> x \<rightarrow>\<^bsub>cface H\<^esub> y) \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub> y"
  unfolding clink_def by (meson arc_reverse pair_union_arcs_disj)

lemma clinkN: "x \<in> darts H \<Longrightarrow> node H x\<rightarrow>\<^bsub>clink H\<^esub>x"
  by (metis Gr_eq clinkP cnode_def perm_node permutes_in_image)

lemma clinkF: "x \<in> darts H \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub>face H x"
  by (metis Gr_eq cface_def hypermap.clinkP hypermap_axioms perm_face permutes_in_image)

text \<open>Copies the glink_rtrancl_sym proof\<close>
lemma clink_connect_sym: "wf_digraph.connect_sym (clink H)"
proof -
  interpret pair_wf_digraph "clink H" by (rule wf_clink)
  have "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v" if "v \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>u" for u v
  using that proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    have *: "y = node H x \<Longrightarrow> x \<rightarrow>\<^sup>*\<^bsub>(cnode H)\<^sup>R\<^esub> y" "y = face H x \<Longrightarrow> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by (metis clink_def wf_digraph.reach_sym_arc cnode_connect_sym wf_cface
          Gr_eq wf_cnode cface_def cnode_def local.step(2) pair_union_arcs_disj
          converse_iff pair_pre_digraph.simps(2) reverse_def wf_digraph.reachable_adjI 
          wf_digraph_wp_iff with_proj_simps(3) reach_reverse cface_connect_sym perm_face
          permutes_in_image)+
    then have "x \<rightarrow>\<^sup>*\<^bsub>(cnode H)\<^sup>R\<^esub> y \<or> y \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> x"
      by (metis step.hyps(2) clink_def Gr_eq Gr_wf cface_def cnode_def pair_union_arcs_disj
        perm_node permutes_in_image wf_digraph.reachable_adjI wf_digraph_wp_iff with_proj_simps(3)
        pair_wf_digraph.wf_reverse)
    then have "y \<rightarrow>\<^sup>*\<^bsub>(clink H)\<^esub> x"
      by (smt (verit, del_insts) step.hyps(2) reach_in_union comm_pair_union with_proj_union Gr_wf
          cface_def cnode_def compatibleI_with_proj perm_face perm_node permutes_in_image
          wf_digraph_wp_iff Gr_eq *(2) clink_def cnode_connect_sym converse_iff 
          pair_pre_digraph.simps(2) pair_union_arcs_disj reach_reverse reverse_def 
          wf_digraph.reachable_adjI with_proj_simps(3) pair_wf_digraph.wf_reverse
          wf_digraph.connect_sym_def)
    then show "y \<rightarrow>\<^sup>*\<^bsub>with_proj (clink H)\<^esub> v"
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
          by (metis Gr_pverts clinkP clink_connect_sym cnode_def fin_digraph.axioms(1)
              finite_clink step.hyps(3) wf_cnode wf_digraph.adj_in_verts(1)
              wf_digraph.adj_in_verts(2) wf_digraph.adj_reachable_trans wf_digraph.connect_sym_def
              wf_digraph_wp_iff with_proj_simps(1))
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
  from assms(1) have "x \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> y" using connected_hypermap_def assms strongly_connected_def
    by (metis (no_types, lifting) Gr_eq clinkP clink_glink cnode_def wf_glink perm_node 
        permutes_in_image clink.reachable_adjI wf_digraph.reachable_in_verts(2) wf_digraph_wp_iff
        with_proj_simps(3))
  then show ?thesis using clink_glink clink.reachable_apath by simp
qed

text \<open>A "Moebius path" is a contour that cannot appear in a planar map, as it goes from the inside
      of a ring to the outside\<close>

fun moebius_path where
  "moebius_path [] = False"
| "moebius_path (_ # []) = False"
| "moebius_path p = (vpath p (clink H)
                    \<and> appears_before p (face H (edge H (last p))) (node H (hd p)))"

lemma "moebius_path p \<Longrightarrow> length p \<ge> 3"
proof (rule ccontr)
  assume *: "moebius_path p" "\<not> length p \<ge> 3"
  then consider "length p = 0 \<or> length p = 1" | "length p = 2"
    by linarith
  then show "False"
  proof cases
    case 1
    then show ?thesis
      using *(1) moebius_path.elims(2) by fastforce
  next
    case 2
    then have **: "vpath p (clink H)" "appears_before p (face H (edge H (last p))) (node H (hd p))"
      using *(1) hypermap.moebius_path.elims hypermap_axioms by blast+
    then have elems: "face H (edge H (last p)) \<in> set p \<and> node H (hd p) \<in> set p"
      using appears_before_in by auto
    from 2 obtain x y where "p = [x,y]"
      by (metis (no_types, lifting) length_0_conv length_Suc_conv numeral_2_eq_2)
    then have "x \<noteq> y"
      by (metis  *(1) vpath_def distinct_length_2_or_more moebius_path.simps(3))
    then have "face H (edge H y) = y \<and> x = node H x \<or> face H (edge H y) = x \<and> y = node H x"
      by (metis \<open>p = [x,y]\<close> elems empty_iff empty_set faceK hypermap.nodeK hypermap_axioms last.simps list.distinct(1) list.sel(1) set_ConsD)
    then show "False" using \<open>x \<noteq> y\<close> node_inv sorry
  qed
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

lemma permN_connect1_glink: "x\<rightarrow>\<^bsub>glink H\<^esub>y \<longleftrightarrow> x\<rightarrow>\<^bsub>glink (permN H)\<^esub>y"
  by (metis (no_types, lifting) cedge_def cface_def cnode_def glink_def pair_union_arcs_disj 
      permN_def pre_hypermap.select_convs(1,2,3,4))

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
qed

lemma "clink dual = clink H"
  sorry
end
end