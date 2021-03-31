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

lemma darts_edge: "set_perm (edge H) \<subseteq> darts H"
  by (simp add: perm_edge set_perm_subset)

lemma darts_node: "set_perm (node H) \<subseteq> darts H"
  by (simp add: perm_node set_perm_subset)

lemma darts_face: "set_perm (face H) \<subseteq> darts H"
  by (simp add: perm_face set_perm_subset)

text \<open>Cycles\<close>
definition cedge where
 "cedge h \<equiv> (Gr (darts h) (edge h))"

lemma cedge_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub> u "
  by (metis cedge_def finite_darts perm_edge perm_on.intro perm_on.perm_reach_sym)

definition cnode where
 "cnode h \<equiv> (Gr (darts h) (node h))"

lemma cnode_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub> u "
  by (metis cnode_def finite_darts perm_node perm_on.intro perm_on.perm_reach_sym)

definition cface where
  "cface h \<equiv> (Gr (darts h) (face h))"

lemma cface_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>cface H\<^esub> u "
  by (metis cface_def finite_darts perm_face perm_on.intro perm_on.perm_reach_sym)

section \<open>Components\<close>
definition glink
  where "glink h = pair_union (cedge h) (pair_union (cnode h) (cface h))"

lemma glink_wf: "pair_wf_digraph (glink H)"
  unfolding cedge_def cnode_def cface_def glink_def
  by (metis Gr_wf compatibleI_with_proj perm_edge perm_face perm_node permutes_in_image 
            wellformed_union wf_digraph_wp_iff with_proj_union)

lemma glink_reachable_sym: "u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub> u"
proof -
  interpret pair_wf_digraph "glink H" by (simp add: glink_wf)
  assume "u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" then show ?thesis
  proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    then show ?case sorry
  qed
qed

definition connected_hypermap :: "'a pre_hypermap \<Rightarrow> bool" where
"connected_hypermap h \<equiv> strongly_connected (glink h)"

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

lemma wf_clink: "pair_wf_digraph (clink H)"
proof -
  have "pair_wf_digraph (cface H)"
    by (simp add: Gr_wf cface_def darts_face)
  also have "pair_wf_digraph ((cnode H)\<^sup>R)"
    by (simp add: Gr_wf cnode_def wf_reverse darts_node)
  ultimately show ?thesis
    unfolding clink_def by (rule wf_pair_union)
qed

lemma clinkP:
  assumes "x \<in> darts H" and "y \<in> darts H"
  shows "(y\<rightarrow>\<^bsub>cnode H\<^esub> x \<or> x \<rightarrow>\<^bsub>cface H\<^esub> y) \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub> y"
  unfolding clink_def apply (erule disjE)
   apply (metis (no_types, lifting) UnI2 arcs_union converse_iff pair_pre_digraph.select_convs(2) reverse_def with_proj_simps(2) with_proj_simps(3) with_proj_union)
  by (metis (no_types, lifting) UnI1 arcs_union with_proj_simps(2) with_proj_simps(3) with_proj_union)

lemma clinkN: "x \<in> darts H \<Longrightarrow> node H x\<rightarrow>\<^bsub>clink H\<^esub>x"
  by (metis Gr_eq clinkP cnode_def perm_node permutes_in_image)

lemma clinkF: "x \<in> darts H \<Longrightarrow> x\<rightarrow>\<^bsub>clink H\<^esub>face H x"
  by (metis Gr_eq cface_def hypermap.clinkP hypermap_axioms perm_face permutes_in_image)

lemma clink_rtrancl_sym: "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub> u"
proof -
  interpret pair_wf_digraph "clink H" by (rule wf_clink)
  assume "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v" then show ?thesis
  proof (induct rule: reachable_induct)
    case base
    then show ?case by simp
  next
    case (step x y)
    then show ?case sorry
  qed
qed

lemma clink_glink: "u \<rightarrow>\<^sup>*\<^bsub>clink H\<^esub>v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>glink H\<^esub>v" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
    sorry
next
  assume ?R then show ?L
    sorry
    (*
    have "glink H \<subseteq> (clink H)\<^sup>*"
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
    then show "(glink H)\<^sup>* \<subseteq> (clink H)\<^sup>*"
      by (rule rtrancl_subset_rtrancl)*)
qed

context begin
interpretation pair_wf_digraph "clink H" by (rule wf_clink)

lemma connected_clink:
  assumes "connected_hypermap H" "x \<in> (darts H)" "y \<in> (darts H)"
  shows "\<exists>p. apath x p y"
  using clink_glink assms connected_hypermap_def sorry

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