theory Hypermap
  imports "Fun_Graph" 
begin

section \<open>Hypermap\<close>
record ('a::finite) hypermap =
  edge :: "'a \<Rightarrow> 'a"
  node :: "'a \<Rightarrow> 'a"
  face :: "'a \<Rightarrow> 'a"

definition darts :: "'a hypermap \<Rightarrow> 'a set" where
"darts G = UNIV"

locale hypermap =
  fixes H :: "('a :: finite) hypermap" (structure)
  assumes edgeK: "\<And>x. edge H (node H (face H x)) = x"
begin

text \<open>Basic properties of the functions\<close>
lemma edgeI: "inj (edge H)"
  by (metis edgeK finite_UNIV finite_UNIV_surj_inj surj_def)

lemma nodeK: "\<And>x. node H (face H (edge H x)) = x"
  by (meson edgeI edgeK inj_eq)

lemma nodeI: "inj (node H)"
  by (metis nodeK finite_UNIV finite_UNIV_surj_inj surj_def)
  
lemma faceK: "\<And>x. face H (edge H (node H x)) = x"
  by (meson nodeI nodeK inj_eq)

lemma faceI: "inj (face H)"
  by (metis faceK finite_UNIV finite_UNIV_surj_inj surj_def)

text \<open>Permutations\<close>
lemma permutes_edge: "(edge H) permutes UNIV"
  by (meson UNIV_I bijI bij_imp_permutes edgeI endo_inj_surj finite_UNIV subset_UNIV)

lemma permutation_edge: "permutation (edge H)"
  using permutes_edge unfolding permutation_permutes by auto

lemma permutes_node: "node H permutes UNIV"
  by (meson UNIV_I bijI bij_imp_permutes nodeI endo_inj_surj finite_UNIV subset_UNIV)

lemma permutation_node: "permutation (node H)"
  using permutes_node unfolding permutation_permutes by auto

lemma permutes_face: "face H permutes UNIV"
  by (meson UNIV_I bijI bij_imp_permutes faceI endo_inj_surj finite_UNIV subset_UNIV)

lemma permutation_face: "permutation (face H)"
  using permutes_face unfolding permutation_permutes by auto

text \<open>Cycles\<close>
definition cedge :: "'a rel"
  where "cedge \<equiv> {(a,b) . b \<in> set (support (edge H) a)}"

lemma cedge_rtrancl: "cedge = (rel_of (edge H))\<^sup>*"
proof -
  have "permutation (edge H)" by (rule permutation_edge)
  thus "cedge = (rel_of (edge H))\<^sup>*"
    using support_rtrancl cedge_def by fast
qed

definition cnode :: "'a rel"
  where "cnode \<equiv> {(a,b) . b \<in> set (support (node H) a)}"

lemma cnode_rtrancl: "cnode = (rel_of (node H))\<^sup>*"
proof -
  have "permutation (node H)" by (rule permutation_node)
  thus "cnode = (rel_of (node H))\<^sup>*"
    using support_rtrancl cnode_def by fast
qed

definition cface :: "'a rel"
  where "cface \<equiv> {(a,b) . b \<in> set (support (face H) a)}"

lemma cface_rtrancl: "cface = (rel_of (face H))\<^sup>*"
proof -
  have "permutation (face H)" by (rule permutation_face)
  thus "cface = (rel_of (face H))\<^sup>*"
    using support_rtrancl cface_def by fast
qed

lemma sym_cedge: "sym cedge"
  unfolding cedge_def sym_def using permutation_edge support_sym by fast

lemma sym_cnode: "sym cnode"
  unfolding cnode_def sym_def using permutation_node support_sym by fast

lemma sym_cface: "sym cface"
  unfolding cface_def sym_def using permutation_face support_sym by fast

section \<open>Components\<close>

definition rel_to_digraph :: "'a rel \<Rightarrow> 'a pair_pre_digraph" where
"rel_to_digraph r = \<lparr> pverts = UNIV, parcs = r\<rparr>"

interpretation pair_wf_digraph "rel_to_digraph r"
  by (simp add: pair_wf_digraph.intro rel_to_digraph_def)

definition glink :: "'a hypermap \<Rightarrow> 'a rel"
  where "glink h = (rel_of (edge h)) \<union> ((rel_of (node h)) \<union> rel_of (face h))"

lemma glink_e: "(x, edge H x) \<in> glink H"
  unfolding glink_def by (rule UnI1, simp add: rel_of_def)
lemma glink_n: "(x, node H x) \<in> glink H"
  unfolding glink_def by (rule UnI2, simp add: rel_of_def)
lemma glink_f: "(x, face H x) \<in> glink H"
  unfolding glink_def by (rule UnI2, simp add: rel_of_def)

lemma glink_connected: "sym ((glink H)\<^sup>*)"
  by (metis cedge_rtrancl glink_def permutation_face permutation_node rtrancl_Un_rtrancl
            support_rtrancl support_sym symI sym_Un sym_cedge sym_rtrancl)

definition connected_hypermap :: "'a hypermap \<Rightarrow> bool" where
"connected_hypermap h \<equiv> connected (rel_to_digraph (glink h))"

text \<open>All connected components are in the same equivalence class\<close>
corollary "equiv UNIV ((glink H)\<^sup>*)"
  by (simp add: glink_connected equivI refl_rtrancl trans_rtrancl)

section \<open>Genus\<close>
definition euler_rhs :: "'a hypermap \<Rightarrow> nat" where
"euler_rhs h = card (cycles (edge h) (darts h)) +
               card (cycles (node h) (darts h)) +
               card (cycles (face h) (darts h))"

definition euler_lhs :: "'a hypermap \<Rightarrow> nat" where
"euler_lhs h = card (sccs (glink h)) + card (darts h)"

definition genus where
"genus h \<equiv> (euler_lhs h - euler_rhs h) div 2"

definition planar where
"planar h \<equiv> genus h = 0"

section \<open>Jordan\<close>
definition clink :: "'a hypermap \<Rightarrow> 'a rel" where
"clink g \<equiv> (rel_of (face g)) \<union> (rel_of (node g))\<inverse>"

lemma clinkP: "(x = node H y \<or> face H x = y) \<Longrightarrow> (x,y) \<in> clink H"
  unfolding clink_def apply (erule disjE)
  by (simp add: rel_of_eq)+

lemma clinkN: "((node H x), x) \<in> clink H"
  using clinkP by simp

lemma clinkF: "(x, (face H x)) \<in> clink H"
  using clinkP by simp

lemma clinkC: "sym ((clink H)\<^sup>*)"
  unfolding clink_def
  by (metis faceK hypermap.cedge_rtrancl hypermap.intro hypermap.sym_cedge nodeK select_convs(1)
      select_convs(2) select_convs(3) sym_Un sym_conv_converse_eq rtrancl_Un_rtrancl rtrancl_converse sym_rtrancl)

lemma clink_glink: "(clink H)\<^sup>* = (glink H)\<^sup>*"
proof (rule subset_antisym)
    have "\<forall>x y. x \<subseteq> ((x\<inverse> \<union> y)\<inverse>)\<^sup>*" by auto
    then show "(clink H)\<^sup>* \<subseteq> (glink H)\<^sup>*"
      by (metis (no_types) rtrancl_subset_rtrancl Un_subset_iff clink_def converse_converse
          glink_connected glink_def r_into_rtrancl rtrancl_converse subsetI sup_left_commute sym_conv_converse_eq)
  next
    have "glink H \<subseteq> (clink H)\<^sup>*"
    proof
      fix z assume "z \<in> glink H"
      then obtain x y where "(x,y) = z" by (metis surj_pair)
      then have "y = edge H x \<or> y = node H x \<or> y = face H x"
        by (metis Un_iff \<open>z \<in> glink H\<close> glink_def rel_of_eq)
      also have "y = edge H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        by (metis clinkC clinkF clinkN converse_rtrancl_into_rtrancl nodeK r_into_rtrancl sym_def)
      moreover have "y = node H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        by (simp add: clinkC clinkN r_into_rtrancl symD)
      moreover have "y = face H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>*"
        using clinkP by blast
      ultimately show "z \<in> (clink H)\<^sup>*" using \<open>(x,y) = z\<close> by blast
    qed
    then show "(glink H)\<^sup>* \<subseteq> (clink H)\<^sup>*"
      by (rule rtrancl_subset_rtrancl)
  qed

lemma connected_clink:
  assumes "connected_hypermap H"
  shows "\<exists> p. (awalk (clink H) x p y)"
  sorry

definition appears_before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"appears_before p x y = (y \<in> set (dropWhile (\<lambda> z. z \<noteq> x) p))"

fun moebius_path :: "'a hypermap \<Rightarrow> 'a vwalk \<Rightarrow> bool" where
  "moebius_path _ [] = False"
| "moebius_path h p = (vpath p (rel_to_digraph (clink h)) \<and>
            (\<exists>n. ((n, (last p)) \<in> (rel_of (node h))) \<and> appears_before p n (node h (hd p))))"

definition jordan :: "'a hypermap \<Rightarrow> bool" where
"jordan h = (\<forall>p. \<not> (moebius_path h p))"

end
end