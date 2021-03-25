theory Hypermap
  imports "Fun_Graph"
begin

section \<open>Hypermap\<close>

record 'a hypermap =
  darts :: "'a set"
  edge :: "'a perm"
  node :: "'a perm"
  face :: "'a perm"

locale hypermap =
  fixes H :: "'a hypermap" (structure)
  assumes edgeK: "edge H (node H (face H x)) = x"
  and finite_darts: "finite (darts H)"
  and darts_edge: "set_perm (edge H) \<subseteq> darts H"
  and darts_node: "set_perm (node H) \<subseteq> darts H"
  and darts_face: "set_perm (face H) \<subseteq> darts H"
begin

text \<open>Basic properties of the functions\<close>
lemma nodeK: "\<And>x. node H (face H (edge H x)) = x"
  by (meson apply_inj_eq_iff edgeK)

lemma faceK: "\<And>x. face H (edge H (node H x)) = x"
  by (meson apply_inj_eq_iff nodeK)

lemma perm_edge: "(edge H) permutes (darts H)"
  by (meson bij_betw_apply_perm bij_imp_permutes darts_edge in_mono in_set_permI)

lemma perm_node: "(node H) permutes (darts H)"
  by (meson bij_betw_apply_perm bij_imp_permutes darts_node in_mono in_set_permI)

lemma perm_face: "(face H) permutes (darts H)"
  by (meson bij_betw_apply_perm bij_imp_permutes darts_face in_mono in_set_permI)

text \<open>Cycles\<close>
definition cedge where
 "cedge h \<equiv> (Gr (darts h) (edge h))\<^sup>+"

lemma cedge_sym: "sym (cedge H)"
  by (simp add: perm_trancl_sym cedge_def perm_edge)

definition cnode where
 "cnode h \<equiv> (Gr (darts h) (node h))\<^sup>+"

lemma cnode_sym: "sym (cnode H)"
  by (simp add: perm_trancl_sym cnode_def perm_node)

definition cface where
  "cface h \<equiv> (Gr (darts h) (face h))\<^sup>+"

lemma cface_sym: "sym (cface H)"
  by (simp add: perm_trancl_sym cface_def perm_face)

section \<open>Components\<close>

definition rel_to_digraph :: "'a rel \<Rightarrow> 'a pair_pre_digraph" where
"rel_to_digraph r = \<lparr>pverts = Field r, parcs = r\<rparr>"

interpretation pair_wf_digraph "rel_to_digraph r"
  by (simp add: FieldI1 FieldI2 pair_wf_digraph_def rel_to_digraph_def)

definition glink :: "'a hypermap \<Rightarrow> 'a rel"
  where "glink h = (Gr (darts h) (edge h)) \<union>
                   (Gr (darts h) (node h)) \<union>
                   (Gr (darts h) (face h))"

lemma glink_sym: "sym ((glink H)\<^sup>+)"
proof -
  have "sym ((glink H)\<^sup>*)"
    by (smt (verit, ccfv_threshold) cface_sym cnode_sym cedge_sym sym_rtrancl glink_def
          hypermap_axioms perm_edge perm_face perm_node perm_trancl_sym rtrancl_Un_rtrancl
          sym_Un trancl_rtrancl_absorb)
  then show "sym ((glink H)\<^sup>+)"
    by (metis rtranclD sym_def trancl_into_rtrancl)
qed

definition connected_hypermap :: "'a hypermap \<Rightarrow> bool" where
"connected_hypermap h \<equiv> connected (rel_to_digraph (glink h))"

text \<open>All connected components are in the same equivalence class\<close>
section \<open>Genus\<close>
definition euler_rhs :: "'a hypermap \<Rightarrow> nat" where
"euler_rhs h = count_cycles_on (darts h) (edge h) +
               count_cycles_on (darts h) (node h) +
               count_cycles_on (darts h) (face h)"

definition euler_lhs :: "'a hypermap \<Rightarrow> nat" where
"euler_lhs h = card (sccs (glink h)) * 2 + card (darts h)"

definition genus where
"genus h \<equiv> (euler_lhs h - euler_rhs h) div 2"

definition planar where
"planar h \<equiv> genus h = 0"

section \<open>Jordan\<close>
definition clink :: "'a hypermap \<Rightarrow> 'a rel" where
"clink g \<equiv> (Gr (darts g) (face g)) \<union> (Gr (darts g) (node g))\<inverse>"

lemma clinkP:
  assumes "x \<in> darts H" and "y \<in> darts H"
  shows "(x = node H y \<or> face H x = y) \<Longrightarrow> (x,y) \<in> clink H"
  unfolding clink_def apply (erule disjE)
  using Gr_def assms by auto+

lemma clinkN: "x \<in> darts H \<Longrightarrow> ((node H x), x) \<in> clink H"
  by (simp add: Gr_eq clink_def)

lemma clinkF: "x \<in> darts H \<Longrightarrow> (x, (face H x)) \<in> clink H"
  by (simp add: Gr_eq clink_def)

lemma clinkC: "sym ((clink H)\<^sup>+)"
  unfolding clink_def by (smt (verit, ccfv_threshold) cface_def cface_sym cnode_def
      cnode_sym converse_Un rtranclD rtrancl_Un_rtrancl rtrancl_converse sym_conv_converse_eq
      sym_def trancl_into_rtrancl trancl_rtrancl_absorb)
  
lemma clink_glink: "(clink H)\<^sup>+ = (glink H)\<^sup>+"
proof
  show "(clink H)\<^sup>+ \<subseteq> (glink H)\<^sup>+" sorry
    (*have "\<forall>x y. x \<subseteq> ((x\<inverse> \<union> y)\<inverse>)\<^sup>+" by auto
    then show "(clink H)\<^sup>+ \<subseteq> (glink H)\<^sup>+" try*)
  next
    have "glink H \<subseteq> (clink H)\<^sup>+"
    proof
      fix z assume "z \<in> glink H"
      then obtain x y where "(x,y) = z" by (metis surj_pair)
      then have "y = edge H x \<or> y = node H x \<or> y = face H x"
        by (metis Gr_eq UnE \<open>z \<in> glink H\<close> glink_def)
      also have "y = edge H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>+"
        by (smt (z3) Gr_eq Un_iff \<open>(x, y) = z\<close> \<open>z \<in> glink H\<close> clinkC clinkN hypermap.clinkF hypermap.glink_def hypermap_axioms nodeK perm_face perm_node permutes_in_image sym_def trancl.r_into_trancl trancl_trans)
      moreover have "y = node H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>+"
        by (metis calculation(2) clinkC clinkN darts_edge darts_node in_mono in_set_permI symE trancl.simps)
      moreover have "y = face H x \<Longrightarrow> (x,y) \<in> (clink H)\<^sup>+"
        by (metis calculation(2) clinkF darts_edge darts_node faceK in_mono in_set_permI trancl.r_into_trancl)
      ultimately show "z \<in> (clink H)\<^sup>+" using \<open>(x,y) = z\<close> by blast
    qed
    then show "(glink H)\<^sup>+ \<subseteq> (clink H)\<^sup>+"
      by (smt (verit) IntE relcompE subsetD subsetI trancl_Int_subset transitive_closure_trans(2))
 qed

lemma connected_clink:
  assumes "connected_hypermap H" "x \<in> (darts H)"
  shows "\<exists> p. (awalk (clink H) x p y)"
  sorry

definition appears_before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"appears_before p x y = (y \<in> set (dropWhile (\<lambda> z. z \<noteq> x) p))"

fun moebius_path :: "'a hypermap \<Rightarrow> 'a vwalk \<Rightarrow> bool" where
  "moebius_path _ [] = False"
| "moebius_path h p = (vpath p (rel_to_digraph (clink h)) \<and>
            (\<exists>n. ((n, (last p)) \<in> (Gr (darts h) (node h))) \<and> appears_before p n (node h (hd p))))"

definition jordan :: "'a hypermap \<Rightarrow> bool" where
"jordan h = (\<forall>p. \<not> (moebius_path h p))"

end
end