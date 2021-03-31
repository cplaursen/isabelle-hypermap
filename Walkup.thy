theory Walkup
  imports Hypermap
begin

text \<open>Differs from the Coq definition in that here we explicitly set
      skip z f z = z. This preserves permutations, which would otherwise have
      a dangling link.\<close>
definition skip :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) " where
"skip z f \<equiv> \<lambda> y. (if y = z then z else (if f y = z then f z else f y))"

lemma skip_id: "skip z f z = z"
  unfolding skip_def by simp

lemma skip_perm: "(\<langle>$\<rangle>) (Perm (skip z (p :: 'a perm))) = skip z p"
proof
  obtain A where "A = set_perm p" by auto
  then have set_perm_A: "finite A" "inj_on p A" "(\<forall>x\<in>A. p x \<in> A)" "(\<forall>x. x\<notin>A \<longrightarrow> p x = x)"
    by auto
  fix x show "(Perm (skip z p)) \<langle>$\<rangle> x = skip z p x"
  proof (rule apply_perm_Perm)
    show "finite A" using set_perm_A(1) by auto
    show "inj_on (skip z p) A"
      by (smt (z3) set_perm_A inj_on_def skip_def)
    show "\<And>x. x \<in> A \<Longrightarrow> skip z ((\<langle>$\<rangle>) p) x \<in> A"
      by (metis skip_def set_perm_A(3))
    show "\<And>x. x \<notin> A \<Longrightarrow> skip z ((\<langle>$\<rangle>) p) x = x"
      by (metis set_perm_A(4) skip_def)
  qed
qed

lemma perm_skip_image:
  assumes "(f::'a perm) permutes S"
  shows "(skip z f) ` (S - {z}) = S - {z}"
proof
  show "(skip z f) ` (S - {z}) \<subseteq> (S - {z})"
  proof
    fix y assume y_skip: "y \<in> skip z f ` (S - {z})"
    then show "y \<in> (S - {z})"
    proof (cases "y = z")
      case True
      then have "skip z f y = z"
          by (simp add: skip_def)
        then show ?thesis
        by (smt (verit, ccfv_threshold) Diff_iff Permutations.permutes_not_in y_skip assms empty_iff image_iff injD insert_iff permutes_inj skip_def)
    next
      case False
      then have "skip z f y = f y \<or> skip z f y = f z"
        by (simp add: skip_def)
      then show ?thesis
        by (smt (verit, ccfv_SIG) y_skip Diff_iff False assms empty_iff image_iff insert_iff permutes_in_image skip_def)
    qed
  qed
next
  show "S - {z} \<subseteq> skip z f ` (S - {z})"
  proof
    fix y assume "y \<in> S - {z}"
    then have "\<exists>c \<in> S - {z}. skip z f c = y"
      by (smt (verit, ccfv_threshold) assms member_remove permutes_def remove_def skip_def)
    then show "y \<in> skip z f ` (S - {z})" by auto
  qed
qed

lemma skip_permutes:
  assumes "(f::'a perm) permutes S"
  shows "skip z f permutes (S - {z})"
proof -
  from assms have perm_f: "(\<forall>x. x \<notin> S \<longrightarrow> f x = x) \<and> (\<forall>y. \<exists>!x. f x = y)"
    by (metis permutes_def)
  then have "(\<forall>x. x \<notin> (S - {z}) \<longrightarrow> skip z f x = x)"
    by (simp add: skip_def)
  moreover have "\<forall>y. \<exists>!x. skip z f x = y"
    by (smt (verit, ccfv_threshold) perm_f skip_def)
  ultimately show ?thesis
    by (simp add: permutes_def)
qed

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

lemma skip_edge_Perm: 
  assumes "hypermap h"
  shows "(\<langle>$\<rangle>) (Perm (skip_edge z h)) = skip_edge z h"
proof
  obtain A where "A = darts h" by auto
  fix x show "(Perm (skip_edge z h)) \<langle>$\<rangle> x = skip_edge z h x"
  proof (rule apply_perm_Perm)
    show "finite (A - {z})"
      by (simp add: \<open>A = darts h\<close> assms hypermap.finite_darts)
    show "inj_on (skip_edge z h) (A - {z})"
      by (smt (z3) apply_inj_eq_iff assms hypermap.faceK inj_on_def skip_edge_def)
    show "\<And>x. x \<in> (A - {z}) \<Longrightarrow> skip_edge z h x \<in> (A - {z})"
      by (smt (z3) Diff_iff \<open>A = darts h\<close> apply_inj_eq_iff assms empty_iff hypermap.faceK hypermap.perm_edge hypermap.perm_face insert_iff permutes_in_image skip_edge_def)
    show "\<And>x. x \<notin> (A - {z}) \<Longrightarrow> skip_edge z h x = x"
      by (smt (z3) Diff_empty Diff_insert0 Permutations.permutes_not_in \<open>A = darts h\<close> assms hypermap.perm_edge hypermap.perm_face insert_Diff insert_iff skip_edge_def)
  qed
qed

lemma skip_edge_subproof:
  assumes "u \<noteq> z" "hypermap H"
  shows "skip_edge z H u \<noteq> z"
  using assms hypermap.faceK hypermap.nodeK skip_edge_def by (smt (z3))

lemma skip_edge_permutes:
  assumes "hypermap h"
  shows "skip_edge z h permutes darts h - {z}"
  unfolding permutes_def
proof
  have "\<And>x. x \<notin> darts h - {z} \<Longrightarrow> skip_edge z h x = x"
  proof -
    fix x assume "x \<notin> darts h - {z}"
    then have disj: "x \<notin> darts h \<or> x = z" by simp
    have "x = z \<Longrightarrow> skip_edge z h x = x" by (simp add: skip_edge_id)
    also have "x \<notin> darts h \<Longrightarrow> skip_edge z h x = x"
      by (metis Permutations.permutes_not_in assms hypermap.perm_edge hypermap.perm_face skip_edge_def)
    ultimately show "skip_edge z h x = x"
      using disj by linarith
    qed
    then show "\<forall>x. x \<notin> darts h - {z} \<longrightarrow> skip_edge z h x = x" by simp
next
  show "\<forall>y. \<exists>!x. skip_edge z h x = y"
    by (metis assms skip_edge_Perm UNIV_I bij_apply bij_imp_permutes permutes_univ)
qed


definition walkupE :: "'a pre_hypermap \<Rightarrow> 'a \<Rightarrow> 'a pre_hypermap" where
"walkupE h z = 
  \<lparr>darts = darts h - {z},
   edge = Perm (skip_edge z h),
   node = Perm (skip z (node h)),
   face = Perm (skip z (face h))\<rparr>"

lemma hypermap_walkupE:
  assumes "hypermap h"
  shows "hypermap (walkupE h z)" (is "hypermap ?E")
proof
  have "finite (darts h)" using assms hypermap.finite_darts by auto
  also have "(darts ?E) = (darts h) - {z}"
    by (simp add: walkupE_def)
  ultimately show "finite (darts ?E)" by auto
  show "edge (walkupE h z) permutes darts (walkupE h z)"
    by (simp add: assms hypermap.perm_node skip_edge_Perm walkupE_def skip_edge_permutes)
  show "(node (walkupE h z)) permutes darts (walkupE h z)"
    by (simp add: assms hypermap.perm_node skip_perm skip_permutes walkupE_def)
  show "(face (walkupE h z)) permutes darts (walkupE h z)"
    by (simp add: assms hypermap.perm_face skip_perm skip_permutes walkupE_def)
next
  fix x have "skip_edge z h (skip z (node h) (skip z (face h) x)) = x"
  proof (cases "x = z")
    case True
    then show ?thesis
      by (auto simp add: skip_id skip_edge_id)
  next
    case False
    then show ?thesis
      by (smt (z3) apply_inj_eq_iff assms hypermap.faceK skip_def skip_edge_def)
  qed
  then show "(edge (walkupE h z)) \<langle>$\<rangle> (node (walkupE h z)) \<langle>$\<rangle> (face (walkupE h z)) \<langle>$\<rangle> x = x"
    by (simp add: skip_perm walkupE_def assms skip_edge_Perm)
qed

end