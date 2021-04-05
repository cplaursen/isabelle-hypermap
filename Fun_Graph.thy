theory Fun_Graph
  imports "Perm" "Graph_Theory.Graph_Theory"
begin

text \<open>Permutations and funpow\<close>
lemma cycles_funpow:
  assumes "z \<in> set_cycle (perm_orbit p x)"
  shows "\<exists>n. (apply_perm p ^^ n) z = x"
proof -
  from assms have "(apply_perm p ^^ n) z \<in> set_cycle (perm_orbit p x)" by simp
  also have "x \<in> set_cycle (perm_orbit p x)" using assms by fastforce
  ultimately show ?thesis
    by (metis apply_perm_power assms funpow_apply_cycle_perm_orbit set_cycle_ex_funpow)
qed

lemma funpow_cycles:
  assumes "(apply_perm p ^^ n) z = x" "z \<noteq> x"
  shows "z \<in> set_cycle (perm_orbit p x)"
proof (cases "n = 0")
  case True then show ?thesis using assms by auto
next
  case False then show ?thesis
    by (metis apply_inj_eq_iff apply_perm_power assms funpow_apply_perm_in_perm_orbit_iff
       id_funpow_id start_in_perm_orbit_iff)
qed

lemma set_perm_subset:
  assumes "(p :: 'a perm) permutes S"
  shows "set_perm p \<subseteq> S"
  by (meson permutes_not_in apply_perm_neq_idI assms subsetI)

lemma permutes_perm:
  assumes "finite S" "f permutes S"
  shows "(Perm f) permutes S"
  by (metis (no_types, lifting) Perm_inverse assms mem_Collect_eq permutation permutation_permutes)

text \<open>Digraph extras\<close>
lemma reachable1:
  assumes "a \<rightarrow>\<^bsub>G\<^esub> b" "a \<in> verts G" "b \<in> verts G"
  shows "a\<rightarrow>\<^sup>*\<^bsub>G\<^esub>b"
  by (metis assms reachable_def rtrancl_on.simps)

lemma reach_sym_arc:
  assumes "a \<rightarrow>\<^sup>*\<^bsub>g\<^esub> b \<Longrightarrow> b \<rightarrow>\<^sup>*\<^bsub>g\<^esub> a" "wf_digraph g"
  shows "a \<rightarrow>\<^bsub>g\<^esub> b \<Longrightarrow> b \<rightarrow>\<^sup>*\<^bsub>g\<^esub> a"
  by (simp add: assms wf_digraph.reachable_adjI)

definition pair_union :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" where
"pair_union g h \<equiv> \<lparr> pverts = pverts g \<union> pverts h, parcs = parcs g \<union> parcs h\<rparr>"

lemma with_proj_union[simp]: "with_proj (pair_union g h) = union (with_proj g) (with_proj h)"
  by (simp add: pair_union_def)

lemma comm_pair_union: "pair_union g h = pair_union h g"
  unfolding pair_union_def by auto

lemma wf_pair_union:
  assumes "pair_wf_digraph g" "pair_wf_digraph h"
  shows "pair_wf_digraph (pair_union g h)"
  by (metis assms compatibleI_with_proj wellformed_union wf_digraph_wp_iff with_proj_union)

lemma pair_union_arcs_disj: "x\<rightarrow>\<^bsub>pair_union g h\<^esub>y \<longleftrightarrow> x\<rightarrow>\<^bsub>g\<^esub>y \<or> x\<rightarrow>\<^bsub>h\<^esub>y"
  by (simp add: pair_union_def)

lemma arc_in_union: "x\<rightarrow>\<^bsub>with_proj g\<^esub>y \<Longrightarrow> x\<rightarrow>\<^bsub>pair_union g h\<^esub>y"
  using with_proj_union apply simp
  by (metis Un_iff arcs_union with_proj_simps(2) with_proj_simps(3) with_proj_union)

lemma reach_in_union:
  assumes "wf_digraph g" "wf_digraph h" "compatible g h" "x\<rightarrow>\<^sup>*\<^bsub>g\<^esub>y"
  shows "x\<rightarrow>\<^sup>*\<^bsub>union g h\<^esub>y"
by (meson assms pre_digraph.reachable_mono subgraphs_of_union(1))

definition reverse :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph" ("(_\<^sup>R)" [1000] 999) where
"reverse a = \<lparr>pverts = pverts a, parcs = (parcs a)\<inverse>\<rparr>"

lemma wf_reverse: "pair_wf_digraph g \<Longrightarrow> pair_wf_digraph (g\<^sup>R)"
  unfolding reverse_def
  by (smt (verit, ccfv_SIG) converseE fst_swap pair_pre_digraph.select_convs(1)
      pair_pre_digraph.select_convs(2) pair_wf_digraph_def swap_simp)

lemma arc_reverse: "x\<rightarrow>\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def)

lemma reach_reverse: "x\<rightarrow>\<^sup>*\<^bsub>with_proj g\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>g\<^sup>R\<^esub>x"
  by (simp add: reverse_def reachable_def rtrancl_on_converseI)

section \<open>Suppressing an element from a permutation\<close>

definition skip :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"skip z f \<equiv> \<lambda> x. (if x = z then z else (if f x = z then f z else f x))"

lemma skip_id: "skip z f z = z"
  unfolding skip_def by simp

lemma skip_invariant: "x \<noteq> z \<Longrightarrow> f x \<noteq> z \<Longrightarrow> skip z f x = f x"
  unfolding skip_def by simp

lemma inj_skip: "inj f \<Longrightarrow> inj (skip z f)"
  unfolding skip_def by (smt (verit, ccfv_SIG) injD inj_on_def)

definition skip_perm :: "'a \<Rightarrow> 'a perm \<Rightarrow> 'a perm" where
"skip_perm \<equiv> (\<lambda>z (p ::'a perm). Perm (skip z p))"

lemma apply_skip_perm: "(\<langle>$\<rangle>) (skip_perm z p) = skip z p"
unfolding skip_perm_def
proof
  obtain A where "A = set_perm p" by simp
  fix x show "(Perm (skip z p)) \<langle>$\<rangle> x = skip z p x"
  proof (rule apply_perm_Perm)
    show "finite A" by (simp add: \<open>A = set_perm p\<close>)
    show "inj_on (skip z ((\<langle>$\<rangle>) p)) A"
      by (meson inj_skip inj_on_apply_perm inj_on_subset subset_UNIV)
    show "\<And>x. x \<in> A \<Longrightarrow> skip z p x \<in> A"
      by (metis \<open>A = set_perm p\<close> apply_set_perm skip_def)
    show "\<And>x. x \<notin> A \<Longrightarrow> skip z p x = x"
      by (metis \<open>A = set_perm p\<close> in_set_permI skip_def)
   qed
qed

lemma skip_perm_notin: "z \<notin> set_perm p \<Longrightarrow> skip_perm z p = p"
  by (smt (z3) apply_perm_inverse_eq_iff apply_perm_inverse_not_in_set apply_skip_perm perm_eq_iff skip_def)

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
          by (smt (verit, ccfv_threshold) Diff_iff Permutations.permutes_not_in y_skip assms empty_iff
              image_iff injD insert_iff permutes_inj skip_def)
    next
      case False
      then have "skip z f y = f y \<or> skip z f y = f z"
        by (simp add: skip_def)
      then show ?thesis
        by (smt (verit, ccfv_SIG) y_skip Diff_iff False assms empty_iff image_iff insert_iff
            permutes_in_image skip_def)
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

lemma rotate_remove1:
  assumes "distinct l"
  shows "\<exists>m. rotate m (remove1 a l) = remove1 a (rotate n l)"
proof (cases "l = []")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
  proof (induction n)
    case 0 then show ?case
      by (metis funpow_0 rotate_def)
  next
    case (Suc n)
    then obtain m where *: "rotate m (remove1 a l) = remove1 a (rotate n l)" by auto
    have "a = hd l \<Longrightarrow> remove1 a l = remove1 a (rotate1 l)"
      by (metis Diff_iff Suc.prems append_Nil2 assms hd_Cons_tl insertCI remove1.simps(2)
          remove1_append rotate1_hd_tl set_remove1_eq)
    then have "a = hd (rotate n l) \<Longrightarrow> rotate m (remove1 a l) = remove1 a (rotate (Suc n) l)"
      by (metis * rotate_Suc append_Nil2 assms distinct_remove1_removeAll distinct_rotate
          list.exhaust_sel removeAll.simps(2) removeAll_append rotate1.simps(2) rotate_is_Nil_conv)
    also have "a \<noteq> hd l \<Longrightarrow> rotate1 (remove1 a l) = remove1 a (rotate1 l)"
      by (smt (z3) Suc.prems hd_Cons_tl insert_iff list.simps(15) remove1.simps(2) remove1_append
          remove1_idem rotate1.simps(2) set_rotate1)
    then have "a \<noteq> hd (rotate n l) \<Longrightarrow> rotate (Suc m) (remove1 a l) = remove1 a (rotate (Suc n) l)"
        by (simp; smt (z3) * insert_iff list.exhaust_sel list.set(2) remove1.simps(2) remove1_append
              remove1_idem rotate1.simps(2) rotate_is_Nil_conv set_rotate1)
    then show ?case using calculation by blast
  qed
qed                                  

text \<open>Need to set xs to [] if length is 2 to satisfy rel_cycle\<close>
lift_definition remove1_cycle :: "'a \<Rightarrow> 'a cycle \<Rightarrow> 'a cycle" is 
  "\<lambda>a xs. let xs' = remove1 a xs in (if length xs' = 1 then [] else xs')"
proof (auto simp add: cycle_rel_def)
  fix a::"'a" and l::"'a list" assume assms: "distinct l" "length l \<noteq> Suc 0"
  show "distinct (let xs' = remove1 a l in if length xs' = Suc 0 then [] else xs')"
    by (metis (full_types) assms(1) distinct.simps(1) distinct_remove1)
  show "length (let xs' = remove1 a l in if length xs' = Suc 0 then [] else xs') = Suc 0 \<Longrightarrow> False"
    by (metis (full_types) One_nat_def less_numeral_extra(1) less_numeral_extra(3) list.size(3))
  fix n show "\<exists>na. rotate na (let xs' = remove1 a l in if length xs' = Suc 0 then [] else xs')
              = (let xs' = remove1 a (rotate n l) in if length xs' = Suc 0 then [] else xs')"
    using \<open>distinct l\<close> rotate_remove1 by (smt (z3) length_rotate rotate_is_Nil_conv)
qed

lemma remove1_cycle_noteq: "x \<in> set_cycle c \<longleftrightarrow> remove1_cycle x c \<noteq> c"
proof
  show "x \<in> set_cycle c \<Longrightarrow> remove1_cycle x c \<noteq> c"
    apply transfer
    by (metis (mono_tags) One_nat_def Suc_pred cycle_rel_def cycle_rel_imp_same_set empty_iff
        length_pos_if_in_set length_remove1 length_rotate lessI list.set(1) order_less_irrefl)
  show "remove1_cycle x c \<noteq> c \<Longrightarrow> x \<in> set_cycle c"
    apply transfer
    using remove1_idem by force
qed

lemma cycles_skip:
  assumes "z \<in> set_perm p"
  shows "cycles_of_perm p = cycles_of_perm (skip_perm z p) \<union>
       {perm_orbit p z} - {remove1_cycle z (perm_orbit p z)}" (is "?C = ?C' \<union> {?poz} - {?poz'}")
proof (rule subset_antisym; rule subsetI)
  have disj: "disjoint_cycles ?C" "disjoint_cycles ?C'" by auto
  have poz_subset: "set_cycle ?poz' \<subseteq> set_cycle ?poz"
      apply transfer by (smt (z3) set_remove1_subset empty_subsetI list.set(1))
  {
    fix x assume "x \<in> ?C"
      then have "z \<notin> set_cycle x \<Longrightarrow> x \<in> ?C'"
        by (smt (verit, ccfv_threshold) apply_skip_perm skip_invariant apply_set_perm cycles_of_perm_altdef
            mem_Collect_eq set_perm_cycle)
      also have x_orbit: "z \<in> set_cycle x \<Longrightarrow> x = perm_orbit p z"
        using \<open>x \<in> cycles_of_perm p\<close> perm_orbit_eqI by fastforce
      have "?poz \<noteq> ?poz'" 
          by (metis apply_perm_neq_idI assms remove1_cycle_noteq start_in_perm_orbit_iff)
      hence "x \<noteq> ?poz'"
          by (smt (verit, ccfv_SIG) poz_subset \<open>x \<in> ?C\<close> x_orbit apply_perm_neq_idI cycles_funpow cycles_of_perm_def
              funpow_apply_perm_in_perm_orbit_iff imageE in_mono start_in_perm_orbit calculation disj)
      then show "x \<in> ?C' \<union> {?poz} - {?poz'}"
        using x_orbit calculation by blast
  }
  fix x assume x_in: "x \<in> ?C' \<union> {?poz} - {?poz'}"    
  also have "?poz \<in> ?C"
    using assms by (rule perm_orbit_in_cycles_of_perm)
  moreover have "x \<noteq> ?poz' \<Longrightarrow> x \<in> ?C' \<Longrightarrow> x \<in> ?C"
    sorry
  ultimately show "x \<in> ?C"
    using x_in by blast
qed

corollary skip_cycles_card: "card (cycles_of_perm (skip_perm z p)) \<le> card (cycles_of_perm p)"
  by (smt (z3) cycles_skip Diff_iff Diff_insert_absorb Un_insert_right apply_perm_neq_idI
      boolean_algebra_cancel.sup0 card_Diff_insert card_eq_0_iff card_insert_if card_mono
      cycles_of_perm_altdef finite_cycles_of_perm in_set_permI insert_absorb insert_not_empty
      mem_Collect_eq nat.simps(3) perm_orbit_eqI perm_orbit_in_cycles_of_perm skip_perm_notin
      start_in_perm_orbit_iff subset_eq)

section \<open>Pair digraph of a function\<close>

definition Gr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a pair_pre_digraph" where
"Gr S f = \<lparr>pverts = S, parcs = {(a, f a) | a. a \<in> S}\<rparr>"

lemma Gr_eq: "a\<rightarrow>\<^bsub>Gr S f\<^esub> b \<longleftrightarrow> a \<in> S \<and> f a = b"
  unfolding Gr_def by auto

lemma Gr_wf:
  assumes "\<forall>a \<in> S. f a \<in> S"
  shows "pair_wf_digraph (Gr S f)"
  by (simp add: Fun_Graph.Gr_def assms pair_wf_digraph_def)

lemma funpow_in_rtrancl:
  assumes "a \<in> S" "\<forall> x \<in> S. f x \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S f\<^esub>(f ^^ n) a"
proof (induct n)
  let ?G = "Gr S f"
  case 0
  then show ?case using assms by (simp add: Fun_Graph.Gr_def reachable_def)
next
  case (Suc n)
  then show ?case
    by (smt (verit, del_insts) assms Gr_eq Fun_Graph.Gr_def funpow_simp_l pair_pre_digraph.simps(1)
        reachable_def rtrancl_on.simps with_proj_simps(1))
qed

locale perm_on =
  fixes p :: "'a perm" and S :: "'a set"
  assumes permutes_p: "p permutes S" and finite_S: "finite S"
begin

interpretation pair_wf_digraph "Gr S p"
  by (simp add: Fun_Graph.Gr_def pair_wf_digraph_def permutes_p permutes_in_image)

lemma reach_iff_funpow:
  assumes "a \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>b \<longleftrightarrow> (\<exists>n. (((\<langle>$\<rangle>) p) ^^ n) a = b)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
  proof (induct rule: reachable_induct)
    case base
    then show ?case by (meson funpow_0)
  next
    case (step x y)
    then obtain n where "(((\<langle>$\<rangle>) p) ^^ n) a = x" by auto
    also have "p x = y" by (metis Gr_eq step.hyps(2) with_proj_simps(3))
    ultimately show ?case by (metis funpow_simp_l)
  qed
next
  assume *: ?R
  then obtain n where "((\<langle>$\<rangle>) p ^^ n) a = b" by auto
  then show ?L using assms funpow_in_rtrancl
    by (metis (no_types, lifting) Fun_Graph.Gr_def Gr_eq in_arcsD2 pair_pre_digraph.simps(1) with_proj_simps(3))
qed

lemma perm_cycles_iff_reach:
  assumes "x \<noteq> y"
  shows "y \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y" (is "?L \<longleftrightarrow> ?R")
proof
  assume *: ?L
  then obtain n where "(apply_perm p ^^ n) y = x"
     using cycles_funpow by fast
   then show ?R
     by (smt (verit, del_insts) * perm_on.permutes_p perm_on_axioms reach_iff_funpow Permutations.permutes_not_in
        apply_perm_power funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff 
        set_cycle_ex_funpow start_in_perm_orbit_iff)
next
  assume *: ?R
  then obtain n where "(apply_perm p ^^ n) x = y"
    by (metis (no_types, lifting) Fun_Graph.Gr_def reach_iff_funpow pair_pre_digraph.simps(1) reachable_in_verts(1))
  then show ?L
    by (metis assms funpow_apply_perm_in_perm_orbit_iff id_funpow_id start_in_perm_orbit_iff)
qed

lemma perm_reach_sym: "x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y \<Longrightarrow> y\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>x"
proof (induct rule: reachable_induct)
case base
  then show ?case by simp
next
  let ?G = "Gr S p"
  case (step x y)
  then have "y \<rightarrow>\<^sup>*\<^bsub>?G\<^esub> x"
    by (smt (verit, best) Fun_Graph.Gr_def adj_in_verts(2) apply_perm_power funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff pair_pre_digraph.simps(1) perm_cycles_iff_reach reach_iff_funpow reachable_adjI reachable_in_verts(1) reachable_refl set_cycle_ex_funpow)
  then show ?case by (meson reachable_trans step.hyps(3))
qed

end
end