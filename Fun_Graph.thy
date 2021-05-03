theory Fun_Graph
  imports "Extras"
begin

text \<open>Pair digraph of a function\<close>
definition Gr :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a pair_pre_digraph" where
"Gr S f = \<lparr>pverts = S, parcs = {(a, f a) | a. a \<in> S}\<rparr>"

lemma Gr_pverts [simp]: "pverts (Gr S f) = S"
  by (simp add: Fun_Graph.Gr_def)

lemma Gr_parcs [simp]: "parcs (Gr S f) = {(a, f a) | a. a \<in> S}"
  by (simp add: Fun_Graph.Gr_def)

lemma Gr_verts [simp]: "verts (with_proj (Gr S f)) = S"
  by simp

lemma Gr_arcs [simp]: "arcs (with_proj (Gr S f)) = {(a, f a) | a. a \<in> S}"
  by (simp add: Fun_Graph.Gr_def)

lemma Gr_eq: "a\<rightarrow>\<^bsub>Gr S f\<^esub> b \<longleftrightarrow> a \<in> S \<and> f a = b"
  unfolding Gr_def by auto

lemma Gr_wf:
  assumes "\<forall>a \<in> S. f a \<in> S"
  shows "pair_wf_digraph (Gr S f)"
  by (simp add: Fun_Graph.Gr_def assms pair_wf_digraph_def)

corollary Gr_wf_perm: "(p :: 'a perm) permutes S \<Longrightarrow> pair_wf_digraph (Gr S p)"
  by (simp add: Gr_wf permutes_in_image)

lemma Gr_finite:
  assumes "finite S" "wf_digraph (Gr S f)"
  shows "fin_digraph (Gr S f)"
  apply (intro_locales)
  unfolding fin_digraph_axioms_def using assms by auto

lemma funpow_in_rtrancl:
  assumes "a \<in> S" "\<forall> x \<in> S. f x \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S f\<^esub>(f ^^ n) a"
proof (induct n)
  case 0
  then show ?case using assms by (simp add: Fun_Graph.Gr_def reachable_def)
next
  case (Suc n)
  then have "(f ^^ n) a \<rightarrow>\<^sup>*\<^bsub>Gr S f\<^esub> (f ^^ (Suc n)) a"
    by (metis assms(2) Gr_eq Gr_verts Gr_wf funpow_simp_l reachable_in_vertsE 
        wf_digraph.reachable_adjI wf_digraph_wp_iff)
  then show ?case
    by (metis (no_types, lifting) Gr_eq Gr_verts Suc funpow_simp_l reachable_def
        reachable_in_vertsE rtrancl_on.rtrancl_on_into_rtrancl_on)
qed

lemma reach_iff_funpow:
  assumes "a \<in> S" "\<forall>x \<in> S. f x \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S f\<^esub>b \<longleftrightarrow> (\<exists>n. (f ^^ n) a = b)" (is "?L \<longleftrightarrow> ?R")
proof
  interpret wf_digraph "Gr S f"
    by (simp add: Gr_wf assms(2) wf_digraph_wp_iff)
  assume ?L then show ?R
  proof (induct rule: reachable_induct)
    case base
    then show ?case by (meson funpow_0)
  next
    case (step x y)
    then obtain n where "(f ^^ n) a = x" by auto
    also have "f x = y" by (metis Gr_eq step.hyps(2) with_proj_simps(3))
    ultimately show ?case by (metis funpow_simp_l)
  qed
next
  assume *: ?R
  then obtain n where "(f ^^ n) a = b" by auto
  then show ?L
    using assms funpow_in_rtrancl by meson
qed


section \<open>Graph of a permutation\<close>
context perm_on
begin

interpretation Gr: pair_wf_digraph "Gr S p"
  by (simp add: Fun_Graph.Gr_def pair_wf_digraph_def permutes_p permutes_in_image)

lemma Gr_reverse_eq_inv: "(Gr S p)\<^sup>R = Gr S (inv p)"
proof (simp add: Gr_def reverse_def; rule; rule)
  fix x assume *: "x \<in> {(a, p \<langle>$\<rangle> a) |a. a \<in> S}\<inverse>"
  then obtain a b where "(a,b) = x" by auto
  then have "a = p b" using * converseI by auto
  hence "b = (inv p) a" by (metis permutes_inverses(2) permutes_p)
  then show "x \<in> {(a, inv ((\<langle>$\<rangle>) p) a) |a. a \<in> S}"
    using * \<open>(a,b) = x\<close> bij_betwE permutes_imp_bij permutes_p by fastforce
next
  fix x assume *: "x \<in> {(a, inv ((\<langle>$\<rangle>) p) a) |a. a \<in> S}"
  then obtain a b where "(a,b) = x" by auto
  then have "a = p b"
    by (smt (verit, del_insts) * Pair_inject mem_Collect_eq permutes_inv_eq permutes_p)
  then have "(b,a) \<in> {(a, p \<langle>$\<rangle> a) |a. a \<in> S}"
    using * \<open>(a,b) = x\<close> permutes_not_in permutes_p by fastforce
  then show "x \<in> {(a, p \<langle>$\<rangle> a) |a. a \<in> S}\<inverse>"
    using \<open>(a,b) = x\<close> by auto
qed

lemma reach_iff_funpow_perm:
  assumes "a \<in> S"
  shows "a\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>b \<longleftrightarrow> (\<exists>n. ((\<langle>$\<rangle>) p ^^ n) a = b)"
  by (simp add: assms permutes_in_image permutes_p reach_iff_funpow)

lemma perm_cycles_iff_reach:
  assumes "x \<noteq> y"
  shows "y \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y" (is "?L \<longleftrightarrow> ?R")
proof
  assume *: ?L
  then obtain n where "(apply_perm p ^^ n) y = x"
     using cycles_funpow by fast
   then show ?R
     by (smt (verit, del_insts) * perm_on.permutes_p perm_on_axioms reach_iff_funpow_perm
         Permutations.permutes_not_in apply_perm_power funpow_apply_cycle_perm_orbit
         funpow_apply_perm_in_perm_orbit_iff set_cycle_ex_funpow start_in_perm_orbit_iff)
next
  assume *: ?R
  then obtain n where "(apply_perm p ^^ n) x = y"
    by (metis (no_types, lifting) Fun_Graph.Gr_def reach_iff_funpow_perm pair_pre_digraph.simps(1)
        Gr.reachable_in_verts(1))
  then show ?L
    by (metis assms funpow_apply_perm_in_perm_orbit_iff id_funpow_id start_in_perm_orbit_iff)
qed

lemma perm_reach_sym: "Gr.connect_sym"
proof (auto simp: Gr.connect_sym_def)
  fix a b assume "a \<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub> b"
  then show "b \<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub> a"
proof (induct rule: Gr.reachable_induct)
case base
  then show ?case by simp
next
  let ?G = "Gr S p"
  case (step x y)
  then have "y \<rightarrow>\<^sup>*\<^bsub>?G\<^esub> x"
    by (smt (verit, best) Fun_Graph.Gr_def Gr.adj_in_verts(2) apply_perm_power
        funpow_apply_cycle_perm_orbit funpow_apply_perm_in_perm_orbit_iff pair_pre_digraph.simps(1)
        perm_cycles_iff_reach reach_iff_funpow_perm Gr.reachable_adjI Gr.reachable_in_verts(1) 
        Gr.reachable_refl set_cycle_ex_funpow)
  then show ?case by (meson Gr.reachable_trans step.hyps(3))
qed
qed
end

section \<open>Graph of a cycle\<close>
lemma wf_digraph_cycle: "wf_digraph (Gr (set_cycle c) (apply_cycle c))"
  by (simp add: Gr_wf wf_digraph_wp_iff)

lemma strongly_connected_cycle:
  assumes "c \<noteq> id_cycle"
  shows "strongly_connected (Gr (set_cycle c) (apply_cycle c))" (is "strongly_connected ?G")
proof
  show "verts ?G \<noteq> {}"
    using assms by simp
  fix u v assume "u \<in> verts ?G" "v \<in> verts ?G"
  then show "u \<rightarrow>\<^sup>*\<^bsub>?G\<^esub> v"
    by (metis Gr_verts apply_cycle_in_set_iff funpow_in_rtrancl set_cycle_ex_funpow)
qed

lemma (in perm_on) perm_orbit_subgraph:
  assumes "orb \<in> cycles_of_perm p"
  shows "subgraph (with_proj (Gr (set_cycle orb) (apply_cycle orb))) (with_proj (Gr S p))"
proof (auto simp: subgraph_def)
  show "x \<in> S" if "x \<in> set_cycle orb" for x
    using assms set_cycle_of_perm_subset set_perm_subset that by blast
  then show "apply_cycle orb x = p \<langle>$\<rangle> x" "x \<in> S" if "x \<in> set_cycle orb" for x
    by (simp_all add: assms that)
  show "wf_digraph (with_proj (Gr S p))"
    by (simp add: Gr_wf_perm permutes_p wf_digraph_wp_iff)
  show "wf_digraph (with_proj (Gr (set_cycle orb) (apply_cycle orb)))"
    by (simp add: wf_digraph_cycle)
qed

lemma (in perm_on) perm_orbit_induced_subgraph:
  assumes "orb \<in> cycles_of_perm p"
  shows "induced_subgraph (with_proj (Gr (set_cycle orb) (apply_cycle orb))) (with_proj (Gr S p))"
    (is "induced_subgraph ?orbit ?G")
proof (auto simp add: induced_subgraph_def)
  show subgraph: "subgraph ?orbit ?G"
    by (simp add: assms perm_orbit_subgraph)
  fix a assume *: "a \<in> set_cycle orb"
  then show "apply_cycle orb a = p \<langle>$\<rangle> a" "a \<in> S"
    apply (simp_all add: assms)
    using subgraph by fastforce
  from * show "p \<langle>$\<rangle> a = apply_cycle orb a"
    by (simp add: \<open>apply_cycle orb a = p \<langle>$\<rangle> a\<close>)
qed

lemma (in perm_on) perm_id_subgraph:
  assumes "c \<notin> set_perm p" "c \<in> S"
  shows "subgraph (with_proj (Gr {c} id)) (with_proj (Gr S p))"
  by (auto simp: subgraph_def assms apply_perm_eq_same_iff(2) Gr_wf  Gr_wf_perm
      permutes_p wf_digraph_wp_iff)

lemma (in perm_on) perm_id_induced_subgraph:
  assumes "c \<notin> set_perm p" "c \<in> S"
  shows "induced_subgraph (with_proj (Gr {c} id)) (with_proj (Gr S p))"
  by (auto simp: assms induced_subgraph_def perm_id_subgraph apply_perm_eq_same_iff(2))

subsection \<open>Connected components of a permutation\<close>
context perm_on begin

interpretation Gr: pair_wf_digraph "Gr S p"
  by (simp add: Fun_Graph.Gr_def pair_wf_digraph_def permutes_p permutes_in_image)

lemma sccs_perm:
  "Gr.sccs = (\<lambda>c. with_proj (Gr (set_cycle c) (cycle_perm c))) ` (cycles_of_perm p)
                 \<union> (\<lambda>c. with_proj (Gr {c} id)) ` {x \<in> S. p x = x}" (is "Gr.sccs = ?C \<union> ?Id")
proof (rule subset_antisym; rule subsetI)
  fix x assume "x \<in> Gr.sccs"
  then have x_scc: "induced_subgraph x (Gr S p)" "strongly_connected x"
    "\<not> (\<exists>d. induced_subgraph d (Gr S p) \<and> strongly_connected d \<and> verts x \<subset> verts d)"
    by auto
  then obtain v where "v \<in> verts x"
    by (meson all_not_in_conv x_scc strongly_connected_def)
  then show "x \<in> ?C \<union> ?Id"
  proof (cases "p v = v")
    case True
    then have "verts x = {v}"
    proof -
      { fix u assume "u \<in> verts x" "u \<noteq> v"
        then have "False"
          by (metis Gr.reachable_mono True \<open>v \<in> verts x\<close> emptyE id_cycle_eq_perm_orbit_iff
              induced_imp_subgraph perm_on.perm_cycles_iff_reach perm_on_axioms set_cycle_id
              strongly_connected_def x_scc(1) x_scc(2))
      } then show "verts x = {v}"
        using \<open>v \<in> verts x\<close> by blast
    qed
    then have "x \<in> ?Id"
      by (smt (verit, ccfv_SIG) Gr.induce_eq_iff_induced Gr_verts True \<open>v \<in> verts x\<close>
          apply_perm_neq_idI image_iff in_mono induced_imp_subgraph mem_Collect_eq 
          perm_on.perm_id_induced_subgraph perm_on_axioms subgraph_imp_subverts x_scc(1))
    then show "x \<in> ?C \<union> ?Id"
      by simp
  next
    case False
    then have "v \<in> set_perm p"
      by auto
    define cycle_v where "cycle_v \<equiv> perm_orbit p v"
    then have "cycle_v \<in> cycles_of_perm p"
    using perm_orbit_in_cycles_of_perm \<open>v \<in> set_perm p\<close> by blast
  also have "x = with_proj (Gr (set_cycle cycle_v) (apply_cycle cycle_v))"
    by (smt (verit) x_scc \<open>v \<in> verts x\<close> Gr.induce_eq_iff_induced Gr_pverts apply_cycle_perm_orbit'
        apply_cycle_same_iff calculation cycle_v_def id_cycle_eq_perm_orbit_iff
        induced_imp_subgraph perm_on.perm_cycles_iff_reach perm_on_axioms
        perm_orbit_in_cycles_of_perm_iff perm_orbit_induced_subgraph pre_digraph.reachable_mono
        psubsetI strongly_connected_cycle strongly_connected_def subset_iff with_proj_simps(1))
  ultimately show "x \<in> ?C \<union> ?Id"
    by simp
  qed
next
  fix G assume "G \<in> ?C \<union> ?Id"
  then consider (cycle) "G \<in> ?C" | (id) "G \<in> ?Id"
    by auto
  then show "G \<in> Gr.sccs"
  proof (cases)
    case cycle
    assume G_in:"G \<in> (\<lambda>c. with_proj (Gr (set_cycle c) ((\<langle>$\<rangle>) (cycle_perm c)))) ` cycles_of_perm p"
    then obtain x 
      where x_cycle: "x \<in> cycles_of_perm p" "G = with_proj (Gr (set_cycle x) (apply_cycle x))"
      by force
  {
    fix H assume *: "induced_subgraph H (Gr S p)" "strongly_connected H" "verts G \<subset> verts H"
    then have "False"
    proof -
      from *(3) obtain v where "v \<in> verts H \<and> v \<notin> verts G"
        by auto
      also obtain u where "u \<in> verts G"
        using cycle by fastforce
      then have "\<exists>n. (((\<langle>$\<rangle>) p) ^^ n) v = u"
        by (metis (no_types, hide_lams) * Gr.reachable_mono Gr_pverts calculation 
            perm_on.reach_iff_funpow_perm perm_on_axioms strongly_connected_def
            subgraph_imp_subverts subsetD with_proj_simps(1) induced_imp_subgraph psubsetE) 
      then show "False"
        by (smt (verit, ccfv_threshold) cycle Gr_verts \<open>u \<in> verts G\<close> 
            calculation cycles_of_perm_def funpow_apply_perm_in_perm_orbit_iff image_iff )
    qed
  }
  then show "G \<in> Gr.sccs"
    apply (auto simp: Gr.sccs_def G_in)
    apply (simp add: x_cycle G_in perm_orbit_induced_subgraph perm_on_axioms)
    apply (metis x_cycle id_cycle_not_in_cycles_of_perm strongly_connected_cycle)
    done
  next
    case id
    then obtain c where c_def: "c \<in> S" "p c = c" "G \<equiv> with_proj (Gr {c} id)"
      by auto
    then have "wf_digraph G"
      by (simp add: Gr_wf wf_digraph_wp_iff)
  {
    fix H assume *: "induced_subgraph H (Gr S p)" "strongly_connected H" "verts G \<subset> verts H"
    then have "False"
    proof -
      from *(3) obtain v where "v \<in> verts H" "v \<notin> verts G"
        by auto
      then have "\<exists>n. (((\<langle>$\<rangle>) p) ^^ n) v = c"
        by (metis (mono_tags, lifting) * c_def(3) Gr.reachable_mono Gr_verts \<open>p \<langle>$\<rangle> c = c\<close>
            induced_imp_subgraph insertCI perm_on.perm_cycles_iff_reach perm_on_axioms
            perm_orbit_eq_id_cycle_iff psubsetE set_cycle_id strongly_connectedE subsetD)
      then show "False"
        by (metis \<open>v \<notin> verts G\<close> \<open>p c = c\<close> c_def(3) Gr_verts apply_inj_eq_iff apply_perm_power 
            id_funpow_id insert_iff)
    qed
  }
  then show "G \<in> Gr.sccs"
    apply (auto simp: Gr.sccs_def c_def(3))
    apply (meson apply_perm_neq_idI c_def(1) c_def(2) perm_id_induced_subgraph)
    unfolding strongly_connected_def using \<open>wf_digraph G\<close>
    apply (simp add: wf_digraph.reachable_refl Fun_Graph.Gr_def c_def(3))
    done
  qed
qed

lemma sccs_set_perm:
  assumes "S = set_perm p"
  shows "Gr.sccs = (\<lambda>c. with_proj (Gr (set_cycle c) (cycle_perm c))) ` (cycles_of_perm p)"
proof -
  from assms have "{x \<in> S. p x = x} = {}"
    by blast
  then show ?thesis
    using sccs_perm by auto
qed

lemma scc_of_orbit: 
  assumes "x \<in> S"
  shows "Gr.scc_of x = (if p \<langle>$\<rangle> x = x then {x} else set_cycle (perm_orbit p x))"
proof (cases "p \<langle>$\<rangle> x = x")
  case True
  {
    assume "Gr.scc_of x \<noteq> {x}"
    then obtain y where "y \<noteq> x" "x\<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub>y"
      using Gr.scc_of_def Collect_cong Gr.in_scc_of_self Gr_pverts assms by fastforce
    then have "x = y"
      by (metis True assms funpow_apply_perm_in_perm_orbit_iff perm_on.perm_cycles_iff_reach
          perm_on.reach_iff_funpow_perm perm_on_axioms start_in_perm_orbit_iff)
    then have "False" using \<open>y \<noteq> x\<close> by auto
  }
  then show ?thesis using True by auto
next
  case False
  have "Gr.scc_of x = set_cycle (perm_orbit p x)"
  proof (rule subset_antisym; rule subsetI)
    fix y assume "y \<in> Gr.scc_of x"
    then have "y \<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub> x \<and> x \<rightarrow>\<^sup>*\<^bsub>Gr S p\<^esub> y"
      using Gr.in_scc_of_self Gr.in_sccs_verts_conv_reachable Gr.scc_of_in_sccs_verts assms by auto
    then show "y \<in> set_cycle (perm_orbit p x)"
      by (metis False perm_cycles_iff_reach start_in_perm_orbit)
  next
    fix y assume "y \<in> set_cycle (perm_orbit p x)"
    then show "y \<in> Gr.scc_of x"
      by (metis (full_types, lifting) Gr.connect_sym_def Gr.scc_of_def Gr.wf_digraph_axioms
          Gr_pverts assms mem_Collect_eq perm_cycles_iff_reach perm_reach_sym 
          wf_digraph.reachable_refl with_proj_simps(1))
  qed
  then show ?thesis
    using False by presburger
qed
end
end