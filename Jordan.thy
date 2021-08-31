theory Jordan
  imports Walkup
begin

theorem even_genus: "hypermap H \<Longrightarrow> even (genus H)"
proof (induct "card (darts H)" arbitrary: H)
  case 0
  then interpret H: hypermap H by simp
  have "darts H = {}"
    by (metis 0 card_eq_0_iff hypermap_def)
  then have "verts (glink H) = {}"
    by (simp add: cedge_def cface_def cnode_def glink_def)
  then have "pre_digraph.sccs (glink H) = {}"
    apply auto
    by (metis \<open>verts (with_proj (glink H)) = {}\<close> pre_digraph.in_sccsE
      pre_digraph.induced_subgraph_altdef strongly_connected_def subgraph_imp_subverts subset_empty)
  then have "euler_lhs H = 0"
    by (simp add: "0.hyps" euler_lhs_def)
  also have "euler_rhs H = 0"
    unfolding euler_rhs_def
    by (metis H.perm_edge H.perm_face H.perm_node \<open>darts H = {}\<close> add_eq_0_iff_both_eq_0 
        perm_on.count_cycles_on_empty perm_on.intro)
  ultimately have "genus H = 0" 
    unfolding genus_def by presburger
  then show ?case by auto
next
  case (Suc x)
  then obtain d where "d \<in> darts H"
    by fastforce
  then interpret H': walkup H d
    by (simp add: Suc.prems walkup.intro walkup_axioms.intro)
  have "even (genus (walkupE H d))"
    by (metis H'.H'_def H'.card_darts_walkup H'.hypermap_walkupE Suc.hyps diff_Suc_1)
  then show "even (genus H)"
    by (simp add: H'.H'_def H'.even_genus_walkupE)
qed

(********************* Excerpt from jordan.v **********************************)
(*  For the induction we consider the following cases for the reduction       *)
(*  1) a dart not in p, with an E-transform                                   *)
(*  2) x with an E-transform if x is followed by an N-link (i.e., x = node y) *)
(*  3) y = face x with an F-transform, if y is followed by an N-link.         *)
(*  4) y with an E-transform, if y != t (by 3), z = face y)                   *)
(*  5) y with an N-transform, if y != node x                                  *)
(*  6) z with an E-transform, if z is followed by an F-link in p              *)
(*  7) z with an F-transform, otherwise (z is followed by an N-link in p)     *)
(******************************************************************************)

theorem planar_Jordan: "\<lbrakk>hypermap H; planar H\<rbrakk> \<Longrightarrow> hypermap.jordan H"
proof (induct "card (darts H)" arbitrary: H)
  case 0
  then have "verts (clink H) = {}"
    by (metis card_0_eq hypermap.finite_darts hypermap.verts_clink)
  then have "\<And>p. set p \<subseteq> verts (clink H) \<Longrightarrow> p = []"
    by force
  then show ?case
    by (metis "0.prems"(1) hypermap.jordan_def hypermap.moebius_path.elims(2) vpathE vwalk_def)
next
  case (Suc n)
  then interpret H: hypermap H by simp
  have IHe: "z \<in> darts H \<Longrightarrow> hypermap.jordan (walkupE H z)" for z
    by (metis H.finite_darts H.hypermap_axioms Suc.hyps Suc.prems(2) card_Diff_singleton
        diff_Suc_1 pre_hypermap.select_convs(1) walkup.H'_def hypermap.hypermap_walkupE walkup.intro
        walkup.planar_walkupE walkupE_def walkup_axioms.intro)
  have IHn: "z \<in> darts H \<Longrightarrow> hypermap.jordan (walkupN H z)" for z
    by (metis H.finite_darts H.hypermap_axioms H.hypermap_permN Suc.hyps Suc.prems(2)
        card_Diff_singleton diff_Suc_1 hypermap.hypermap_permF walkup.darts_walkupN walkupN_def
        hypermap.hypermap_walkupE walkup.intro walkup.planar_walkupN walkup_axioms.intro)    
  have IHf: "z \<in> darts H \<Longrightarrow> hypermap.jordan (walkupF H z)" for z
    by (metis H.finite_darts H.hypermap_axioms H.hypermap_permF Suc.hyps Suc.prems(2)
        card_Diff_singleton diff_Suc_1 hypermap.hypermap_permN walkup.darts_walkupF walkupF_def
        hypermap.hypermap_walkupE walkup.intro walkup.planar_walkupF walkup_axioms.intro)
  
  have liftE: "\<lbrakk>z \<notin> set p; vpath p (clink H)\<rbrakk> \<Longrightarrow> vpath p (clink (walkupE H z))" for p z
    unfolding vpath_def
  proof (auto; rule vwalkI; rule)
    define H' where "H' = walkupE H z"
    assume *: "z \<notin> set p" "vwalk p (clink H)" "distinct p"
    { fix x assume "x \<in> set p"
      then have "x \<noteq> z"
        using *(1) by blast
      also have "x \<in> darts H"
        using "*"(2) H.verts_clink \<open>x \<in> set p\<close> by blast
      ultimately show "x \<in> verts (clink H')"
        by (metis Diff_iff H'_def H.hypermap_walkupE distinct.simps(2) distinct_singleton 
            empty_set hypermap.verts_clink insert_iff pre_hypermap.select_convs(1) walkupE_def)
    }
    {
      fix x assume **: "x \<in> set (vwalk_arcs p)"
      then obtain u v where "(u,v) = x"
        by (metis surj_pair)
      then have "face H u = v \<or> node H v = u"
        by (metis "*"(2) H.arc_clink H.verts_clink \<open>x \<in> set (vwalk_arcs p)\<close>
            in_set_vwalk_arcsE subsetD vwalkE)
      also have "u \<noteq> z \<and> v \<noteq> z"
        by (metis *(1) \<open>(u, v) = x\<close> \<open>x \<in> set (vwalk_arcs p)\<close> in_set_vwalk_arcsE)
      ultimately have "face H' u = v \<or> node H' v = u"
        by (metis H'_def pre_hypermap.select_convs(3) pre_hypermap.select_convs(4) 
            skip_perm_invariant walkupE_def)
      then show "x \<in> arcs_ends (clink H')"
        by (metis ** H'_def H.hypermap_walkupE \<open>(u, v) = x\<close> hypermap.verts_clink in_set_vwalk_arcsE
            \<open>\<And>x. x \<in> set p \<Longrightarrow> x \<in> verts (with_proj (clink H'))\<close> hypermap.arc_clink)
    }
    show "p = [] \<Longrightarrow> False"
      using "*"(2) by blast
  qed

  have liftN: "\<lbrakk>z \<notin> set (x#p); face H z \<notin> set p; vpath (x#p) (clink H)\<rbrakk>
                \<Longrightarrow> vpath (x#p) (clink (walkupN H z))" for p x z
  unfolding vpath_def
  proof (simp; rule vwalkI; rule; auto)
    assume *: "face H z \<notin> set p" "z \<noteq> x" "z \<notin> set p" "vwalk (x # p) (clink H)" "x \<notin> set p" "distinct p"
    define H' where "H' \<equiv> walkupN H z"
    have "x \<in> darts H"
      by (metis *(4) H.verts_clink list.set_intros(1) vwalk_verts_in_verts)
    then have "x \<in> darts H'"
      by (metis (no_types, lifting) *(2) Diff_iff H'_def H.darts_permN distinct.simps(2) 
          distinct_singleton empty_set insert_iff permF_def pre_hypermap.ext_inject 
          pre_hypermap.surjective walkupE_def walkupN_def)
    then show "x \<in> pverts (clink H')"
      by (metis H'_def H.hypermap_permN hypermap.hypermap_permF hypermap.hypermap_walkupE 
          hypermap.verts_clink walkupN_def with_proj_simps(1))
    { fix v assume "v \<in> set p"
      then have "v \<noteq> z"
        using *(3) by fast
      also have "v \<in> darts H"
        using *(4) H.verts_clink \<open>v \<in> set p\<close> by fastforce
      ultimately have "v \<in> darts H'"
        by (simp add: H'_def H.darts_permN permF_def walkupE_def walkupN_def)
      then show "v \<in> pverts (clink H')"
        by (simp add: clink_def cnode_def pair_union_def reverse_def)
    }
    fix u v assume "(u, v) \<in> set (vwalk_arcs (x # p))"
    then have "u\<rightarrow>\<^bsub>clink H\<^esub>v"
      using *(4) by blast
    then consider (face) "face H u = v" | (node) "node H v = u"
      by (metis Gr_eq H.clinkP cface_def cnode_def)
    then have "face H' u = v \<or> node H' v = u"
    proof cases
      case face
      then have "face H' u = v"
        by (metis "*"(2) "*"(3) H'_def \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close> in_set_vwalk_arcsE
            permF_def permN_def pre_hypermap.select_convs(3) pre_hypermap.select_convs(4) set_ConsD 
            skip_perm_invariant walkupE_def walkupN_def)
      then show ?thesis by simp
    next
      case node
      then have "v \<noteq> face H z \<and> node H v \<noteq> z"
        by (smt (verit, ccfv_threshold) *(1-3) \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close>
            in_set_vwalk_arcsE list.distinct(1) list.inject list.set_cases list.set_sel(1)
            prod.sel(2) vwalk_arcs.simps(2) vwalk_arcs_Cons)
      then have "node H' v = u"
        by (smt (z3) "*"(2) "*"(3) H'_def H.hypermap_permN \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close>
            hypermap.skip_edge_Perm in_set_vwalk_arcsE node permF_def permN_def
            pre_hypermap.select_convs(2) pre_hypermap.select_convs(3) set_ConsD skip_edge_def
            walkupE_def walkupN_def)
      then show ?thesis by simp
    qed
    then show "(u,v) \<in> parcs (clink H')"
      by (metis H'_def H.hypermap_permN \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close>
          \<open>\<And>v. v \<in> set p \<Longrightarrow> v \<in> pverts (clink H')\<close> \<open>x \<in> darts H'\<close> hypermap.hypermap_permF
          hypermap.hypermap_walkupE hypermap.parcs_clink hypermap.verts_clink in_set_vwalk_arcsE 
          set_ConsD walkupN_def with_proj_simps(1))
  qed
     
 have liftF: "\<lbrakk>z \<notin> set (x#p); face H (edge H z) \<notin> set p; vpath (x#p) (clink H)\<rbrakk>
                \<Longrightarrow> vpath (x#p) (clink (walkupF H z))" for p x z
   unfolding vpath_def
 proof (simp; rule vwalkI; rule; auto)
   assume *: "face H (edge H z) \<notin> set p" "z \<noteq> x" "z \<notin> set p" "vwalk (x # p) (clink H)"
             "x \<notin> set p" "distinct p"
    define H' where "H' \<equiv> walkupF H z"
    have "x \<in> darts H"
      by (metis *(4) H.verts_clink list.set_intros(1) vwalk_verts_in_verts)
    then have "x \<in> darts H'"
      by (metis (no_types, lifting) *(2) Diff_iff H'_def H.darts_permF distinct.simps(2) 
          distinct_singleton empty_set insert_iff permN_def pre_hypermap.ext_inject 
          pre_hypermap.surjective walkupE_def walkupF_def)
    then show "x \<in> pverts (clink H')"
      by (simp add: clink_def cnode_def pair_union_def reverse_def)
    { fix v assume "v \<in> set p"
      then have "v \<noteq> z"
        using *(3) by fast
      also have "v \<in> darts H"
        using *(4) H.verts_clink \<open>v \<in> set p\<close> by fastforce
      ultimately have "v \<in> darts H'"
        by (simp add: H'_def H.darts_permF permN_def walkupE_def walkupF_def)
      then show "v \<in> pverts (clink H')"
        by (simp add: clink_def cnode_def pair_union_def reverse_def)
    }
    fix u v assume "(u, v) \<in> set (vwalk_arcs (x # p))"
    then have "u\<rightarrow>\<^bsub>clink H\<^esub>v"
      using *(4) by blast
    then consider (face) "face H u = v" | (node) "node H v = u"
      by (metis Gr_eq H.clinkP cface_def cnode_def)
    then have "face H' u = v \<or> node H' v = u"
    proof cases
      case face
      then have "u \<noteq> edge H z \<and> face H u \<noteq> z"
        by (smt (verit, ccfv_threshold) *(1-3) \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close>
            in_set_vwalk_arcsE list.distinct(1) list.inject list.set_cases list.set_sel(1)
            prod.sel(2) vwalk_arcs.simps(2) vwalk_arcs_Cons)
      then have "face H' u = v"
        by (metis (no_types, lifting) "*"(2,3) H'_def H.hypermap_axioms H.hypermap_permF 
            \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close> face hypermap.edgeK hypermap.hypermap_walkupE 
            in_set_vwalk_arcsE permF_def permN_def pre_hypermap.select_convs(3,4) set_ConsD
            skip_perm_invariant walkupE_def walkupF_def)
      then show ?thesis by simp
    next
      case node
      then have "node H' v = u"
        by (metis "*"(2,3) H'_def \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close> in_set_vwalk_arcsE permF_def
            permN_def pre_hypermap.select_convs(3,4) set_ConsD skip_perm_invariant
            walkupE_def walkupF_def)
      then show ?thesis by simp
    qed
    then show "(u,v) \<in> parcs (clink H')"
      by (metis H'_def H.hypermap_permF \<open>(u, v) \<in> set (vwalk_arcs (x # p))\<close> 
          \<open>\<And>v. v \<in> set p \<Longrightarrow> v \<in> pverts (clink H')\<close> \<open>x \<in> pverts (clink H')\<close> hypermap.hypermap_permN
          hypermap.hypermap_walkupE hypermap.parcs_clink hypermap.verts_clink in_set_vwalk_arcsE 
          set_ConsD walkupF_def with_proj_simps(1))
  qed

  {
    assume "\<not> H.jordan"
    then obtain x q where xq_def: "H.moebius_path (x#q)"
      using H.jordan_def H.moebius_path.elims(2) by blast
    define p where "p \<equiv> x#q"
    then have vpath_p: "vpath p (clink H)"
      using H.moebius_path.elims(2) xq_def by blast
    have dart_x: "x \<in> darts H"
      by (metis H.verts_clink list.set_intros(1) vpathE p_def vpath_p vwalk_verts_in_verts)
    obtain t where t_def: "(node H t) = last q"
      using H.nodeK by blast
    have dart_t: "t \<in> darts H"
      by (metis H.moebius_path.simps(2) H.perm_node H.verts_clink Permutations.permutes_not_in
          last_ConsR last_in_set p_def subsetD t_def vpathE vpath_p vwalkE xq_def)
    have "appears_before q t (node H x)"
      by (smt (verit, ccfv_threshold) H.faceK H.moebius_path.elims(2) list.inject p_def t_def xq_def)
    (* Case 1: WalkupE on a dart outside the path *)
    have "set p = darts H"
    proof (rule ccontr)
      assume "set p \<noteq> darts H"
      then obtain u where u_def: "u \<notin> set (x#q) \<and> u \<in> darts H"
        by (metis H.finite_darts H.verts_clink List.finite_set card_mono card_seteq 
            subsetI vpathE vpath_p vwalk_def p_def)
      interpret H': walkup H u
        by (simp add: H.hypermap_axioms u_def walkup_axioms.intro walkup_def)
      define H' where "H' \<equiv> walkupE H u"
      then have "vpath (x#q) (clink H')"
        using \<open>u \<notin> set (x # q) \<and> u \<in> darts H\<close> liftE vpath_p xq_def p_def by blast
      also have "appears_before q (face H' (edge H' (last q))) (node H' x)"
        by (smt (z3) H'.H'_def H'.walkup_edge H'.walkup_face H'.walkup_node H'_def H.faceK
            H.moebius_path.simps(2) H.skip_edge_Perm skip_edge_noteq_z xq_def
            \<open>appears_before q t ((node H) \<langle>$\<rangle> x)\<close> appears_before_in apply_skip_perm last_in_set
            list.set_intros p_def skip_edge_def skip_fz skip_perm_invariant t_def u_def)
      ultimately have "hypermap.moebius_path H' (x#q)"
        using H'_def H.hypermap_walkupE H.moebius_path.simps(2)
          hypermap.moebius_path.elims(3) p_def xq_def by blast
      then show False
        using H'.z_dart H'_def H.hypermap_walkupE IHe hypermap.jordan_def by blast
    qed
    obtain y z q' where "q = y#z#q'"
      by (metis H.moebius_path.cases H.moebius_path.elims(2) \<open>appears_before q t ((node H) \<langle>$\<rangle> x)\<close>
          appears_before_in apply_inj_eq_iff distinct_length_2_or_more empty_iff empty_set
          last.simps set_ConsD t_def vpathE xq_def)
    have dart_y: "y \<in> darts H" and dart_z: "z \<in> darts H"
      using \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> p_def by auto
    have vpath_q': "q' \<noteq> [] \<Longrightarrow> vpath q' (clink H)"
      by (metis distinct.simps(2) list.simps(3) vpathE vpathI vpath_p p_def vwalk_consE \<open>q = y#z#q'\<close>)
    have "y \<noteq> x"
      by (metis \<open>q = y # z# q'\<close> distinct_length_2_or_more vpathE vpath_p p_def)
    have "t \<noteq> x"
      by (metis \<open>appears_before q t ((node H) \<langle>$\<rangle> x)\<close> appears_before_in(1) distinct.simps(2)
          p_def vpathE vpath_p)
    have "node H t \<noteq> x"
      by (metis \<open>q = y#z#q'\<close> distinct.simps(2) last_in_set list.distinct(1) p_def t_def vpathE vpath_p)
    have "node H t \<noteq> y"
      by (metis \<open>q = y # z # q'\<close> distinct.simps(2) last_ConsR last_in_set
          list.simps(3) t_def vpathE vpath_p p_def)

    (* Case 2: node H y = x with WalkupE *)
    have "face H x = y"
    proof (rule ccontr)
      assume "face H x \<noteq> y"
      then have "node H y = x"
        by (metis H.arc_clink H.wf_clink \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> p_def
            list.set_intros(1) vpathE vpath_p wf_digraph.vwalk_Cons_Cons wf_digraph_wp_iff)
      interpret H': walkup H x
        by (metis H.hypermap_axioms \<open>set p = darts H\<close> p_def list.set_intros(1)
            walkup.intro walkup_axioms.intro)
      define H' where " H' \<equiv> walkupE H x"
      have "vpath q (clink H')"
        by (metis H'_def \<open>q = y # z # q'\<close> distinct.simps(2) liftE list.distinct(1) p_def
            vpathE vpathI vpath_p vwalk_consE)
      also have "appears_before (z#q') (face H' (edge H' (last (z#q')))) (node H' y)"
        by (metis H'.H'_def H.hypermap_walkupE H'.walkup_node H'_def \<open>node H t \<noteq> x\<close> \<open>node H y = x\<close>
            \<open>appears_before q t (node H x)\<close> \<open>q = y # z # q'\<close> \<open>t \<noteq> x\<close> appears_before_cons
            apply_inj_eq_iff apply_skip_perm hypermap.nodeK last_ConsR list.simps(3) skip_def t_def)
      then have "hypermap.moebius_path H' q"
        by (metis H.hypermap_walkupE H'_def \<open>q = y # z # q'\<close> calculation 
            hypermap.moebius_path.simps(3))
      then show False
        using H'.H'_def H.hypermap_walkupE H'.z_dart H'_def IHe hypermap.jordan_def by auto
    qed

    have ptnx: "if y = t then node H x \<in> set q else appears_before (z # q') t (node H x)"
      by (metis \<open>appears_before q t ((node H) \<langle>$\<rangle> x)\<close> \<open>q = y # z # q'\<close> appears_before_cons)

    (* Case 3 - y with walkupF if z = node y *)
    text_raw \<open>\DefineSnippet{jordan_3}{\<close>
    have "face H y = z"
    proof (rule ccontr)
      assume "face H y \<noteq> z"
      then have "node H z = y"
        by (metis H.arc_clink H.perm_face H.wf_clink \<open>face H x = y\<close> \<open>q = y # z # q'\<close> \<open>y \<noteq> x\<close> p_def
          apply_inj_eq_iff permutes_def vpathE vpath_p wf_digraph.vwalk_Cons_Cons wf_digraph_wp_iff)
      interpret H': walkup H y
        by (metis H.hypermap_axioms \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> list.set_intros p_def
            walkup.intro walkup_axioms_def)
      define H' where "H' \<equiv> walkupF H y"
      have vpath_H'_q': "vpath (z#q') (clink H')"
        by (metis H'_def H.faceK \<open>node H z = y\<close> \<open>q = y # z # q'\<close> distinct.simps(2) liftF 
            list.simps(3) vpathE vpathI vpath_p vwalk_consE p_def)
      also have "face H' x = z"
        by (metis (no_types, lifting) H'.walkup_axioms H'_def H.faceK \<open>face H x = y\<close>
            \<open>node H z = y\<close> \<open>q = y # z # q'\<close> apply_inj_eq_iff distinct_length_2_or_more
            skip_face_def vpathE vpath_p walkup.face_walkupF p_def)
      then have "x\<rightarrow>\<^bsub>clink H'\<^esub>z"
        by (metis Gr_eq H'.darts_walkupF H'.z_dart H'_def \<open>set p = darts H\<close> \<open>y \<noteq> x\<close> p_def
            arc_in_union cface_def clink_def insert_Diff insert_iff list.set_intros(1))
      ultimately have vpath_p': "vpath (x#z#q') (clink H')"
        by (metis H'_def H.hypermap_permF \<open>q = y # z # q'\<close> distinct_length_2_or_more
            fin_digraph.axioms(1) hypermap.finite_clink hypermap.hypermap_permN 
            hypermap.hypermap_walkupE list.sel(1) p_def vpathE vpathI vpath_p walkupF_def
            wf_digraph.vwalk_wf_digraph_consI)
      then have H'_t: "face H' (edge H' (last (z#q'))) = (if t=y then z else t)"
        by (smt (z3) H'.edge_walkupF H'.walkup_axioms H'_def H.faceK \<open>(node H) \<langle>$\<rangle> t \<noteq> y\<close>
            \<open>node H z = y\<close> \<open>q = y # z # q'\<close> apply_inj_eq_iff apply_skip_perm last_ConsR
            list.simps(3) skip_def skip_face_def t_def walkup.face_walkupF)
      then have moebius_q': "appears_before (z#q') (if t=y then z else t) (node H' x)"
        by (smt (z3) H'.node_walkupF H'_def H.faceK \<open>(node H) \<langle>$\<rangle> z = y\<close> \<open>q = y # z # q'\<close>
            appears_before_cons apply_skip_perm distinct.simps(2) distinct_length_2_or_more
            ptnx skip_def vpathE vpath_p p_def)
      then have "hypermap.moebius_path H' (x#z#q')"
        by (smt (z3) H'_def H.darts_permF H.hypermap_permF vpath_p' H'_t dart_y
            hypermap.hypermap_permN hypermap.moebius_path.simps(3) walkup.H'_def 
            hypermap.hypermap_walkupE walkup.intro walkupF_def walkup_axioms.intro)
      then have "\<not> hypermap.jordan H'"
          by (metis H'_def H.hypermap_permF hypermap.hypermap_permN hypermap.hypermap_walkupE
              hypermap.jordan_def walkupF_def)
      then show False
        by (simp add: H'_def IHf dart_y)
    qed
    text_raw \<open>}%EndSnippet\<close>
    
    (* Case 4: y with walkupE if y \<noteq> t *)
    have "t = y"
    proof (rule ccontr)
      assume "t \<noteq> y"
      interpret H': walkup H y
        by (metis H.hypermap_axioms \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> list.set_intros p_def
            walkup.intro walkup_axioms_def)
      define H' where "H' \<equiv> walkupE H y"
      then have "vpath (z#q') (clink H')"
        by (metis \<open>q = y # z # q'\<close> distinct.simps(2) liftE list.simps(3) p_def
            vpathE vpathI vpath_p vwalk_consE)
      also have "face H' x = z"
        by (metis H'.H'_def H'.walkup_face H'_def \<open>face H x = y\<close> \<open>face H y = z\<close> apply_skip_perm skip_fz)
      ultimately have vpath_H': "vpath (x#z#q') (clink H')"
        by (metis H'_def H.hypermap_walkupE \<open>q = y # z # q'\<close> dart_x dart_y distinct_length_2_or_more
            hypermap.arc_clink hypermap.wf_clink insert_Diff insert_iff pre_hypermap.select_convs(1)
            vpath_def vpath_p walkupE_def wf_digraph.vwalk_Cons_Cons wf_digraph_wp_iff p_def)
      moreover have "appears_before (z#q') t (node H' x)"
        by (metis H'.H'_def H'.walkup_node H'_def \<open>q = y # z # q'\<close> \<open>t \<noteq> y\<close> appears_before_in(2) 
          distinct.simps(2) distinct_length_2_or_more p_def ptnx skip_perm_invariant vpathE vpath_p)
      ultimately have "hypermap.moebius_path H' (x#z#q')"
        by (smt (z3) H'.H'_def H'.walkup_node H'_def H.faceK H.hypermap_axioms \<open>(node H) \<langle>$\<rangle> t \<noteq> y\<close>
            \<open>q = y # z # q'\<close> \<open>t \<noteq> y\<close> apply_skip_perm hypermap.hypermap_walkupE 
            hypermap.moebius_path.simps(3) hypermap.nodeK last_ConsR list.simps(3) skip_def t_def)
      then show False
        using H'_def H.hypermap_walkupE IHe dart_y hypermap.jordan_def by blast
    qed

    (* Case 5: y with walkupN if y \<noteq> node x *)
    have "node H x = y"
    proof (rule ccontr)
      assume "node H x \<noteq> y"
      interpret H': walkup H y
        by (metis H.hypermap_axioms \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> list.set_intros p_def
            walkup.intro walkup_axioms_def)
      define H' where "H' \<equiv> walkupN H y"
      then have "vpath (z#q') (clink H')"
        by (metis \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>q = y # z # q'\<close> distinct.simps(2) liftN list.simps(3)
            vpathE vpathI vpath_p vwalk_consE p_def)
      also have "x\<rightarrow>\<^bsub>clink H'\<^esub>z"
        by (metis Gr_eq H'.darts_walkupN H'_def \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>y \<noteq> x\<close> 
            apply_skip_perm arc_in_union cface_def clink_def dart_x dart_y insert_Diff insert_iff 
            permF_def permN_def pre_hypermap.select_convs(3) pre_hypermap.select_convs(4) skip_fz 
            walkupE_def walkupN_def)
      ultimately have vpath_H': "vpath (x#z#q') (clink H')"
        by (metis H'_def H.hypermap_permN \<open>q = y # z # q'\<close> distinct_length_2_or_more p_def
            hypermap.hypermap_permF hypermap.hypermap_walkupE hypermap.wf_clink list.sel(1) 
            vpath_def vpath_p vwalk_consI walkupN_def wf_digraph.adj_in_verts(1) wf_digraph_wp_iff)
      have "face H' (edge H' (last (z#q'))) = z" 
        by (metis H'.edge_walkupN H'.face_walkupN H'_def H.edgeK \<open>face H x = y\<close> 
            \<open>face H y = z\<close> \<open>node H t \<noteq> y\<close> \<open>q = y # z # q'\<close> \<open>t = y\<close> \<open>y \<noteq> x\<close> apply_skip_perm 
            last_ConsR list.simps(3) skip_def t_def)
      then have "appears_before (z#q') (face H' (edge H' (last (z#q')))) (node H' x)"
        by (metis (no_types, lifting) H'.walkup_axioms H'_def \<open>(face H) \<langle>$\<rangle> y = z\<close> 
            \<open>(node H) \<langle>$\<rangle> x \<noteq> y\<close> \<open>q = y # z # q'\<close> \<open>t = y\<close> \<open>y \<noteq> x\<close> appears_before_cons 
         distinct_length_2_or_more ptnx set_ConsD skip_node_def vpathE vpath_H' walkup.node_walkupN)
      then have "hypermap.moebius_path H' (x#z#q')"
        by (metis H'_def H.hypermap_permN hypermap.hypermap_permF hypermap.hypermap_walkupE
            hypermap.moebius_path.simps(3) vpath_H' walkupN_def)
      then show False
        by (metis H'_def H.hypermap_permN IHn dart_y hypermap.hypermap_permF 
            hypermap.hypermap_walkupE hypermap.jordan_def walkupN_def)
    qed

    (* Base case: when there are less than 4 darts we can directly prove a contradiction *)
    have "length p \<ge> 4"
    proof (rule ccontr)
      have "length p \<ge> 2"
        by (metis H.moebius_path_length add_2_eq_Suc le_add1 less_le_trans not_less
            numeral_3_eq_3 p_def xq_def)
      moreover have "length p = 3 \<Longrightarrow> False"
      proof -
        assume "length p = 3"
        then have "q' = []"
          by (simp add: \<open>q = y # z # q'\<close> p_def)
        then have "p = [x,y,z]"
          by (simp add: \<open>q = y # z # q'\<close> p_def)
        then have "darts H = {x,y,z}"
          using \<open>set p = darts H\<close> by force
        then have "face H z = x"
          by (smt (verit) H.perm_face \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>(node H) \<langle>$\<rangle> t \<noteq> x\<close>
     \<open>q = y # z # q'\<close> \<open>q' = []\<close> empty_iff insert_iff last.simps list.distinct(1) permutes_def t_def)
        have "node H y = z"
          using \<open>q = y # z # q'\<close> \<open>q' = []\<close> \<open>t = y\<close> t_def by auto
        then have "node H z = x"
          by (smt (z3) H.edgeK H.perm_edge Permutations.permutes_not_in \<open>(face H) \<langle>$\<rangle> y = z\<close>
              \<open>(node H) \<langle>$\<rangle> t \<noteq> x\<close> \<open>(node H) \<langle>$\<rangle> t \<noteq> y\<close> \<open>(node H) \<langle>$\<rangle> x = y\<close> \<open>q = y # z # q'\<close>
              \<open>q' = []\<close> \<open>set p = darts H\<close> \<open>t = y\<close> apply_inj_eq_iff distinct.simps(2) 
              distinct_singleton insert_iff list.simps(15) p_def)
        then have "edge H x = y \<and> edge H y = z \<and> edge H z = x"
          by (metis H.edgeK \<open>face H x = y\<close> \<open>face H y = z\<close> \<open>face H z = x\<close> 
                            \<open>node H x = y\<close> \<open>node H y = z\<close>)
        {
          fix u assume "u \<in> darts H"
          then have  "u = x \<or> u = y \<or> u = z"
            using \<open>darts H = {x,y,z}\<close> by blast
          then have "u\<rightarrow>\<^sup>*\<^bsub>cedge H\<^esub>v \<and> u\<rightarrow>\<^sup>*\<^bsub>cnode H\<^esub>v \<and> u\<rightarrow>\<^sup>*\<^bsub>cface H\<^esub>v" if "v \<in> darts H" for v
            by (smt (z3) Gr_eq Gr_verts H.arc_clink H.cedge_connect_sym H.cface_connect_sym
              H.clinkP H.cnode_connect_sym H.wf_cedge H.wf_cface H.wf_cnode
              \<open>(edge H) \<langle>$\<rangle> x = y \<and> (edge H) \<langle>$\<rangle> y = z \<and> (edge H) \<langle>$\<rangle> z = x\<close> \<open>(face H) \<langle>$\<rangle> x = y\<close>
              \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>(face H) \<langle>$\<rangle> z = x\<close> \<open>(node H) \<langle>$\<rangle> x = y\<close> \<open>(node H) \<langle>$\<rangle> y = z\<close> 
              \<open>(node H) \<langle>$\<rangle> z = x\<close> \<open>p = [x, y, z]\<close> \<open>set p = darts H\<close> cedge_def cface_def cnode_def 
              empty_iff empty_set set_ConsD that wf_digraph.reach_sym_arc wf_digraph.reachable_adjI
              wf_digraph.reachable_refl wf_digraph_wp_iff)
        } note reach_enf = this
        then have strongly_connected_enf: "strongly_connected (cedge H)"
                  "strongly_connected (cnode H)" 
                  "strongly_connected (cface H)"
          by (metis Gr_verts cedge_def cnode_def cface_def reach_enf
              dart_y equals0D strongly_connectedI)+
        then have "card (pre_digraph.sccs (cedge H)) = 1" 
                  "card (pre_digraph.sccs (cnode H)) = 1" 
                  "card (pre_digraph.sccs (cface H)) = 1"
          using H.wf_cedge H.wf_cnode H.wf_cface wf_digraph.card_sccs_connected wf_digraph_wp_iff 
          by blast+
        then have "euler_rhs H = 3"
          unfolding euler_rhs_def
          by (simp add: perm_on.count_cycles_card_sccs H.finite_darts H.perm_edge H.perm_face
              H.perm_node cedge_def cface_def cnode_def perm_on.intro)

        have "card (darts H) = 3"
          by (metis \<open>length p = 3\<close> \<open>set p = darts H\<close> distinct_card vpathE vpath_p)
        also have "strongly_connected (glink H)"
        proof
          show "verts (glink H) \<noteq> {}"
            by (metis H.hypermap_axioms H.verts_clink H.wf_clink dart_x empty_iff 
             hypermap.clink_glink reachable_in_vertsE wf_digraph.reachable_refl wf_digraph_wp_iff)
          fix u v assume "u \<in> verts (glink H)" "v \<in> verts (glink H)"
          then show "u \<rightarrow>\<^sup>*\<^bsub>with_proj (glink H)\<^esub> v"
            by (metis H.arc_clink H.clink_connect_sym H.clink_glink H.verts_clink H.wf_clink
                H.wf_glink \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>(node H) \<langle>$\<rangle> z = x\<close> 
                \<open>q = y # z # q'\<close> \<open>q' = []\<close> \<open>set p = darts H\<close> empty_iff empty_set p_def 
                reachable_in_vertsE set_ConsD wf_digraph.reach_sym_arc wf_digraph.reachable_adjI 
                wf_digraph.reachable_refl wf_digraph_wp_iff)
        qed
        then have "card (pre_digraph.sccs (glink H)) = 1"
          using H.wf_glink wf_digraph.card_sccs_connected wf_digraph_wp_iff by blast
        then have "euler_lhs H = 5"
          unfolding euler_lhs_def using \<open>card (darts H) = 3\<close> by simp
        then have "genus H = 1"
          using \<open>euler_rhs H = 3\<close> by (simp add: genus_def)
        then show False
          by (metis H.finite_darts One_nat_def Suc.prems(2) calculation card_0_eq dart_t
              empty_iff numeral_3_eq_3 planar_def)
      qed
      ultimately show "\<not> 4 \<le> length p \<Longrightarrow> False"
        by (metis H.moebius_path_length Suc_leI le_neq_implies_less numeral_eq_Suc p_def 
            pred_numeral_simps(2) semiring_norm(26,27) xq_def)
    qed

    then obtain w q'' where "w # q'' = q'"
      by (metis One_nat_def Suc_le_length_iff Suc_le_mono \<open>q = y # z # q'\<close> add.commute list.size(4)
          numeral_3_eq_3 numeral_eq_Suc p_def plus_1_eq_Suc pred_numeral_simps(2) semiring_norm(26,27))
    then have xyzw: "p = x#y#z#w#q''"
      by (simp add: \<open>q = y # z # q'\<close> p_def)

    (* Case 6: z with walkupE if z is followed by an f-link *)
    have "node H w = z"
    proof (rule ccontr)
      assume "node H w \<noteq> z"
      then have "face H z = w"
        by (metis H.arc_clink \<open>q = y # z # q'\<close> \<open>w # q'' = q'\<close> dart_z list.sel(1)
            list.simps(3) p_def vpathE vpath_p vwalk_consE)
      interpret H': walkup H z
        by (metis H.hypermap_axioms \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> list.set_intros p_def
            walkup.intro walkup_axioms_def)
      define H' where "H' \<equiv> walkupE H z"
      have "vpath q' (clink H')"
        unfolding H'_def apply (rule liftE)
        using \<open>q = y # z # q'\<close> p_def vpath_p apply auto
        using \<open>w # q'' = q'\<close> vpath_q' by blast
      moreover have "x\<rightarrow>\<^bsub>clink H'\<^esub>y"
        by (metis H'.H'_def H'.walkup_face H'_def H.hypermap_walkupE \<open>(face H) \<langle>$\<rangle> x = y\<close> 
            \<open>q = y # z # q'\<close> apply_skip_perm dart_x dart_z distinct.simps(2) hypermap.arc_clink
            insert_Diff insert_iff list.simps(15) p_def pre_hypermap.select_convs(1) skip_invariant
            vpathE vpath_p walkupE_def)
      moreover have "y\<rightarrow>\<^bsub>clink H'\<^esub>w"
        by (metis H'.H'_def H'.walkup_face H'_def H.hypermap_walkupE \<open>(face H) \<langle>$\<rangle> y = z\<close> 
            \<open>(face H) \<langle>$\<rangle> z = w\<close> apply_skip_perm calculation(2) hypermap.arc_clink 
            hypermap.verts_clink hypermap.wf_clink skip_fz wf_digraph.adj_in_verts(2)
            wf_digraph_wp_iff)
      ultimately have "vpath (x#y#q') (clink H')"
        by (metis H'_def H.hypermap_walkupE \<open>q = y # z # q'\<close> \<open>w # q'' = q'\<close>
            distinct_length_2_or_more hypermap.wf_clink list.sel(1) p_def vpathE vpathI vpath_p
            wf_digraph.vwalk_wf_digraph_consI wf_digraph_wp_iff)
      also have "appears_before (y#q') t (node H' x)"
        by (metis H'.H'_def H'.walkup_node H'_def \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(face H) \<langle>$\<rangle> y = z\<close> 
            \<open>(face H) \<langle>$\<rangle> z = w\<close> \<open>(node H) \<langle>$\<rangle> x = y\<close> \<open>t = y\<close> \<open>w # q'' = q'\<close> appears_before_id
            calculation distinct_length_2_or_more list.set_intros(1) skip_perm_invariant vpathE)
      ultimately have "hypermap.moebius_path H' (x#y#q')"
        by (smt (z3) H'.H'_def H'.walkup_axioms H'.walkup_face H'_def H.edgeK H.hypermap_walkupE
          H.skip_edge_Perm \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(face H) \<langle>$\<rangle> y = z\<close> \<open>q = y # z # q'\<close> \<open>t = y\<close>
          \<open>w # q'' = q'\<close> distinct.simps(2) distinct_length_2_or_more hypermap.moebius_path.simps(3) 
          last_ConsR last_in_set list.distinct(1) p_def skip_edge_def skip_perm_invariant t_def
          vpathE vpath_p walkup.walkup_edge)
      then show False
        using H'_def H.hypermap_walkupE IHe dart_z hypermap.jordan_def by blast
    qed

    (* Case 7: otherwise z with F-transform *)
    then have False
    proof -
       interpret H': walkup H z
        by (metis H.hypermap_axioms \<open>q = y # z # q'\<close> \<open>set p = darts H\<close> list.set_intros p_def
            walkup.intro walkup_axioms_def)
      define H' where "H' \<equiv> walkupF H z"
      have "vpath (w#q'') (clink H')"
        unfolding H'_def apply (rule liftF)
          apply (metis distinct.simps(2) vpathE vpath_p xyzw)
         apply (metis H.faceK \<open>(node H) \<langle>$\<rangle> w = z\<close> \<open>w # q'' = q'\<close>
            distinct.simps(2) list.distinct(1) vpathE vpath_q')
        using \<open>w # q'' = q'\<close> vpath_q' by fastforce
      moreover have "face H' x = y"
        by (metis H'.walkup_axioms H'_def H.faceK \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(node H) \<langle>$\<rangle> w = z\<close> 
            \<open>q = y # z # q'\<close> \<open>w # q'' = q'\<close> distinct_length_2_or_more p_def skip_face_def vpathE 
            vpath_p walkup.face_walkupF)
      moreover have "face H' y = w"
        by (metis H'.walkup_axioms H'_def H.faceK \<open>face H y = z\<close> \<open>node H w = z\<close> \<open>q = y # z # q'\<close>
            \<open>w # q'' = q'\<close> apply_perm_neq_idI apply_set_perm distinct_length_2_or_more in_set_permI
            p_def skip_face_def vpathE vpath_p walkup.face_walkupF)
      ultimately have "vpath (x#y#q') (clink H')"
        by (metis H'.darts_walkupF H'_def H.hypermap_permF \<open>q = y # z # q'\<close> \<open>w # q'' = q'\<close> dart_x 
            dart_y dart_z distinct_length_2_or_more hypermap.clinkF hypermap.hypermap_permN 
            hypermap.hypermap_walkupE hypermap.verts_clink insert_Diff insert_iff list.sel(1) p_def
            vpath_def vpath_p vwalk_consI walkupF_def)
      also have "appears_before (y#q') t (node H' x)"
        by (metis H'.node_walkupF H'.walkup_axioms H'_def \<open>(face H') \<langle>$\<rangle> x = y\<close> \<open>(node H) \<langle>$\<rangle> x = y\<close> 
            \<open>t = y\<close> \<open>y \<noteq> x\<close> appears_before_cons apply_inj_eq_iff insert_iff list.simps(15)
            skip_face_def skip_perm_invariant walkup.face_walkupF)
      ultimately have "hypermap.moebius_path H' (x#y#q')"
        by (smt (z3) H'.edge_walkupF H'_def H.edgeK H.hypermap_permF \<open>(face H') \<langle>$\<rangle> x = y\<close> 
            \<open>(face H) \<langle>$\<rangle> x = y\<close> \<open>(node H) \<langle>$\<rangle> w = z\<close> \<open>q = y # z # q'\<close> \<open>t = y\<close> \<open>w # q'' = q'\<close> 
            apply_inj_eq_iff distinct_length_2_or_more hypermap.hypermap_permN 
            hypermap.hypermap_walkupE hypermap.moebius_path.simps(3) last_ConsR list.distinct(1) 
            p_def skip_perm_invariant t_def vpathE vpath_p walkupF_def)
      then show False
        by (metis H'_def H.hypermap_permF IHf dart_z hypermap.hypermap_permN 
            hypermap.hypermap_walkupE hypermap.jordan_def walkupF_def)
    qed
  }
  then show ?case
    by auto
qed


theorem Jordan_planar: "\<lbrakk>hypermap H; hypermap.jordan H\<rbrakk> \<Longrightarrow> planar H"
proof (induction "card (darts H)" arbitrary: H)
  case 0
  then have "darts H = {}"
    by (metis card_0_eq hypermap.finite_darts)
  then have "verts (glink H) = {}"
    by (simp add: cedge_def cface_def cnode_def glink_def)
  then have "pre_digraph.sccs (glink H) = {}"
    by (simp add: "0.prems"(1) hypermap.wf_glink wf_digraph.sccs_empty wf_digraph_wp_iff)
  then have "euler_lhs H = 0"
    by (simp add: "0.hyps" euler_lhs_def)
  also have "euler_rhs H = 0"
    by (metis "0.prems"(1) \<open>darts H = {}\<close> add_eq_0_iff_both_eq_0 euler_rhs_def hypermap.perm_edge 
        hypermap.perm_face hypermap.perm_node perm_on.count_cycles_on_empty perm_on.intro)
  ultimately show ?case
    unfolding planar_def genus_def by presburger
next
  case (Suc x)
  then show ?case sorry
qed

end