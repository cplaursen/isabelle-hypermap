theory Jordan
  imports Walkup
begin

context hypermap
begin

theorem even_genus: "even (genus H)"
  sorry

theorem Euler_le: "euler_rhs H \<le> euler_lhs H"
  using even_genus sorry

theorem planar_Jordan:
  shows "\<lbrakk>hypermap H; planar H\<rbrakk> \<Longrightarrow> hypermap.jordan H"
proof (induct "card (darts H)" arbitrary: H)
  case 0
  then interpret h_0: hypermap H by simp
  show ?case
    by (smt (z3) "0.hyps" Gr_eq card_0_eq cnode_def empty_iff h_0.finite_darts h_0.jordan_def
        h_0.moebius_path.elims(2))
next
  case (Suc x)
  interpret H: hypermap H
    by (simp add: Suc.prems(1))
  interpret clink: wf_digraph "clink H"
    by (simp add: H.wf_clink wf_digraph_wp_iff)
  {
    assume "\<not> H.jordan"
    then obtain p where "H.moebius_path p"
      using H.jordan_def by blast
    then have "length p \<ge> 3"
      sorry
(*  1) a dart not in p, with an E-transform                                   *)
(*  2) x with an E-transform if x is followed by an N-link (i.e., x = node y) *)
(*  3) y = face x with an F-transform, if y is followed by an N-link.         *)
(*  4) y with an E-transform, if y != t (by 3), z = face y)                   *)
(*  5) y with an N-transform, if y != node x                                  *)
(*  6) z with an E-transform, if z is followed by an F-link in p              *)
(*  7) z with an F-transform, otherwise (z is followed by an N-link in p)     *)
    then have "\<exists>p' u. u \<in> darts H \<and> hypermap.moebius_path (walkupE H u) p'"
      sorry
    then obtain u where u: "\<exists>p'. u \<in> darts H \<and> hypermap.moebius_path (walkupE H u) p'"
      by blast
    then interpret walkup: walkup H u
      by (simp add: H.hypermap_axioms walkup.intro walkup_axioms.intro)
    have "\<not> hypermap.jordan (walkupE H u)"
      using u walkup.H'_def walkup.hypermap_walkupE hypermap.jordan_def by auto
    have "x = card (darts (walkupE H u))"
      using Suc.hyps(2) walkup.H'_def walkup.card_darts_walkup by auto
    moreover have "planar (walkupE H u)"
      using Suc.prems walkup.H'_def walkup.planar_walkupE by auto
    moreover have "hypermap (walkupE H u)"
      using local.walkup.H'_def local.walkup.hypermap_walkupE by auto
    ultimately have "hypermap.jordan (walkupE H u)"
      using Suc.hyps(1) by blast
    then have False
      using \<open>\<not> hypermap.jordan (walkupE H u)\<close> by auto
  }
  then show ?case by blast
qed

theorem Jordan_planar: "jordan \<Longrightarrow> planar H"
  sorry

end
end