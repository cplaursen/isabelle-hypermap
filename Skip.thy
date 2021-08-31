theory Skip
    imports "Extras"
begin

text \<open>Suppressing an element from a function\<close>                               

definition skip :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"skip z f \<equiv> \<lambda> x. (if x = z then z else (if f x = z then f z else f x))"

lemma skip_id [simp]: "skip z f z = z"
  unfolding skip_def by simp

lemma skip_z_eq_fz: "f z = z \<Longrightarrow> x \<noteq> z \<Longrightarrow> (skip z f) x = f x"
  unfolding skip_def by simp

lemma skip_fz [simp]: "f x = z \<Longrightarrow> skip z f x = f z"
  by (metis skip_def)

lemma skip_invariant: "x \<noteq> z \<Longrightarrow> f x \<noteq> z \<Longrightarrow> skip z f x = f x"
  unfolding skip_def by simp

lemma inj_skip: "inj f \<Longrightarrow> inj (skip z f)"
  unfolding skip_def by (smt (verit, ccfv_SIG) injD inj_on_def)

lemma bij_skip: "bij f \<Longrightarrow> bij (skip z f)"
  by (metis bij_def inj_skip skip_def surj_def) 

lemma skip_permutes:
  assumes "f permutes S"
  shows "skip z f permutes S - {z}"
proof (simp add: permutes_def; rule conjI)
  show "\<forall>x. (x \<in> S \<longrightarrow> x = z) \<longrightarrow> skip z f x = x"
    by (metis assms permutes_def skip_def)
  have "bij (skip z f)"
    by (meson assms bij_skip permutes_bij)
  then show "\<forall>y. \<exists>!x. skip z f x = y"
    by (simp add: bij_iff)
qed

section \<open>Suppressing an element from a permutation\<close>

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

lemma skip_perm_invariant: "x \<noteq> z \<Longrightarrow> p \<langle>$\<rangle> x \<noteq> z \<Longrightarrow> skip_perm z p x = p \<langle>$\<rangle> x"
  by (simp add: skip_invariant apply_skip_perm)

lemma skip_perm_notin: "z \<notin> set_perm p \<Longrightarrow> skip_perm z p = p"
proof -
  assume "z \<notin> set_perm p"
  then have "p \<langle>$\<rangle> z = z"
    by blast
  then have "skip z p = p"
    by (metis perm_eq_iff skip_id skip_z_eq_fz apply_skip_perm)
  then show ?thesis
    by (simp add: perm.apply_perm_inverse skip_perm_def)
qed

lemma skip_perm_permutes: "(p :: 'a perm) permutes S \<Longrightarrow> skip_perm z p permutes S - {z}"
  by (simp add: apply_skip_perm skip_permutes)

lemma set_perm_skip_id_cycle: "p \<langle>$\<rangle> z = z \<Longrightarrow> set_perm p = set_perm (skip_perm z p)"
  by (simp add: in_set_perm skip_perm_notin)

lemma set_perm_skip_2_cycle: 
  fixes p :: "'a perm"
  assumes "p z \<noteq> z" "p (p z) = z"
  shows "set_perm p = set_perm (skip_perm z p) \<union> {z, p z}"
proof (rule subset_antisym; rule subsetI)
  fix x assume "x \<in> set_perm p"
  then have "x \<noteq> z \<and> x \<noteq> p z \<Longrightarrow> x \<in> set_perm (skip_perm z p)"
    by (metis apply_perm_neq_idI apply_skip_perm in_set_permI skip_def)
  then show "x \<in> set_perm (skip_perm z p) \<union> {z, p z}"
    by auto
next
  show "x \<in> set_perm p" if "x \<in> set_perm (skip_perm z p) \<union> {z, p z}" for x
    by (metis that Un_insert_right apply_perm_eq_same_iff(2) apply_skip_perm
        assms boolean_algebra_cancel.sup0 insert_iff skip_invariant)
qed

lemma set_perm_skip_n_cycle:
  fixes p :: "'a perm"
  assumes "p z \<noteq> z" "p (p z) \<noteq> z"
  shows "set_perm p = set_perm (skip_perm z p) \<union> {z}"
proof (rule subset_antisym; rule subsetI)
  fix x assume "x \<in> set_perm p"
  then show "x \<in> set_perm (skip_perm z p) \<union> {z}"
    by (metis apply_perm_eq_same_iff(2) apply_skip_perm assms(2) inf_sup_aci(5)
        insert_iff insert_is_Un skip_fz skip_invariant)
next
  fix x assume "x \<in> set_perm (skip_perm z p) \<union> {z}"
  then show "x \<in> set_perm p"
    by (metis UnE apply_perm_neq_idI apply_skip_perm assms(1) empty_iff in_set_permI
        insert_iff skip_invariant)
qed

lemma cycles_imp_cycles_skip:
  assumes "c \<in> cycles_of_perm p" (is "c \<in> ?C")
      and "c \<notin> cycles_of_perm (skip_perm z p)" (is "c \<notin> ?C'")
  shows "\<And> x. x \<noteq> c \<Longrightarrow> x \<in> cycles_of_perm p \<Longrightarrow> x \<in> cycles_of_perm (skip_perm z p)"
proof -
  have "z \<in> set_cycle c"
    by (smt (verit, ccfv_threshold) assms apply_cycle_in_set_iff apply_perm_cycle apply_skip_perm 
        cycles_of_perm_altdef mem_Collect_eq skip_invariant)
  then have "c = perm_orbit p z"
    using assms(1) perm_orbit_eqI by fastforce
  have disj: "disjoint_cycles ?C" by auto
  fix x assume "x \<noteq> c"
  then show "x \<in> ?C \<Longrightarrow> x \<in> ?C'"
    by (smt (verit, ccfv_threshold) \<open>c \<in> ?C\<close> disj(1) IntI \<open>z \<in> set_cycle c\<close> apply_cycle_cycles_of_perm
        apply_perm_cycle apply_set_perm apply_skip_perm cycle_perm_same_iff cycles_of_perm_altdef
        cycles_of_perm_of_cycles disjoint_cycles_insert empty_iff insertE mem_Collect_eq
        mk_disjoint_insert perm_of_cycles_not_in set_perm_cycle skip_invariant)
qed

lemma skip_perm_cycle_invariant:
  assumes "x \<notin> set_cycle (perm_orbit p z)" "x \<in> set_perm p"
  shows "perm_orbit (skip_perm z p) x = perm_orbit p x"
  by (smt (verit) apply_cycle_cycles_of_perm apply_perm_cycle apply_perm_neq_idI assms
      cycles_imp_cycles_skip apply_skip_perm perm_orbit_eqI
      perm_orbit_in_cycles_of_perm skip_id skip_perm_notin start_in_perm_orbit_iff)

lemma perm_orbit_notin_skip_perm: "perm_orbit p z \<notin> cycles_of_perm (skip_perm z p)"
  by (metis apply_cycle_cycles_of_perm apply_cycle_perm_orbit' apply_skip_perm
      id_cycle_eq_perm_orbit_iff id_cycle_not_in_cycles_of_perm skip_id start_in_perm_orbit_iff)

theorem remove1_cycle_orbit: "delete_cycle z (perm_orbit p z) = perm_orbit (skip_perm z p) (p z)"
proof (rule cycle_eqI; rule; auto simp: conjI apply_cycle_delete)
  show "p \<langle>$\<rangle> z = z \<Longrightarrow> z = (skip_perm z p) \<langle>$\<rangle> z"
    by (simp add: apply_skip_perm)
  fix x
  show "apply_cycle (perm_orbit p z) x = z \<Longrightarrow> x \<noteq> z \<Longrightarrow>
         p \<langle>$\<rangle> z = apply_cycle (perm_orbit (skip_perm z p) (p \<langle>$\<rangle> z)) x"
    by (metis apply_cycle_perm_orbit apply_cycle_same_iff apply_perm_in_perm_orbit_iff 
      apply_skip_perm skip_def start_in_perm_orbit_iff)
  show "p \<langle>$\<rangle> z \<noteq> z \<Longrightarrow> z = apply_cycle (perm_orbit (skip_perm z p) (p \<langle>$\<rangle> z)) z"
    by (metis apply_cycle_not_in_set apply_cycle_perm_orbit apply_skip_perm skip_id)
  
  assume *: "apply_cycle (perm_orbit p z) x \<noteq> z"  "x \<noteq> z"
  then consider "p z = x" 
    | "x \<notin> set_cycle (perm_orbit p z)"
    | "p z \<noteq> x \<and> x \<in> set_cycle (perm_orbit p z)" 
    by blast 
  then show "apply_cycle (perm_orbit p z) x = apply_cycle (perm_orbit (skip_perm z p) (p \<langle>$\<rangle> z)) x"
  proof cases
    case 1
    then show ?thesis
      by (metis *(1) apply_cycle_perm_orbit apply_cycle_perm_orbit'
          apply_perm_in_perm_orbit_iff skip_perm_invariant start_in_perm_orbit)
  next
    case 2
    then have "apply_cycle (perm_orbit p z) x = x"
      by (transfer; simp)
    also have "apply_cycle (perm_orbit (skip_perm z p) (p \<langle>$\<rangle> z)) x = x"
      by (smt (z3) 2 apply_cycle_not_in_set apply_cycle_perm_orbit apply_perm_in_perm_orbit_iff 
          apply_skip_perm perm_orbit_eqI perm_orbit_eq_id_cycle_iff skip_def start_in_perm_orbit_iff)
    ultimately show ?thesis by simp
next
  case 3
  then have "apply_cycle (perm_orbit p z) x = p x"
      by (meson apply_cycle_perm_orbit)
    also {
      have "skip_perm z p x = p x"
        by (metis \<open>apply_cycle (perm_orbit p z) x \<noteq> z\<close> \<open>x \<noteq> z\<close> skip_invariant 
            apply_skip_perm calculation)
      define n where "n = (LEAST n. (p ^ Suc n) x = p z)"
      then have "((\<langle>$\<rangle>) (skip_perm z p) ^^ n) x = p z"
      proof (simp add: apply_skip_perm)
        assume n_def: "n = (LEAST n. (p * p ^ n) \<langle>$\<rangle> x = p \<langle>$\<rangle> z)"
        have "\<exists>m. (p * p ^ m) x = p z"
          by (metis 3 apply_perm_power apply_perm_sequence cycles_funpow)
        then have "(p * p ^ n) x = p z"
          using LeastI n_def by fast
        then have "(p ^ n) x = z"
          by (metis apply_inj_eq_iff apply_perm_sequence)
        then have "n > 0"
          using \<open>x \<noteq> z\<close> gr_zeroI by fastforce
        { fix l assume "l < n"
          then have "(p ^ l) x \<noteq> p z \<and> (p ^ l) x \<noteq> z"
            apply (safe)
            using 3 \<open>(p ^ n) \<langle>$\<rangle> x = z\<close> apply_inj_eq_iff apply_perm_sequence
                dual_order.strict_trans n_def not0_implies_Suc not_less_Least not_less_eq power_Suc
                power_Suc0_right by (smt (verit, del_insts) \<open>l < n\<close>)+
          from \<open>l < n\<close> have p_eq: "(p ^ l) x = ((skip z p) ^^ l) x"
          proof (induct l)
            case 0
            then show ?case by simp
          next
            case (Suc l)
            then show ?case
              by (smt (z3) Suc_lessD n_def
                   apply_perm_sequence apply_skip_perm funpow_simp_l not_less_Least power_Suc 
                   skip_perm_invariant)
          qed
        }
        then have "(p ^ (n-1)) x = ((skip z p) ^^ (n-1)) x"
          by (simp add: \<open>0 < n\<close>)
        then show "(skip z ((\<langle>$\<rangle>) p) ^^ (LEAST n. (p * p ^ n) \<langle>$\<rangle> x = p \<langle>$\<rangle> z)) x = p \<langle>$\<rangle> z"
          by (smt (z3) One_nat_def Suc_pred \<open>(p ^ n) \<langle>$\<rangle> x = z\<close> \<open>0 < n\<close>
              n_def apply_perm_power funpow_simp_l skip_fz)
      qed
      then have "apply_cycle (perm_orbit (skip_perm z p) (p \<langle>$\<rangle> z)) x = p x"
        by (metis 3 \<open>(skip_perm z p) \<langle>$\<rangle> x = p \<langle>$\<rangle> x\<close> apply_cycle_perm_orbit funpow_cycles)
    }
    ultimately show ?thesis by simp
  next
  qed
qed

lemma cycles_skip_diff:
  assumes "x \<noteq> delete_cycle z (perm_orbit p z)" 
      and "x \<in> cycles_of_perm (skip_perm z p)" (is "x \<in> ?C'")
    shows "x \<in> cycles_of_perm p"
proof -
  from assms(1) have "\<forall>y \<in> set_cycle x. y \<notin> set_cycle (perm_orbit (skip_perm z p) z)"
    by (simp add: apply_skip_perm)
  moreover have "x \<in> cycles_of_perm p \<Longrightarrow> \<forall>y \<in> set_cycle x. perm_orbit p y \<in> cycles_of_perm p"
    by (meson perm_orbit_in_cycles_of_perm set_cycle_of_perm_subset subset_iff)
  consider  (empty) "set_cycle (perm_orbit p z) = {}" | 
            (size_two) "size (perm_orbit p z) = 2" |
            (union) "size (perm_orbit p z) > 2"
    by (metis One_nat_def gr_implies_not_zero less_2_cases_iff neqE perm_orbit_fixpoint
        set_cycle_empty_iff set_cycle_ex_funpow size_cycle_not_1' start_in_perm_orbit_iff)
  then show ?thesis
  proof cases
    case empty
    then show ?thesis
      by (metis assms(2) id_cycle_not_in_cycles_of_perm perm_orbit_in_cycles_of_perm
          set_cycle_empty_iff skip_perm_notin)
  next
    case size_two
    then have "{z, p z} = set_cycle (perm_orbit p z)"
      by (smt (z3) apply_cycle_in_set_iff apply_cycle_perm_orbit' card_2_iff card_set_cycle
      doubleton_eq_iff insert_absorb insert_iff perm_orbit_eq_id_cycle_iff set_cycle_empty_iff
      start_in_perm_orbit)
    also have "perm_orbit (skip_perm z p) (p z) = id_cycle"
      by (smt (verit, ccfv_threshold) calculation apply_cycle_in_set_iff apply_cycle_perm_orbit
 apply_skip_perm insertCI insertE is_singletonI is_singleton_conv_Ex1 perm_orbit_fixpoint skip_def)
    ultimately show ?thesis
      by (smt (z3) DiffD2 Diff_insert_absorb apply_perm_neq_idI apply_skip_perm assms(2)
          cycles_of_perm_def image_iff in_set_permI insertE perm_orbit_eq_id_cycle_iff skip_id 
          skip_invariant skip_perm_cycle_invariant)
  next
    case union
    then have "size (perm_orbit p z) \<ge> 3" by simp
    define poz where "poz = perm_orbit p z"
    then have "delete_cycle z poz \<noteq> id_cycle"
      using \<open>size (perm_orbit p z) \<ge> 3\<close> apply transfer
      by (smt (z3) List.finite_set One_nat_def card.empty card.insert_remove cycle_relE
          cycle_rel_imp_same_set distinct_card empty_set filter_cong insert_absorb leD lessI 
          list.size(3) not_numeral_le_zero numeral_3_eq_3 perm_orbit_impl set_minus_filter_out)
    also have remove1_poz: "delete_cycle z poz = perm_orbit (skip_perm z p) (p z)"
      by (simp add: poz_def remove1_cycle_orbit union)
    moreover have "perm_orbit p z = perm_orbit p (p z)"
      by (smt (verit, ccfv_threshold) apply_perm_in_perm_orbit_iff apply_set_perm apply_skip_perm 
cycles_imp_cycles_skip disjoint_cycles_cycles_of_perms in_set_permI perm_of_cycles_in
 perm_of_cycles_of_perm perm_orbit_fixpoint perm_orbit_in_cycles_of_perm perm_orbit_notin_skip_perm
 skip_id start_in_perm_orbit)
    ultimately have "set_cycle (perm_orbit (skip_perm z p) (p z)) \<union> {z} = set_cycle (perm_orbit p z)"
      by (metis Un_insert_right poz_def boolean_algebra_cancel.sup0
          gr_implies_not_zero insert_Diff not_less_iff_gr_or_eq perm_orbit_eq_id_cycle_iff
          set_cycle_delete size_cycle_eq_0_iff' start_in_perm_orbit union)
    then show ?thesis
      by (smt (verit, ccfv_SIG) poz_def remove1_poz apply_cycle_cycles_of_perm
          apply_cycle_same_iff apply_set_perm apply_skip_perm assms cycles_of_perm_altdef
          mem_Collect_eq perm_orbit_eqI set_perm_cycle skip_def)
  qed
qed

lemma cycles_skip:
  assumes "z \<in> set_perm p"
  shows "cycles_of_perm p = cycles_of_perm (skip_perm z p) \<union>
       {perm_orbit p z} - {delete_cycle z (perm_orbit p z)}" (is "?C = ?C' \<union> {?poz} - {?poz'}")
proof (rule subset_antisym; rule subsetI)
  have disj: "disjoint_cycles ?C" "disjoint_cycles ?C'" by auto
  have poz_subset: "set_cycle ?poz' \<subseteq> set_cycle ?poz"
    by (metis DiffD1 apply_perm_neq_idI assms cycle_delete_swap equals0D set_cycle_delete
        set_cycle_empty_iff start_in_perm_orbit subsetI)
  have poz_in_C: "?poz \<in> ?C" using assms by (rule perm_orbit_in_cycles_of_perm)
  {
    fix x assume "x \<in> ?C"
    then have "z \<notin> set_cycle x \<Longrightarrow> x \<in> ?C'"
      by (metis apply_cycle_cycles_of_perm apply_perm_neq_idI apply_skip_perm assms
          cycles_imp_cycles_skip poz_in_C skip_def start_in_perm_orbit_iff)
      also have x_orbit: "z \<in> set_cycle x \<Longrightarrow> x = perm_orbit p z"
        using \<open>x \<in> ?C\<close> perm_orbit_eqI by fastforce
      have "?poz \<noteq> ?poz'" 
        by (metis apply_cycle_delete apply_cycle_perm_orbit' apply_perm_neq_idI assms)
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
    using cycles_skip_diff by fast
  ultimately show "x \<in> ?C" by fast
qed

section \<open>Permutation domain lemmas\<close>
context perm_on
begin
lemma cycle_count_skip:
  assumes "finite S" "z \<in> S"
  shows "count_cycles_on S p = count_cycles_on (S - {z}) (skip_perm z p) + (if p z = z then 1 else 0)"
proof -
  consider "p z = z" | "p z \<noteq> z \<and> p (p z) = z" | "p (p z) \<noteq> z" by blast
then show ?thesis
proof cases
  case 1
  have "set_perm p = set_perm (skip_perm z p)"
    by (metis apply_perm_neq_idI 1 skip_perm_notin)
  moreover have "card (S - set_perm p) = Suc (card (S - {z} - set_perm (skip_perm z p)))"
    by (smt (z3) 1 Diff_eq_empty_iff Diff_insert2 One_nat_def Suc_pred add_Suc_right 
        add_diff_cancel_right' apply_perm_neq_idI assms calculation card_Diff_insert card_gt_0_iff 
        finite_Diff subsetD zero_less_Suc)
  ultimately show ?thesis
    by (smt (z3) "1" Nat.add_0_right add_Suc_right apply_perm_neq_idI count_cycles_on_def 
        perm_type_on_def size_replicate_mset One_nat_def size_union skip_perm_notin)
next
  case 2
  then have pz_id: "skip_perm z p (p z) = p z"
    by (simp add: apply_skip_perm)
  then have skip_z: "delete_cycle z (perm_orbit p z) = id_cycle"
    by (simp add: remove1_cycle_orbit)
  { have "cycles_of_perm p = cycles_of_perm (skip_perm z p) \<union> {perm_orbit p z}
                              - {delete_cycle z (perm_orbit p z)}"
      by (meson "2" apply_perm_eq_idI cycles_skip)
    then have "cycles_of_perm p = cycles_of_perm (skip_perm z p) \<union> {perm_orbit p z}"
        by (simp add: skip_z 2)
    moreover have "perm_orbit p z \<notin> cycles_of_perm (skip_perm z p)"
        by (simp add: perm_orbit_notin_skip_perm)
    ultimately have "card (cycles_of_perm p) = card (cycles_of_perm (skip_perm z p)) + 1"
      by (simp add: finite_cycles_of_perm)
  }
  moreover {
    have "set_perm p = set_perm (skip_perm z p) \<union> {z, p z}"
      by (meson 2 assms(1) set_perm_skip_2_cycle)
    also have "z \<notin> set_perm (skip_perm z p)"
      by (simp add: apply_skip_perm in_set_perm)
    moreover have "p z \<notin> set_perm (skip_perm z p)"
      using 2 \<open>(skip_perm z p) (p z) = p z\<close> by blast
    ultimately have "card (S - set_perm p) = card (S - {z} - set_perm (skip_perm z p)) - 1"
      by (smt (z3) Diff_iff Diff_insert2 Diff_insert_absorb Permutations.permutes_not_in 
          Un_insert_right apply_perm_eq_same_iff(1) apply_set_perm assms
          boolean_algebra_cancel.sup0 card_Diff_insert permutes_p singletonD)
    }
  ultimately show ?thesis
    apply (simp add: perm_on.count_cycles_on_eq_card perm_on.intro skip_perm_permutes permutes_p)
    by (smt (verit, ccfv_threshold) "2" Diff_eq_empty_iff Diff_insert_absorb Suc_pred 
        apply_perm_in_iff apply_perm_neq_idI assms card_gt_0_iff finite_Diff
        in_mono insertE mk_disjoint_insert pz_id set_perm_subset)
next
  case 3
  { then have "set_perm p = set_perm (skip_perm z p) \<union> {z}"
      by (metis set_perm_skip_n_cycle)
    also have "z \<notin> set_perm (skip_perm z p)"
      by (simp add: apply_skip_perm in_set_perm)
    ultimately have "S - set_perm p = S - {z} - set_perm (skip_perm z p)"
      by (metis Diff_insert2 Un_insert_right boolean_algebra_cancel.sup0)
  }
  also have "card (cycles_of_perm p) = card (cycles_of_perm (skip_perm z p))"
    by (smt (verit, ccfv_threshold) Diff_insert_absorb 3 Un_insert_right apply_set_perm 
        boolean_algebra_cancel.sup0 card.infinite card_0_eq card_Diff_insert card_insert_le 
        cycles_skip finite_cycles_of_perm insert_absorb insert_iff le_zero_eq
        perm_orbit_in_cycles_of_perm perm_orbit_notin_skip_perm remove1_cycle_orbit
        set_perm_skip_n_cycle)
  ultimately show ?thesis
    by (smt (z3) 3 add.right_neutral perm_on.count_cycles_on_eq_card 
        perm_on.intro permutes_p skip_perm_permutes)
qed
qed

end
end
