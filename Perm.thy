(*
  File:   Library/Perm.thy
  Author: Florian Haftmann, TU München
  Author: Manuel Eberl, TU München

  With some lemmas about even permutations adapted from Amine Chaieb
*)
section \<open>Permutations as abstract type\<close>

theory Perm
imports Main "HOL-Library.Disjoint_Sets" "HOL-Library.Stirling" "HOL-Library.Multiset"
begin

lemma bij_id' [simp, intro]: "bij (\<lambda>x. x)"
  using bij_id unfolding id_def .

lemma is_singleton_conv_Ex1: "is_singleton A \<longleftrightarrow> (\<exists>!x. x \<in> A)"
  by (auto simp: is_singleton_def)

lemma disjoint_family_on_Un_D:
  assumes "A \<inter> B = {}" "disjoint_family_on f (A \<union> B)"
  shows   "(\<Union>x\<in>A. f x) \<inter> (\<Union>x\<in>B. f x) = {}" "disjoint_family_on f A" "disjoint_family_on f B"
  using assms unfolding disjoint_family_on_def by force+
 
  
lemma disjoint_family_on_UnI [intro]:
  "disjoint_family_on f A \<Longrightarrow> disjoint_family_on f B \<Longrightarrow> (\<Union>x\<in>A. f x) \<inter> (\<Union>x\<in>B. f x) = {}
   \<Longrightarrow> disjoint_family_on f (A \<union> B)"
  unfolding disjoint_family_on_def by blast

lemma rotate_nth:
  assumes "i < length xs"
  shows   "rotate n xs ! i = xs ! ((i + n) mod length xs)"
  using assms
  by (metis hd_rotate_conv_nth length_rotate list.size(3) mod_if not_less_zero rotate_rotate)

lemma inj_funpow_cycle_exists:
  assumes "x \<in> A" "bij_betw f A A" "finite A"
  shows   "\<exists>n\<in>{0<..card A}. (f ^^ n) x = x \<and> inj_on (\<lambda>n. (f ^^ n) x) {..<n}"
proof -
  define N where "N = card A"
  have f_pow_in: "(f ^^ n) x \<in> A" if "x \<in> A" for x n
    using assms(2) that by (induction n) (auto simp: bij_betw_def)
  have "card ((\<lambda>n. (f ^^ n) x) ` {..N}) \<le> card A"
    using assms f_pow_in by (intro card_mono) auto
  also have "\<dots> < card {..N}"
    by (simp add: N_def)
  finally have "\<not>inj_on (\<lambda>n. (f ^^ n) x) {..N}"
    using pigeonhole by metis
  then obtain i' j' where i'j': "i' \<noteq> j'" "(f ^^ i') x = (f ^^ j') x" "i' \<le> N" "j' \<le> N"
    by (auto simp: inj_on_def)
  define i j where "i = min i' j'" and "j = max i' j' - min i' j'"
  have ij: "j > 0" "(f ^^ i) x = (f ^^ (i + j)) x" "j \<le> N"
    using i'j' by (auto simp: i_def j_def min_def max_def algebra_simps)

  have f_eq_iff: "f a = f b \<longleftrightarrow> a = b" if "a \<in> A" "b \<in> A" for a b
    using assms that by (auto simp: bij_betw_def inj_on_def)
  have f_pow_eq_iff: "(f ^^ n) a = (f ^^ n) b \<longleftrightarrow> a = b" if "a \<in> A" "b \<in> A" for a b n
    using that by (induction n) (auto simp: bij_betw_def inj_on_def f_eq_iff f_pow_in)

  note ij(2)
  also have "(f ^^ (i + j)) x = (f ^^ i) ((f ^^ j) x)"
    by (simp add: funpow_add)
  finally have j': "(f ^^ j) x = x"
    using assms by (subst (asm) f_pow_eq_iff) (auto simp: f_pow_in)

  define n where "n = (LEAST n. n > 0 \<and> (f ^^ n) x = x)"
  have "n > 0 \<and> (f ^^ n) x = x"
    unfolding n_def by (rule LeastI_ex) (use ij j' in auto)
  moreover have "n \<le> j"
    unfolding n_def by (rule Least_le) (use ij j' in auto)
  moreover have "inj_on (\<lambda>n. (f ^^ n) x) {..<n}"
  proof (rule ccontr)
    assume "\<not>inj_on (\<lambda>n. (f ^^ n) x) {..<n}"
    then obtain k' l' where k'l': "k' < n" "l' < n" "k' \<noteq> l'" "(f ^^ k') x = (f ^^ l') x"
      by (auto simp: inj_on_def)
    define k l where "k = min k' l'" and "l = max k' l' - min k' l'"
    have kl: "l > 0" "(f ^^ k) x = (f ^^ (k + l)) x" "l < n"
      using k'l' by (auto simp: min_def max_def k_def l_def)
    hence "(f ^^ k) x = (f ^^ k) ((f ^^ l) x)"
      by (simp add: funpow_add)
    hence "(f ^^ l) x = x"
      using \<open>x \<in> A\<close> by (subst (asm) f_pow_eq_iff) (auto simp: f_pow_in)
    have "l \<ge> n"
      unfolding n_def by (rule Least_le) (use kl \<open>(f ^^ l) x = x\<close> in auto)
    with kl show False by simp
  qed
  ultimately show ?thesis
    using \<open>j > 0\<close> and \<open>j \<le> N\<close> by (auto simp: N_def)
qed

lemma finite_distinct_lists:
  assumes "finite A"
  shows   "finite {xs. distinct xs \<and> set xs \<subseteq> A}"
proof -
  have "{xs. distinct xs \<and> set xs \<subseteq> A} \<subseteq> {xs. set xs \<subseteq> A \<and> length xs \<le> card A}"
  proof safe
    fix xs assume xs: "distinct xs" "set xs \<subseteq> A"
    from xs have "length xs = card (set xs)"
      by (auto simp: distinct_card)
    also have "\<dots> \<le> card A"
      using assms xs by (intro card_mono) auto
    finally show "length xs \<le> card A" .
  qed
  moreover have "finite \<dots>"
    using assms finite_lists_length_le by blast
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma card_distinct_lists_set_eq:
  assumes "finite A"
  shows   "card {xs. distinct xs \<and> set xs = A} = fact (card A)"
proof -
  have "{xs. distinct xs \<and> set xs = A} =
        {xs. length xs = card A \<and> distinct xs \<and> set xs \<subseteq> A}"
  proof (intro equalityI subsetI)
    fix xs assume xs: "xs \<in> {xs. length xs = card A \<and> distinct xs \<and> set xs \<subseteq> A}"
    hence "set xs = A"
      by (intro card_subset_eq) (auto simp: distinct_card assms)
    with xs show "xs \<in> {xs. distinct xs \<and> set xs = A}" by simp
  qed (auto simp: distinct_card)
  also have "card \<dots> = \<Prod>{1..card A}"
    by (subst card_lists_distinct_length_eq) (use assms in auto)
  also have "\<dots> = fact (card A)"
    by (simp add: fact_prod)
  finally show ?thesis .
qed

lemma finite_bij_nats_lessThan:
  assumes "finite (A :: 'a :: linorder set)"
  obtains f where "f ` {..<card A} = A" "strict_mono_on f {..<card A}"
proof -
  define xs where "xs = sorted_list_of_set A"
  define f where "f = (\<lambda>i. xs ! i)"
  have len: "length xs = card A"
    using assms unfolding xs_def
    by (metis distinct_card distinct_sorted_list_of_set set_sorted_list_of_set)
  have "f ` {..<length xs} = set xs"
    unfolding f_def by (subst set_conv_nth) auto
  also have "set xs = A"
    using assms by (simp add: xs_def)
  also have "length xs = card A"
    using assms unfolding xs_def
    by (metis distinct_card distinct_sorted_list_of_set set_sorted_list_of_set)
  finally have "f ` {..<card A} = A" .
  moreover have "distinct xs" "sorted xs"
    by (auto simp: xs_def)
  hence "strict_mono_on f {..<card A}"
    unfolding f_def
    by (intro strict_mono_onI order.not_eq_order_implies_strict sorted_nth_mono)
       (auto simp: distinct_conv_nth \<open>length xs = _\<close>)
  ultimately show ?thesis using that[of f] by blast
qed




declare [[coercion_enabled]]

text \<open>
  This theory introduces basics about permutations, i.e. almost
  everywhere fix bijections.  But it is by no means complete.
  Grieviously missing are cycles since these would require more
  elaboration, e.g. the concept of distinct lists equivalent
  under rotation, which maybe would also deserve its own theory.
  But see theory \<open>src/HOL/ex/Perm_Fragments.thy\<close> for
  fragments on that.
\<close>

subsection \<open>Abstract type of permutations\<close>

typedef 'a perm = "{f :: 'a \<Rightarrow> 'a. bij f \<and> finite {a. f a \<noteq> a}}"
  morphisms "apply_perm" Perm
proof
  show "id \<in> ?perm" by simp
qed

declare [[coercion "apply_perm"]]

setup_lifting type_definition_perm

notation apply_perm (infixr "\<langle>$\<rangle>" 999)

lemma apply_perm_Perm:
  assumes "finite A" "inj_on f A" "\<And>x. x \<in> A \<Longrightarrow> f x \<in> A" "\<And>x. x \<notin> A \<Longrightarrow> f x = x"
  shows   "(Perm f) \<langle>$\<rangle> x = f x"
proof (subst Perm_inverse; safe)
  show "finite {x. f x \<noteq> x}"
    by (rule finite_subset[OF _ assms(1)]) (use assms(4) in auto)
  have "bij_betw f A A"
    unfolding bij_betw_def
  proof
    show "inj_on f A" by fact
    have subset: "f ` A \<subseteq> A"
      using assms(3) by auto
    have "A \<subseteq> f ` A \<longleftrightarrow> (\<forall>y\<in>A. \<exists>x\<in>A. f x = y)"
      by auto
    also have "\<dots> \<longleftrightarrow> inj_on f A"
      by (intro surjective_iff_injective_gen subset assms refl)
    finally have "A \<subseteq> f ` A"
      using \<open>inj_on f A\<close> by simp
    with subset show "f ` A = A"
      by (intro antisym)
  qed
  moreover {
    have "bij_betw id (-A) (-A)"
      by simp
    also have "?this \<longleftrightarrow> bij_betw f (-A) (-A)"
      using assms(4) by (intro bij_betw_cong) auto
    finally have "bij_betw f (-A) (-A)" .
  }
  ultimately have "bij_betw f (A \<union> -A) (A \<union> -A)"
    by (intro bij_betw_combine) auto
  also have "A \<union> -A = UNIV"
    by auto
  finally show "bij f" .
qed

lemma bij_apply [simp]:
  "bij (apply_perm f)"
  using "apply_perm" [of f] by simp

lemma perm_eqI:
  assumes "\<And>a. f \<langle>$\<rangle> a = g \<langle>$\<rangle> a"
  shows "f = g"
  using assms by transfer (simp add: fun_eq_iff)

lemma perm_eq_iff:
  "f = g \<longleftrightarrow> (\<forall>a. f \<langle>$\<rangle> a = g \<langle>$\<rangle> a)"
  by (auto intro: perm_eqI)

lemma apply_inj_eq_iff [simp]:
  "f \<langle>$\<rangle> a = f \<langle>$\<rangle> b \<longleftrightarrow> a = b"
  by (rule inj_eq) (rule bij_is_inj, simp)

lemma inj_on_apply_perm [intro]: "inj_on (apply_perm p) A"
  by (auto simp: inj_on_def)

lift_definition set_perm :: "'a perm \<Rightarrow> 'a set"
  is "\<lambda>f. {a. f a \<noteq> a}" .

lemma in_set_perm:
  "a \<in> set_perm f \<longleftrightarrow> f \<langle>$\<rangle> a \<noteq> a"
  by transfer simp

lemma not_in_set_perm:
  "a \<notin> set_perm f \<longleftrightarrow> f \<langle>$\<rangle> a = a"
  by transfer simp

lemma set_perm_eq: "set_perm p = {x. p \<langle>$\<rangle> x \<noteq> x}"
  by transfer simp

lemma in_set_permD [dest]: "x \<in> set_perm p \<Longrightarrow> p \<langle>$\<rangle> x \<noteq> x"
  unfolding set_perm_eq by blast

lemma not_in_set_permD [dest]: "x \<notin> set_perm p \<Longrightarrow> p \<langle>$\<rangle> x = x"
  unfolding set_perm_eq by blast

lemma in_set_permI [intro]: "p \<langle>$\<rangle> x \<noteq> x \<Longrightarrow> x \<in> set_perm p"
  unfolding set_perm_eq by blast

lemma apply_perm_eq_idI: "x \<notin> set_perm p \<Longrightarrow> p \<langle>$\<rangle> x = x"
  unfolding set_perm_eq by blast

lemma apply_perm_neq_idI: "x \<in> set_perm p \<Longrightarrow> p \<langle>$\<rangle> x \<noteq> x"
  unfolding set_perm_eq by blast

lemma apply_perm_eq_same_iff:
  "f \<langle>$\<rangle> a = a \<longleftrightarrow> a \<notin> set_perm f"
  "a = f \<langle>$\<rangle> a \<longleftrightarrow> a \<notin> set_perm f"
  by (auto simp: set_perm_eq)

lemma finite_set_perm [simp]:
  "finite (set_perm f)"
  by transfer simp

lemma apply_set_perm [simp]:
  "f \<langle>$\<rangle> a \<in> set_perm f \<longleftrightarrow> a \<in> set_perm f"
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a :: 'a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" by simp
  interpret bijection f by standard (rule \<open>bij f\<close>)
  have "f a \<in> {a. f a = a} \<longleftrightarrow> a \<in> {a. f a = a}" (is "?P \<longleftrightarrow> ?Q")
    by auto
  then show "f a \<in> {a. f a \<noteq> a} \<longleftrightarrow> a \<in> {a. f a \<noteq> a}"
    by simp
qed

lemma apply_perm_in:
  assumes "set_perm p \<subseteq> A" and "x \<in> A"
  shows   "p \<langle>$\<rangle> x \<in> A"
proof (cases "x \<in> set_perm p")
  case True
  hence "p \<langle>$\<rangle> x \<in> set_perm p"
    by simp
  also have "\<dots> \<subseteq> A"
    by fact
  finally show ?thesis .
next
  case False
  have "x \<in> A"
    by fact
  also have "x = p \<langle>$\<rangle> x"
    using False by auto
  finally show ?thesis .
qed

lemma card_set_perm_not_one:
  "card (set_perm f) \<noteq> 1"
proof
  interpret bijection "apply_perm f"
    by standard (rule bij_apply)
  assume "card (set_perm f) = 1"
  then obtain a where *: "set_perm f = {a}"
    by (rule card_1_singletonE)
  then have **: "f \<langle>$\<rangle> a \<noteq> a"
    by (simp flip: in_set_perm)
  with * have "f \<langle>$\<rangle> a \<notin> set_perm f"
    by simp
  then have "f \<langle>$\<rangle> (f \<langle>$\<rangle> a) = f \<langle>$\<rangle> a"
    by (simp add: apply_perm_eq_same_iff)
  then have "inv (apply_perm f) (f \<langle>$\<rangle> (f \<langle>$\<rangle> a)) = inv (apply_perm f) (f \<langle>$\<rangle> a)"
    by simp
  with ** show False by simp
qed

instantiation perm :: (type) size
begin

definition size_perm :: "'a perm \<Rightarrow> nat" where
  "size p = card (set_perm p)"

instance ..
end

lemma card_set_perm [simp]: "card (set_perm p) = size p"
  by (simp add: size_perm_def)


subsection \<open>Identity, composition and inversion\<close>

instantiation Perm.perm :: (type) "{monoid_mult, inverse}"
begin

lift_definition one_perm :: "'a perm"
  is id
  by simp

lemma set_perm_one [simp]:
  "set_perm 1 = {}"
  by transfer simp

lemma set_perm_empty_iff [simp]:
  "set_perm f = {} \<longleftrightarrow> f = 1"
  by transfer auto

lift_definition times_perm :: "'a perm \<Rightarrow> 'a perm \<Rightarrow> 'a perm"
  is comp
proof
  fix f g :: "'a \<Rightarrow> 'a"
  assume "bij f \<and> finite {a. f a \<noteq> a}"
    "bij g \<and>finite {a. g a \<noteq> a}"
  then have "finite ({a. f a \<noteq> a} \<union> {a. g a \<noteq> a})"
    by simp
  moreover have "{a. (f \<circ> g) a \<noteq> a} \<subseteq> {a. f a \<noteq> a} \<union> {a. g a \<noteq> a}"
    by auto
  ultimately show "finite {a. (f \<circ> g) a \<noteq> a}"
    by (auto intro: finite_subset)
qed (auto intro: bij_comp)

lemma apply_perm_times:
  "apply_perm (f * g) = apply_perm f \<circ> apply_perm g"
  by (fact times_perm.rep_eq)

lemma apply_perm_sequence:
  "f \<langle>$\<rangle> (g \<langle>$\<rangle> a) = apply_perm (f * g) a"
  by (simp add: apply_perm_times)

lemma set_perm_times:
  "set_perm (f * g) \<subseteq> set_perm f \<union> set_perm g"
  by transfer auto

lemma set_perm_timesE [elim]:
  assumes "x \<in> set_perm (f * g)"
  obtains "x \<in> set_perm f" | "x \<in> set_perm g"
  using assms set_perm_times[of f g] by auto

lift_definition inverse_perm :: "'a perm \<Rightarrow> 'a perm"
  is inv
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" and fin: "finite {b. f b \<noteq> b}"
    by auto
  interpret bijection f by standard (rule \<open>bij f\<close>)
  from fin show "bij (inv f) \<and> finite {a. inv f a \<noteq> a}"
    by (simp add: bij_inv)
qed

instance
  by standard (transfer; simp add: comp_assoc)+

end

abbreviation id_perm :: "'a perm" where
  "id_perm \<equiv> 1"

lemma apply_perm_id [simp]: "apply_perm 1 = id"
  by transfer (rule refl)

lemma apply_perm_inverse:
  "apply_perm (inverse f) = inv (apply_perm f)"
  by (fact inverse_perm.rep_eq)

lemma set_perm_inverse [simp]:
  "set_perm (inverse f) = set_perm f"
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and a
  assume "bij f \<and> finite {b. f b \<noteq> b}"
  then have "bij f" by simp
  interpret bijection f by standard (rule \<open>bij f\<close>)
  show "{a. inv f a \<noteq> a} = {a. f a \<noteq> a}"
    by simp
qed

global_interpretation perm: group times id_perm inverse
proof
  fix f :: "'a perm"
  show "1 * f = f"
    by transfer simp
  show "inverse f * f = 1"
  proof transfer
    fix f :: "'a \<Rightarrow> 'a" and a
    assume "bij f \<and> finite {b. f b \<noteq> b}"
    then have "bij f" by simp
    interpret bijection f by standard (rule \<open>bij f\<close>)
    show "inv f \<circ> f = id"
      by simp
  qed
qed

declare perm.inverse_distrib_swap [simp]

lemma apply_perm_inverse_eq_iff [simp]: "(inverse p) \<langle>$\<rangle> x = y \<longleftrightarrow> p \<langle>$\<rangle> y = x"
  by (metis apply_perm_sequence id_apply one_perm.rep_eq perm.left_inverse)

lemma eq_apply_perm_inverse_iff [simp]: "y = (inverse p) \<langle>$\<rangle> x \<longleftrightarrow> p \<langle>$\<rangle> y = x"
  using apply_perm_inverse_eq_iff[of p x y] by fast

lemma apply_perm_inverse_not_in_set [simp]: "x \<notin> set_perm p \<Longrightarrow> (inverse p) \<langle>$\<rangle> x = x"
  by (auto intro: apply_perm_eq_idI)

lemma perm_mult_commute:
  assumes "set_perm f \<inter> set_perm g = {}"
  shows "g * f = f * g"
proof (rule perm_eqI)
  fix a
  from assms have *: "a \<in> set_perm f \<Longrightarrow> a \<notin> set_perm g"
    "a \<in> set_perm g \<Longrightarrow> a \<notin> set_perm f" for a
    by auto
  consider "a \<in> set_perm f \<and> a \<notin> set_perm g
        \<and> f \<langle>$\<rangle> a \<in> set_perm f"
    | "a \<notin> set_perm f \<and> a \<in> set_perm g
        \<and> f \<langle>$\<rangle> a \<notin> set_perm f"
    | "a \<notin> set_perm f \<and> a \<notin> set_perm g"
    using assms by auto
  then show "(g * f) \<langle>$\<rangle> a = (f * g) \<langle>$\<rangle> a"
  proof cases
    case 1
    with * have "f \<langle>$\<rangle> a \<notin> set_perm g"
      by auto
    with 1 show ?thesis by (simp add: apply_perm_times in_set_perm)
  next
    case 2
    with * have "g \<langle>$\<rangle> a \<notin> set_perm f"
      by auto
    with 2 show ?thesis by (simp add: apply_perm_times in_set_perm)
  next
    case 3
    then show ?thesis by (simp add: apply_perm_times in_set_perm)
  qed
qed

lemma apply_perm_power:
  "apply_perm (f ^ n) = apply_perm f ^^ n"
  by (induct n) (simp_all add: apply_perm_times)

lemma set_perm_power: "set_perm (f ^ n) \<subseteq> set_perm f"
  by (induction n) auto

lemma set_perm_powerD [dest]: "x \<in> set_perm (f ^ n) \<Longrightarrow> x \<in> set_perm f"
  using set_perm_power[of f n] by blast

lemma set_perm_power_int: "set_perm (f powi n) \<subseteq> set_perm f"
  by (auto simp: power_int_def)

lemma set_perm_power_intD [dest]: "x \<in> set_perm (f powi n) \<Longrightarrow> x \<in> set_perm f"
  using set_perm_power_int[of f n] by blast

lemma perm_power_inverse:
  "inverse f ^ n = inverse ((f :: 'a perm) ^ n)"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case
    unfolding power_Suc2 [of f] by simp
qed

lemma bij_betw_apply_perm [intro]:
  assumes "set_perm p \<subseteq> A"
  shows   "bij_betw (apply_perm p) A A"
  unfolding bij_betw_def
proof safe
  fix x assume "x \<in> A"
  thus "p \<langle>$\<rangle> x \<in> A"
    by (intro apply_perm_in assms)
next
  fix x assume "x \<in> A"
  with assms have "p \<langle>$\<rangle> (inverse p) \<langle>$\<rangle> x \<in> apply_perm p ` A"
    by (intro imageI apply_perm_in) auto
  thus "x \<in> apply_perm p ` A"
    by (simp add: apply_perm_sequence)
qed (use assms in auto)

lemma apply_perm_image:
  assumes "set_perm p \<subseteq> A"
  shows   "apply_perm p ` A = A"
  using bij_betw_apply_perm[OF assms] by (simp add: bij_betw_def)

lemma apply_perm_in_iff [simp]:
  assumes "set_perm p \<subseteq> A"
  shows   "p \<langle>$\<rangle> x \<in> A \<longleftrightarrow> x \<in> A"
  using apply_perm_image[OF assms] apply_perm_image[of "inverse p" A] assms by auto

lemma apply_perm_inverse_cancel [simp]: "p * p' = id_perm \<Longrightarrow> p \<langle>$\<rangle> (p' \<langle>$\<rangle> x) = x"
  by (simp add: apply_perm_sequence)

lemmas apply_perm_simps =
  apply_perm_times apply_perm_inverse apply_perm_power

lemma size_perm_id [simp]: "size id_perm = 0"
  by (simp flip: card_set_perm)

lemma size_perm_times: "size (p * q :: 'a perm) \<le> size p + size q"
proof -
  have "card (set_perm (p * q)) \<le> card (set_perm p \<union> set_perm q)"
    by (intro card_mono set_perm_times) auto
  also have "\<dots> \<le> size p + size q"
    unfolding size_perm_def by (intro card_Un_le)
  finally show ?thesis
    by (simp only: size_perm_def)
qed

lemma size_perm_inverse [simp]: "size (inverse p :: 'a perm) = size p"
  by (simp flip: card_set_perm)

lemma size_perm_power: "size (p ^ n :: 'a perm) \<le> size p"
  unfolding size_perm_def by (intro card_mono) (auto simp: size_perm_def)

lemma size_perm_power_int: "size (p powi n :: 'a perm) \<le> size p"
  by (auto simp: power_int_def intro: order.trans[OF size_perm_power])


subsection \<open>Swaps\<close>

lift_definition swap_perm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a perm"  ("\<langle>_ \<leftrightarrow> _\<rangle>")
  is "\<lambda>a b. Fun.swap a b id"
proof
  fix a b :: 'a
  have "{c. Fun.swap a b id c \<noteq> c} \<subseteq> {a, b}"
    by (auto simp add: Fun.swap_def)
  then show "finite {c. Fun.swap a b id c \<noteq> c}"
    by (rule finite_subset) simp
qed simp

lemma apply_perm_swap_eq:
  "apply_perm \<langle>a \<leftrightarrow> b\<rangle> = Fun.swap a b id"
  by transfer (rule refl)

lemma apply_perm_swap [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> a = b"
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> b = a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = c"
  by (transfer; simp; fail)+

lemma apply_perm_swap_eq_iff [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = a \<longleftrightarrow> c = b"
  "\<langle>a \<leftrightarrow> b\<rangle> \<langle>$\<rangle> c = b \<longleftrightarrow> c = a"
  by (transfer; auto simp add: Fun.swap_def)+

lemma swap_perm_same [simp]:
  "\<langle>a \<leftrightarrow> a\<rangle> = 1"
  by transfer simp

lemma swap_commute:
  "\<langle>b \<leftrightarrow> a\<rangle> = \<langle>a \<leftrightarrow> b\<rangle>"
  by (transfer; auto simp add: Fun.swap_def)+

lemma swap_perm_times_self [simp]:
  "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> = 1"
  "\<langle>b \<leftrightarrow> a\<rangle> * \<langle>a \<leftrightarrow> b\<rangle> = 1"
  by (transfer; simp add: Fun.swap_def fun_eq_iff; fail)+

lemma swap_perm_times_commute:
  assumes "a \<noteq> c" "a \<noteq> d" "b \<noteq> c" "b \<noteq> d"
  shows   "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> = \<langle>c \<leftrightarrow> d\<rangle> * \<langle>a \<leftrightarrow> b\<rangle>"
  using assms by transfer (auto simp: fun_eq_iff Fun.swap_def)

lemma set_perm_swap [simp]:
  "a \<noteq> b \<Longrightarrow> set_perm \<langle>a \<leftrightarrow> b\<rangle> = {a, b}"
  by transfer (auto simp add: Fun.swap_def)

lemma set_perm_swap':
  "set_perm \<langle>a \<leftrightarrow> b\<rangle> = (if a = b then {} else {a, b})"
  by transfer (auto simp add: Fun.swap_def)

lemma inverse_swap [simp]:
  "inverse \<langle>a \<leftrightarrow> b\<rangle> = \<langle>a \<leftrightarrow> b\<rangle>"
  by transfer (auto intro: inv_equality simp: Fun.swap_def)

lemma perm_swap_power: "\<langle>a \<leftrightarrow> b\<rangle> ^ n = (if even n then id_perm else \<langle>a \<leftrightarrow> b\<rangle>)"
  by (induction n) auto

lemma perm_swap_power_even [simp]: "even n \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> ^ n = id_perm"
  and perm_swap_power_odd [simp]: "odd n \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> ^ n = \<langle>a \<leftrightarrow> b\<rangle>"
  by (simp_all add: perm_swap_power)

lemma perm_swap_power_int: "\<langle>a \<leftrightarrow> b\<rangle> powi n = (if even n then id_perm else \<langle>a \<leftrightarrow> b\<rangle>)"
  by (auto simp: power_int_def perm_swap_power even_nat_iff)

lemma perm_swap_power_int_even: "even n \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> powi n = id_perm"
  and perm_swap_power_int_odd [simp]: "odd n \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> powi n = \<langle>a \<leftrightarrow> b\<rangle>"
  by (simp_all add: perm_swap_power_int)

lemma perm_swap_cong: "{a, b} = {c, d} \<Longrightarrow> \<langle>a \<leftrightarrow> b\<rangle> = \<langle>c \<leftrightarrow> d\<rangle>"
  by transfer (auto simp: Fun.swap_def fun_eq_iff)


definition swaps_set :: "('a \<times> 'a) list \<Rightarrow> 'a set" where
  "swaps_set xs = (\<Union>(x,y)\<in>set xs. {x, y})"

definition perm_swaps :: "('a \<times> 'a) list \<Rightarrow> 'a perm"
  where "perm_swaps xs = (\<Prod>(a,b)\<leftarrow>xs. \<langle>a \<leftrightarrow> b\<rangle>)"

lemma perm_swaps_Nil [simp]: "perm_swaps [] = id_perm"
  and perm_swaps_Cons [simp]: "perm_swaps (x # xs) = \<langle>fst x \<leftrightarrow> snd x\<rangle> * perm_swaps xs"
  and perm_swaps_append [simp]: "perm_swaps (xs @ ys) = perm_swaps xs * perm_swaps ys"
  by (simp_all add: perm_swaps_def case_prod_unfold)

lemma set_perm_swaps: "set_perm (perm_swaps xs) \<subseteq> swaps_set xs"
proof (induction xs)
  case (Cons x xs)
  have "set_perm (perm_swaps (x # xs)) = set_perm (\<langle>fst x \<leftrightarrow> snd x\<rangle> * perm_swaps xs)"
    by simp
  also have "\<dots> \<subseteq> set_perm \<langle>fst x \<leftrightarrow> snd x\<rangle> \<union> set_perm (perm_swaps xs)"
    by (rule set_perm_times)
  also have "\<dots> \<subseteq> swaps_set (x # xs)"
    using Cons by (auto simp: case_prod_unfold set_perm_swap' swaps_set_def)
  finally show ?case .
qed auto

lemma perm_swaps_replicate [simp]: "perm_swaps (replicate n z) = \<langle>fst z \<leftrightarrow> snd z\<rangle> ^ n"
  by (induction n) auto

lemma perm_swaps_reverse [simp]: "perm_swaps (rev xs) = inverse (perm_swaps xs)"
  by (induction xs) auto

lemma perm_swaps_cong:
  assumes "list_all2 (\<lambda>(a,b) (c,d). {a, b} = {c, d}) xs ys"
  shows   "perm_swaps xs = perm_swaps ys"
  using assms by induction (auto dest: perm_swap_cong)

lemma size_perm_swap [simp]: "a \<noteq> b \<Longrightarrow> size \<langle>a \<leftrightarrow> b\<rangle> = 2"
  by (simp flip: card_set_perm)

lemma size_perm_swap': "size \<langle>a \<leftrightarrow> b\<rangle> = (if a = b then 0 else 2)"
  by (simp flip: card_set_perm add: set_perm_swap')


subsection \<open>Representing a permutation as a product of swaps\<close>

declare perm.Perm_induct [induct del]

lemma perm_induct' [consumes 1, case_names id swap]:
  assumes "set_perm p \<subseteq> A"
  assumes "P id_perm"
  assumes "\<And>a b q. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> set_perm q \<subseteq> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> P q \<Longrightarrow> P (\<langle>a \<leftrightarrow> b\<rangle> * q)"
  shows   "P p"
proof -
  have "finite (set_perm p)"
    by auto
  from this and assms(1) show ?thesis
  proof (induction "set_perm p" arbitrary: p rule: finite_psubset_induct)
    case (psubset p)
    show ?case
    proof (cases "p = id_perm")
      case True
      thus ?thesis using assms by simp
    next
      case False
      hence "set_perm p \<noteq> {}"
        by auto
      then obtain a where a: "a \<in> set_perm p"
        by blast
      have "P (\<langle>a \<leftrightarrow> p a\<rangle> * (\<langle>a \<leftrightarrow> p a\<rangle> * p))"
      proof (rule assms(3))
        have subset: "set_perm (\<langle>a \<leftrightarrow> p a\<rangle> * p) \<subseteq> set_perm p - {a}"
          by (auto simp: set_perm_eq apply_perm_simps apply_perm_swap_eq Fun.swap_def)
        thus "set_perm (\<langle>a \<leftrightarrow> p \<langle>$\<rangle> a\<rangle> * p) \<subseteq> A"
          using psubset by auto
        note subset
        also have "set_perm p - {a} \<subset> set_perm p"
          using a by auto
        finally show "P (\<langle>a \<leftrightarrow> p a\<rangle> * p)"
          using psubset.prems by (intro psubset) auto
      next
        have "{a, p \<langle>$\<rangle> a} \<subseteq> set_perm p"
          using a by auto
        also have "\<dots> \<subseteq> A"
          by fact
        finally show "a \<in> A" "p \<langle>$\<rangle> a \<in> A"
          by auto
      next
        
      qed (use a in \<open>auto simp: apply_perm_eq_same_iff\<close>)
      also have "\<langle>a \<leftrightarrow> p a\<rangle> * (\<langle>a \<leftrightarrow> p a\<rangle> * p) = p"
        by (simp flip: mult.assoc)
      finally show ?thesis .
    qed
  qed
qed

lemma perm_rev_induct' [consumes 1, case_names id swap]:
  assumes "set_perm p \<subseteq> A" and "P id_perm"
  assumes "\<And>a b q. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> set_perm q \<subseteq> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> P q \<Longrightarrow> P (q * \<langle>a \<leftrightarrow> b\<rangle>)"
  shows   "P p"
proof -
  from assms(1) have "set_perm (inverse p) \<subseteq> A"
    by simp
  hence "P (inverse (inverse p))"
    by (induction rule: perm_induct') (auto intro!: assms)
  thus ?thesis
    by simp
qed

lemmas perm_induct [case_names id swap, induct type] = perm_induct'[OF order.refl]
lemmas perm_rev_induct [case_names id swap] = perm_rev_induct'[OF order.refl]



lemma ex_perm_swaps: "\<exists>xs. swaps_set xs \<subseteq> set_perm p \<and> (\<forall>(x,y)\<in>set xs. x \<noteq> y) \<and> perm_swaps xs = p"
proof -
  define A where "A = set_perm p"
  have "set_perm p \<subseteq> A"
    by (simp add: A_def)
  thus "\<exists>xs. swaps_set xs \<subseteq> A \<and> (\<forall>(x,y)\<in>set xs. x \<noteq> y) \<and> perm_swaps xs = p"
  proof (induction p rule: perm_induct')
    case id
    thus ?case by (intro exI[of _ "[]"]) (auto simp: swaps_set_def)
  next
    case (swap a b q)
    obtain xs where "(\<Union>(a,b)\<in>set xs. {a,b}) \<subseteq> A" "\<forall>(x,y)\<in>set xs. x \<noteq> y" "perm_swaps xs = q"
      using swap.IH unfolding swaps_set_def by blast
    with swap.hyps show ?case unfolding swaps_set_def
      by (intro exI[of _ "(a, b) # xs"]) simp_all
  qed
qed


subsection \<open>Even and odd permutations\<close>

definition even_perm :: "'a perm \<Rightarrow> bool" where
  "even_perm p \<longleftrightarrow>
     (\<forall>xs. swaps_set xs \<subseteq> set_perm p \<and> (\<forall>(x,y)\<in>set xs. x \<noteq> y) \<longrightarrow>
       perm_swaps xs = p \<longrightarrow> even (length xs))"

abbreviation odd_perm :: "'a perm \<Rightarrow> bool" where
  "odd_perm p \<equiv> \<not>even_perm p"

definition sgn_perm :: "'a perm \<Rightarrow> int" where "sgn_perm p = (if even_perm p then 1 else -1)"

text \<open>
  The following alternative definition makes it a bit clearer that the definition is parametric:
\<close>
lemma even_perm_def_parametric:
  "even_perm p \<longleftrightarrow>
     (\<forall>xs\<in>lists (set_perm p \<times> set_perm p). (\<forall>(x,y)\<in>set xs. x \<noteq> y) \<longrightarrow>
       perm_swaps xs = p \<longrightarrow> even (length xs))"
  by (fastforce simp: even_perm_def swaps_set_def lists_eq_set)

lemma even_perm_id [simp, intro]: "even_perm id_perm"
  unfolding even_perm_def_parametric by auto

lemma not_even_perm_swap [simp]:
  assumes "a \<noteq> b"
  shows   "\<not>even_perm \<langle>a \<leftrightarrow> b\<rangle>"
proof -
  have "[(a, b)] \<in> lists (set_perm  \<langle>a \<leftrightarrow> b\<rangle> \<times> set_perm  \<langle>a \<leftrightarrow> b\<rangle>)"
       "\<forall>(x,y)\<in>set [(a,b)]. x \<noteq> y" "perm_swaps [(a,b)] = \<langle>a \<leftrightarrow> b\<rangle>" "odd (length [(a,b)])"
    using assms by auto
  thus ?thesis unfolding even_perm_def_parametric
    by blast
qed

lemma swap_perm_commute_exists_lemma[consumes 2, case_names wlog sym]:
  assumes "a \<noteq> b" "c \<noteq> d"
    and "\<And>a b c d. a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow>
      a = c \<and> b = d \<or> a = c \<and> b \<noteq> d \<or> a \<noteq> c \<and> b = d \<or> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<Longrightarrow>
      P a b c d"
  assumes "\<And>a b c d. P a b c d \<Longrightarrow> P a b d c"
  shows "P a b c d"
  using assms by metis

lemma swap_perm_commute_exists:
  assumes "a \<noteq> b" and "c \<noteq> d"
  obtains "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> = id_perm" |
  x y z where "x \<noteq> a" "y \<noteq> a" "z \<noteq> a" "x \<noteq> y" "{x,y,z} \<subseteq> {b,c,d}"
              "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> = \<langle>x \<leftrightarrow> y\<rangle> * \<langle>a \<leftrightarrow> z\<rangle>"
  using assms that
proof (induction a b c d rule: swap_perm_commute_exists_lemma)
  case (wlog a b c d)
  from this(3) show ?thesis
  proof (elim disjE conjE)
    assume "a = c" "b = d"
    thus ?thesis using wlog.prems(1)
      by (auto dest: perm_swap_cong)
  next
    assume "a = c" "b \<noteq> d"
      thus ?thesis using wlog.hyps
        by (intro wlog.prems(2)[of b d b])
           (auto intro!: perm_eqI simp: apply_perm_swap_eq apply_perm_simps Fun.swap_def)
  next
    assume "a \<noteq> c" "b = d"
      thus ?thesis using wlog.hyps
        by (intro wlog.prems(2)[of c d c])
           (auto intro!: perm_eqI simp: apply_perm_swap_eq apply_perm_simps Fun.swap_def)
  next
    assume "a \<noteq> c" "a \<noteq> d" "b \<noteq> c" "b \<noteq> d"
      thus ?thesis using wlog.hyps
        by (intro wlog.prems(2)[of c d b])
           (auto intro!: perm_eqI simp: apply_perm_swap_eq apply_perm_simps Fun.swap_def)
  qed
qed (simp add: swap_commute insert_commute)

lemma even_perm_welldefined_aux1:
  assumes "a \<noteq> b" and "\<forall>(x,y)\<in>set xs. x \<noteq> y" and "(perm_swaps ((a,b) # xs)) \<langle>$\<rangle> a = a"
  shows   "\<exists>ys. length xs = length ys + 1 \<and> swaps_set ys \<subseteq> swaps_set ((a,b)#xs) \<and>
                (\<forall>(x,y)\<in>set ys. x \<noteq> y) \<and> perm_swaps ys = perm_swaps ((a,b) # xs)"
  using assms
proof (induction xs arbitrary: a b)
  case Nil
  thus ?case by auto
next
  case (Cons cd xs a b)
  obtain c d where [simp]: "cd = (c, d)"
    by (cases cd)
  define q where "q = perm_swaps xs"
  have "a \<noteq> b" "c \<noteq> d"
    using Cons by auto
  consider "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> = id_perm"
    | x y z where  "x \<noteq> a" "y \<noteq> a" "z \<noteq> a" "x \<noteq> y" "{x,y,z} \<subseteq> {b,c,d}"
                   "\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> = \<langle>x \<leftrightarrow> y\<rangle> * \<langle>a \<leftrightarrow> z\<rangle>"
    using swap_perm_commute_exists[OF \<open>a \<noteq> b\<close> \<open>c \<noteq> d\<close>] by metis
  thus ?case
  proof cases
    case 1
    thus ?thesis using Cons.prems
      by (intro exI[of _ xs]) (auto simp flip: mult.assoc simp: swaps_set_def)
  next
    case 2
    have "a = (\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle> * q) \<langle>$\<rangle> a"
      using Cons.prems(3) by (simp add: q_def mult.assoc)
    also have "inverse (\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle>) \<dots> = q \<langle>$\<rangle> a"
      by (simp add: apply_perm_simps)
    also have "inverse (\<langle>a \<leftrightarrow> b\<rangle> * \<langle>c \<leftrightarrow> d\<rangle>) = \<langle>a \<leftrightarrow> z\<rangle> * \<langle>x \<leftrightarrow> y\<rangle>"
      using 2 by simp
    also have "\<dots> \<langle>$\<rangle> a = z"
      using 2 by (simp add: apply_perm_simps)
    finally have q_a: "q \<langle>$\<rangle> a = z" ..
    
    have "\<exists>ys. length xs = length ys + 1 \<and> swaps_set ys \<subseteq> swaps_set ((a, z) # xs) \<and>
               (\<forall>(x,y)\<in>set ys. x \<noteq> y) \<and> perm_swaps ys = perm_swaps ((a, z) # xs)"
      using 2 Cons q_a by (intro Cons) (auto simp: case_prod_unfold apply_perm_simps q_def)
    then obtain ys where ys: "length xs = length ys + 1" "swaps_set ys \<subseteq> swaps_set ((a,z)#xs)"
                             "\<forall>(x,y)\<in>set ys. x \<noteq> y" "perm_swaps ys = perm_swaps ((a, z) # xs)"
      by blast
    have "swaps_set ((x, y) # ys) \<subseteq> swaps_set ((a, b) # (c, d) # xs)"
      using 2(1-5) ys(2) unfolding swaps_set_def case_prod_unfold by simp blast?
    thus ?thesis
      using ys 2 by (intro exI[of _ "(x,y) # ys"]) (simp flip: mult.assoc)
  qed
qed

lemma even_perm_welldefined_aux2:
  assumes "perm_swaps xs = id_perm" and "\<forall>(x,y)\<in>set xs. x \<noteq> y"
  shows   "even (length xs)"
  using assms
proof (induction "length xs" arbitrary: xs rule: less_induct)
  case (less xs)
  show ?case
  proof (cases xs)
    case [simp]: (Cons ab xs1)
    obtain a b where [simp]: "ab = (a, b)"
      by (cases ab)
    obtain xs2 where xs2: "length xs1 = length xs2 + 1" "swaps_set xs2 \<subseteq> swaps_set ((a, b) # xs1)"
                          "\<forall>(x,y)\<in>set xs2. x \<noteq> y" "perm_swaps xs2 = perm_swaps ((a,b) # xs1)"
      using even_perm_welldefined_aux1[of a b xs1] less.prems by auto
    with less.prems have "perm_swaps xs2 = id_perm"
      by simp
    hence "even (length xs2)"
      using less.prems xs2 by (intro less) (auto simp: case_prod_unfold)
    thus ?thesis
      using xs2(1) by simp
  qed auto
qed

lemma even_perm_welldefined:
  assumes "perm_swaps xs = perm_swaps ys" and "\<forall>(x,y)\<in>set xs\<union>set ys. x \<noteq> y"
  shows   "even (length xs) \<longleftrightarrow> even (length ys)"
proof -
  from assms have "perm_swaps (xs @ rev ys) = id_perm" and "\<forall>(x,y)\<in>set (xs @ rev ys). x \<noteq> y"
    by simp_all
  hence "even (length (xs @ rev ys))"
    by (rule even_perm_welldefined_aux2)
  thus ?thesis by auto
qed

text \<open>
  We can finally show the \<open>proper\<close> definition of the parity of a permutation: if the permutation
  can be represented as product of an even number of permutations it is even, and if it can be
  represented as a product of an odd number of permutations it is odd, and it is even iff it is
  not odd.
\<close>
theorem even_perm_perm_swaps_iff:
  assumes "\<forall>(x,y)\<in>set xs. x \<noteq> y"
  shows   "even_perm (perm_swaps xs) \<longleftrightarrow> even (length xs)"
proof -
  obtain ys where ys: "swaps_set ys \<subseteq> set_perm (perm_swaps xs)"
                      "(\<forall>(x, y)\<in>set ys. x \<noteq> y)" "perm_swaps ys = perm_swaps xs"
    using ex_perm_swaps[of "perm_swaps xs"] by blast
  have "even (length xs) \<longleftrightarrow> even (length ys)"
    using ys assms by (intro even_perm_welldefined) auto
  also have "\<dots> \<longleftrightarrow> even_perm (perm_swaps xs)"
  proof
    assume "even_perm (perm_swaps xs)"
    moreover have "ys \<in> lists (set_perm (perm_swaps xs) \<times> set_perm (perm_swaps xs))"
      using ys(1) by (auto simp: swaps_set_def)
    ultimately show "even (length ys)"
      using ys unfolding even_perm_def by blast
  next
    assume "even (length ys)"
    show "even_perm (perm_swaps xs)"
      unfolding even_perm_def
    proof (safe, goal_cases)
      case (1 zs)
      with ys have "even (length ys) = even (length zs)"
        by (intro even_perm_welldefined) auto
      with \<open>even (length ys)\<close> show ?case by simp
    qed
  qed
  finally show ?thesis ..
qed

lemma even_perm_altdef:
  "even_perm p \<longleftrightarrow> (\<exists>xs. swaps_set xs \<subseteq> set_perm p \<and> (\<forall>(x, y)\<in>set xs. x \<noteq> y) \<and>
                        perm_swaps xs = p \<and> even (length xs))" (is "_ = ?rhs")
proof
  assume "even_perm p"
  with ex_perm_swaps[of p] show ?rhs
    by (auto simp: even_perm_def)
next
  assume ?rhs
  thus "even_perm p"
    by (auto simp: even_perm_perm_swaps_iff)
qed

theorem even_perm_times:
  "even_perm (p * q) \<longleftrightarrow> even_perm p = even_perm q"
proof -
  obtain xs where xs: "\<forall>(x,y)\<in>set xs. x \<noteq> y" "perm_swaps xs = p"
    using ex_perm_swaps[of p] by blast
  obtain ys where ys: "\<forall>(x,y)\<in>set ys. x \<noteq> y" "perm_swaps ys = q"
    using ex_perm_swaps[of q] by blast
  show ?thesis
    using even_perm_perm_swaps_iff[of "xs @ ys"] even_perm_perm_swaps_iff[of xs]
          even_perm_perm_swaps_iff[of ys] xs ys by auto
qed

corollary even_perm_inverse [simp]: "even_perm (inverse p) \<longleftrightarrow> even_perm p"
  using even_perm_times[of p "inverse p"] by simp



subsection \<open>Cycles\<close>

text \<open>
  A cycle is a permutation \<open>p\<close> that is fully defined by the orbit of one element \<open>x\<close>, i.e. the
  elements that are touched by \<open>p\<close> are of the form $p^n(x)$.
\<close>

subsubsection \<open>Cyclic lists\<close>

text \<open>
  We represent cycles as lists with no repeated elements such that each element of the list is
  mapped to the next one by \<open>p\<close> (and the last one to the first one). To achieve uniqueness, we
  do not allow lists of length 1, since these all represent the identity (just like the empty list).
  Moreover, we take the quotient over all lists that arise from one another through rotation, since
  they all represent the same permutation.

  Permitting the identity as a cycle as well has technical reasons: first of all, if we did not
  allow it, there would be no cycle on types of cardinality 1, which is not possible in HOL since
  all types must be inhabited. Second, we will want to define an operation to compute the orbit
  of a given element, and this will return a cycle. If we did not allow the identity as a cycle,
  we would not be able to return anything for elements that are mapped to themselves by the
  permutation.

  First of all, we define the `equal up to rotation' relation for lists and prove some basic
  properties:
\<close>

definition cycle_rel where
  "cycle_rel xs ys \<longleftrightarrow> distinct xs \<and> length xs \<noteq> 1 \<and> (\<exists>n. rotate n xs = ys)"

lemma cycle_rel_Nil_left_iff [simp]: "cycle_rel [] ys \<longleftrightarrow> ys = []"
  by (auto simp: cycle_rel_def)

lemma cycle_rel_Nil_right_iff [simp]: "cycle_rel xs [] \<longleftrightarrow> xs = []"
  by (auto simp: cycle_rel_def)

lemma cycle_rel_rotate_right [intro]:
  "distinct xs \<Longrightarrow> length xs \<noteq> 1 \<Longrightarrow> cycle_rel xs (rotate n xs)"
  by (auto simp: cycle_rel_def)

lemma cycle_relE:
  assumes "cycle_rel xs ys"
  obtains n where "distinct xs" "xs = [] \<or> n < length xs" "rotate n xs = ys" "length xs \<noteq> 1"
proof -
  from assms obtain n where "distinct xs" "rotate n xs = ys" "length xs \<noteq> 1"
    by (auto simp: cycle_rel_def)
  thus ?thesis
    by (intro that[of "n mod length xs"]; cases "xs = []")
       (auto simp flip: rotate_conv_mod)
qed

lemma cycle_rel_same_iff [simp]: "cycle_rel xs xs \<longleftrightarrow> distinct xs \<and> length xs \<noteq> 1"
  by (auto simp: cycle_rel_def intro!: exI[of _ 0])

lemma cycle_rel_revI:
  assumes "cycle_rel xs ys"
  shows   "cycle_rel (rev xs) (rev ys)"
proof -
  from assms obtain n
    where n: "distinct xs" "length xs \<noteq> 1" "ys = rotate n xs" "xs = [] \<or> n < length xs"
    by (elim cycle_relE) auto
  hence "rev ys = rotate (if n = 0 then 0 else length xs - n) (rev xs)"
    by (auto simp: rotate_rev)
  thus ?thesis unfolding cycle_rel_def using n
    by (auto intro: exI[of _ 0])
qed

lemma cycle_rel_rev_iff [simp]: "cycle_rel (rev xs) (rev ys) \<longleftrightarrow> cycle_rel xs ys"
  using cycle_rel_revI[of xs ys] cycle_rel_revI[of "rev xs" "rev ys"] by auto

lemma cycle_rel_commute: "cycle_rel xs ys \<longleftrightarrow> cycle_rel ys xs"
proof -
  have "cycle_rel ys xs" if "cycle_rel xs ys" for xs ys :: "'a list"
  proof -
    from that obtain n where *: "distinct xs" "ys = rotate n xs" "length xs \<noteq> 1"
      by (auto simp: cycle_rel_def)
  
    have "rotate (length xs - n mod length xs) ys = xs"
    proof (cases "xs = []")
      case False
      hence "length xs > 0"
        by simp
      from * have "rotate (length xs - n mod length xs) ys = rotate (length xs - n mod length xs + n) xs"
        by (simp add: rotate_rotate)
      also have "\<dots> = rotate ((length xs - n mod length xs + n) mod length xs) xs"
        by (rule rotate_conv_mod)
      also have "(length xs - n mod length xs + n) mod length xs =
                 (length xs - n mod length xs + n mod length xs) mod length xs"
        by (rule mod_add_right_eq [symmetric])
      also have "\<dots> = 0"
        using pos_mod_bound[OF \<open>length xs > 0\<close>, of n]
        by (subst nat_minus_add_max) (auto simp: max_def)
      finally show ?thesis by simp
    qed (auto simp: *)
    thus "cycle_rel ys xs"
      using * by (auto simp: cycle_rel_def)
  qed
  from this[of xs ys] this[of ys xs] show ?thesis by blast
qed

lemma cycle_rel_rotate_left [intro]:
  "distinct xs \<Longrightarrow> length xs \<noteq> 1 \<Longrightarrow> cycle_rel (rotate n xs) xs"
  by (subst cycle_rel_commute) auto

lemma cycle_rel_rotate_right_iff [simp]:
  "cycle_rel xs (rotate n xs) \<longleftrightarrow> distinct xs \<and> length xs \<noteq> 1"
  by (auto simp: cycle_rel_def)

lemma cycle_rel_rotate_left_iff [simp]:
  "cycle_rel (rotate n xs) xs \<longleftrightarrow> distinct xs \<and> length xs \<noteq> 1"
  by (subst cycle_rel_commute) auto

lemma cycle_rel_trans: "cycle_rel xs ys \<Longrightarrow> cycle_rel ys zs \<Longrightarrow> cycle_rel xs zs"
  by (auto simp: cycle_rel_def rotate_rotate)

lemma part_equivp_cycle_rel: "part_equivp cycle_rel"
proof (intro part_equivpI reflpI sympI transpI)
  show "\<exists>xs. cycle_rel xs xs"
    by (rule exI[of _ "[]"]) auto
qed (auto simp: cycle_rel_commute intro: cycle_rel_trans)

lemma bij_betw_rotate_distinct:
  assumes "distinct xs" and "length xs > 1"
  shows   "bij_betw (\<lambda>n. rotate n xs) {..<length xs} {ys. cycle_rel xs ys}"
  unfolding bij_betw_def
proof (intro conjI inj_onI)
  from assms show "(\<lambda>n. rotate n xs) ` {..<length xs} = {ys. cycle_rel xs ys}"
    by (auto elim!: cycle_relE)
  show "m = n"
    if "rotate m xs = rotate n xs" "m \<in> {..<length xs}" "n \<in> {..<length xs}" for m n
  proof -
    have "hd (rotate m xs) = hd (rotate n xs)"
      using that by simp
    hence "xs ! m = xs ! n"
      using that by (subst (asm) (1 2) hd_rotate_conv_nth) auto
    with assms that show "m = n"
      by (auto simp: distinct_conv_nth)
  qed
qed

lemma card_cycle_rel:
  assumes "distinct xs" and "length xs > 1"
  shows   "card {ys. cycle_rel xs ys} = length xs"
  using bij_betw_same_card[OF bij_betw_rotate_distinct[OF assms]] by simp

lemma card_cycle_rel':
  assumes "distinct xs"
  shows "card {ys. cycle_rel xs ys} =
           (if xs = [] then 1 else if length xs = 1 then 0 else length xs)"
proof (cases "length xs = 1")
  case True
  hence "{ys. cycle_rel xs ys} = {}"
    by (auto simp: cycle_rel_def)
  thus ?thesis using True by auto
next
  case False
  hence "xs = [] \<or> length xs > 1"
    by (cases xs) auto
  thus ?thesis
    using card_cycle_rel[of xs] assms by (elim disjE) auto
qed


text \<open>
  Next, we define the cyclic `lookuplemm' function:
\<close>
fun cycle_lookup_aux :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "cycle_lookup_aux y [] z = z"
| "cycle_lookup_aux y [x] z = (if z = x then y else z)"
| "cycle_lookup_aux y (x1 # x2 # xs) z =
     (if z = x1 then x2 else cycle_lookup_aux y (x2 # xs) z)"

definition cycle_lookup :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "cycle_lookup xs z = (case xs of [] \<Rightarrow> z | x # xs \<Rightarrow> cycle_lookup_aux x (x # xs) z)"

lemma cycle_lookup_aux_not_in_set [simp]:
  "z \<notin> set xs \<Longrightarrow> cycle_lookup_aux y xs z = z"
  by (induction y xs z rule: cycle_lookup_aux.induct) auto

lemma cycle_lookup_aux_last [simp]:
  "xs \<noteq> [] \<Longrightarrow> distinct xs \<Longrightarrow> z = last xs \<Longrightarrow> cycle_lookup_aux y xs z = y"
  by (induction y xs z rule: cycle_lookup_aux.induct) auto

lemma cycle_lookup_not_in_set [simp]:
  "z \<notin> set xs \<Longrightarrow> cycle_lookup xs z = z"
  by (auto simp: cycle_lookup_def split: list.splits)

lemma cycle_lookup_Nil [simp]: "cycle_lookup [] = id"
  by auto

lemma cycle_lookup_aux_not_last:
  "distinct xs \<Longrightarrow> z = xs ! i \<Longrightarrow> i < length xs - 1
   \<Longrightarrow> cycle_lookup_aux y xs z = xs ! (i+1)"
  by (induction y xs z arbitrary: i rule: cycle_lookup_aux.induct)
     (auto simp: nth_Cons split: nat.splits)

lemma cycle_lookup_nth:
  assumes "z = xs ! i" "i < length xs" "distinct xs"
  shows   "cycle_lookup xs z = xs ! ((i + 1) mod length xs)"
proof (cases "i = length xs - 1")
  case False
  thus ?thesis using cycle_lookup_aux_not_last[of xs z i "hd xs"] assms
    by (auto simp: cycle_lookup_def split: list.splits)
next
  case True
  from assms have [simp]: "xs \<noteq> []"
    by auto
  from True assms have "z = last xs"
    by (subst last_conv_nth) auto
  hence "cycle_lookup_aux (hd xs) xs z = hd xs"
    using assms by (subst cycle_lookup_aux_last) auto
  hence "cycle_lookup xs z = xs ! 0"
    by (auto simp: cycle_lookup_def split: list.splits)
  also have "0 = (i + 1) mod length xs"
    using True by simp
  finally show ?thesis .
qed

lemma cycle_lookup_nth':
  assumes "i < length xs" "distinct xs"
  shows   "cycle_lookup xs (xs ! i) = xs ! ((i + 1) mod length xs)"
  using assms by (subst cycle_lookup_nth[where i = i]) auto

lemma cycle_lookup_singleton [simp]: "length xs = 1 \<Longrightarrow> cycle_lookup xs = id"
  by (cases xs) (auto simp: cycle_lookup_def)

lemma cycle_lookup_same_iff [simp]:
  assumes "distinct xs"
  shows   "cycle_lookup xs x = x \<longleftrightarrow> x \<notin> set xs \<or> length xs = 1"
proof -
  {
    assume *: "length xs \<noteq> 1" "x \<in> set xs"
    hence [simp]: "xs \<noteq> []"
      by auto
    from * obtain i where i: "i < length xs" "x = xs ! i"
      by (auto simp: set_conv_nth)
    hence "cycle_lookup xs (xs ! i) = xs ! ((i+1) mod length xs)"
      by (intro cycle_lookup_nth' assms)
    also have "(i+1) mod length xs \<noteq> i"
        using \<open>length xs \<noteq> 1\<close> i by (cases "Suc i = length xs") auto
    hence "xs ! ((i+1) mod length xs) \<noteq> xs ! i"
      using assms i * by (auto simp: distinct_conv_nth)
    finally have "cycle_lookup xs x \<noteq> x"
      using i by simp
  }
  thus ?thesis
    using assms by auto
qed

lemma funpow_cycle_lookup_nth:
  assumes "distinct xs" "i < length xs"
  shows   "(cycle_lookup xs ^^ n) (xs ! i) = xs ! ((i + n) mod length xs)"
  using assms(2)
proof (induction n arbitrary: i) 
  case (Suc n)
  from Suc.prems have [simp]: "xs \<noteq> []"
    by auto
  have "(cycle_lookup xs ^^ Suc n) (xs ! i) = (cycle_lookup xs ^^ n) (cycle_lookup xs (xs ! i))"
    by (subst funpow_Suc_right) auto
  also have "cycle_lookup xs (xs ! i) = xs ! ((i+1) mod length xs)"
    using Suc.prems \<open>distinct xs\<close> by (intro cycle_lookup_nth') auto
  also have "(cycle_lookup xs ^^ n) \<dots> = xs ! ((((i+1) mod length xs)+n) mod length xs)"
    using Suc.prems by (intro Suc.IH mod_less_divisor) auto
  also have *: "n mod length xs = Suc (length xs - Suc 0 + n) mod length xs"
    using Suc.prems by simp
  have "(((i+1) mod length xs)+n) mod length xs = (i + Suc n) mod length xs"
    using Suc.prems by (cases "i = length xs - 1") (auto simp: Suc_diff_Suc *)
  finally show ?case .
qed auto    

lemma funpow_cycle_lookup_nth_not_in [simp]: "x \<notin> set xs \<Longrightarrow> (cycle_lookup xs ^^ n) x = x"
  by (induction n) auto

lemma cycle_lookup_rotate [simp]:
  assumes "distinct xs"
  shows   "cycle_lookup (rotate n xs) = cycle_lookup xs"
proof
  fix z
  show "cycle_lookup (rotate n xs) z = cycle_lookup xs z"
  proof (cases "xs = []")
    case False
    have *: "cycle_lookup (rotate n xs) z = cycle_lookup xs z" if "n < length xs" for n
    proof (cases "z \<in> set xs")
      case True
      then obtain i where i: "i < length xs" "z = xs ! i"
        by (auto simp: set_conv_nth)
      have "xs \<noteq> []"
        using i by auto
      define j where "j = (if n \<le> i then i - n else length xs + i - n)"
      have "j < length xs"
        using i by (auto simp: j_def)
      moreover have "(j + n) mod length xs = i"
        using i \<open>n < length xs\<close> by (auto simp: j_def)
      ultimately have "cycle_lookup (rotate n xs) (xs ! i) =
                         rotate n xs ! ((j + 1) mod length (rotate n xs))"
        using assms i \<open>xs \<noteq> []\<close>
        by (intro cycle_lookup_nth, subst rotate_nth) (auto simp: rotate_nth)
      also have "\<dots> = xs ! ((Suc j mod length xs + n) mod length xs)"
        using \<open>xs \<noteq> []\<close> by (subst rotate_nth) (auto intro: pos_mod_bound)
      also have "((Suc j mod length xs + n) mod length xs) = (Suc j + n) mod length xs"
        by (subst mod_add_left_eq) auto
      also have "\<dots> = (i+1) mod length xs"
      proof (cases "n \<le> i")
        case False
        hence "(Suc j + n) mod length xs = (length xs + (i + 1)) mod length xs"
          using \<open>n < length xs\<close> by (simp add: j_def)
        also have "\<dots> = (i+1) mod length xs"
          by (subst mod_add_self1) auto
        finally show ?thesis .
      qed (auto simp: j_def)
      also have "xs ! ((i+1) mod length xs) = cycle_lookup xs (xs ! i)"
        using i assms by (intro cycle_lookup_nth [symmetric]) auto
      finally show ?thesis
        using i by simp
    qed auto
  
    have "cycle_lookup (rotate (n mod length xs) xs) z = cycle_lookup xs z"
      using False by (intro *) auto
    also have "rotate (n mod length xs) xs = rotate n xs"
      by (metis rotate_conv_mod)
    finally show ?thesis .
  qed auto
qed

lemma cycle_lookup_rev:
  assumes "distinct xs"
  shows   "cycle_lookup (rev xs) (cycle_lookup xs x) = x"
proof (cases "x \<in> set xs")
  case True
  from True have [simp]: "xs \<noteq> []"
    by auto
  from True obtain i where i: "i < length xs" "x = xs ! i"
    by (auto simp: set_conv_nth)
  have "cycle_lookup xs x = xs ! (Suc i mod length xs)"
    using i assms by (auto simp: cycle_lookup_nth')
  also have "(Suc i mod length xs) = (if Suc i = length xs then 0 else Suc i)"
    using i by auto
  also have "xs ! \<dots> = rev xs ! (if Suc i = length xs then length xs - 1 else length xs - 1 - Suc i)"
    using i by (subst rev_nth) auto
  also have "cycle_lookup (rev xs) \<dots> =
               xs ! (if Suc i = length xs then length xs - 1
                     else length xs - Suc (Suc (length xs - Suc (Suc i))))"
    using assms i by (subst cycle_lookup_nth') (auto simp: rev_nth)
  also have "(if Suc i = length xs then length xs - 1
              else length xs - Suc (Suc (length xs - Suc (Suc i)))) = i"
    using i by auto
  finally show ?thesis using i by simp
qed auto

lemma cycle_lookup_rev':
  assumes "distinct xs"
  shows   "cycle_lookup xs (cycle_lookup (rev xs) x) = x"
  using assms cycle_lookup_rev[of "rev xs"] by simp
  
  lemma cycle_lookup_hd [simp]: "cycle_lookup (x # y # xs) x = y"
  by (simp add: cycle_lookup_def)

lemma cycle_lookup_Cons:
  assumes "distinct (x # xs)"
  shows   "cycle_lookup (x # xs) = cycle_lookup (xs @ [x])"
proof -
  have "cycle_lookup (x # xs) = cycle_lookup (rotate 1 (x # xs))"
    using assms by (intro cycle_lookup_rotate [symmetric]) auto
  thus ?thesis by simp
qed

lemma cycle_lookup_last [simp]:
  assumes "last xs = z" and "xs \<noteq> []" and "z \<notin> set (butlast xs)"
  shows   "cycle_lookup xs z = hd xs"
proof -
  have "cycle_lookup_aux a xs z = a" for a
    using assms by (induction a xs z rule: cycle_lookup_aux.induct) auto
  thus ?thesis
    using assms by (auto simp: cycle_lookup_def split: list.splits)
qed

lemma cycle_lookup_last' [simp]:
  assumes "last xs = z" and "xs \<noteq> []" and "distinct xs"
  shows   "cycle_lookup xs z = hd xs"
  unfolding cycle_lookup_def using assms by (auto split: list.splits)


lemma cycle_lookup_Cons' [simp]:
  "z \<in> set xs \<Longrightarrow> distinct (x # xs) \<Longrightarrow> z \<noteq> last (x # xs) \<Longrightarrow>
   cycle_lookup (x # xs) z = cycle_lookup (xs @ [x]) z"
  by (subst cycle_lookup_Cons) auto

lemma cycle_lookup_doubleton [simp]:
  "x \<noteq> y \<Longrightarrow> cycle_lookup [x, y] = Fun.swap x y id"
  by (auto simp: Fun.swap_def)

lemma cycle_lookup_Cons_Cons:
  assumes "distinct (x # y # xs)"
  shows   "cycle_lookup (x # y # xs) = Fun.swap x y id \<circ> cycle_lookup (y # xs)"
proof
  fix z
  consider "z = x" | "z = y" | "z \<noteq> x" "z \<noteq> y"
    by auto
  show "cycle_lookup (x # y # xs) z = (Fun.swap x y id \<circ> cycle_lookup (y # xs)) z"
  proof (cases "xs = []")
    case False
    have "z = x \<or> z = y \<or> z \<notin> set (x # y # xs) \<or> z \<in> set xs"
      by auto
    thus ?thesis
    proof (elim disjE)
      assume "z = x"
      thus ?thesis
        using assms by (auto simp: Fun.swap_def)
    next
      assume "z = y"
      thus ?thesis using False assms
        by (cases xs) (auto simp: Fun.swap_def cycle_lookup_Cons)
    next
      assume "z \<notin> set (x # y # xs)"
      thus ?thesis by simp
    next
      assume "z \<in> set xs"
      then obtain i where i: "z = xs ! i" "i < length xs"
        by (auto simp: set_conv_nth)
      show ?thesis
      proof (cases "i = length xs - 1")
        case True
        hence "z = last xs"
          using \<open>xs \<noteq> []\<close> i by (simp add: last_conv_nth)
        thus ?thesis using assms i \<open>z \<in> set xs\<close> unfolding o_def
          by (subst (1 2) cycle_lookup_last') auto
      next
        case False
        have "cycle_lookup (y # xs) z = xs ! Suc i"
          using i assms False by (subst cycle_lookup_nth[where i = "i + 1"]) auto
        moreover have "cycle_lookup (x # y # xs) z = xs ! Suc i"
          using i assms False by (subst cycle_lookup_nth[where i = "i + 2"]) auto
        ultimately show ?thesis
          using \<open>z \<in> set xs\<close> assms i False by (auto simp: Fun.swap_def)
      qed
    qed
  qed (use assms in auto)
qed

lemma cycle_lookup_cong: "cycle_rel xs ys \<Longrightarrow> x = y \<Longrightarrow> cycle_lookup xs x = cycle_lookup ys y"
  by (auto simp: cycle_rel_def)

lemma funpow_cycle_lookup_cong:
  assumes "m mod length xs = n mod length xs" "cycle_rel xs ys" "x = y"
  shows   "(cycle_lookup xs ^^ m) x = (cycle_lookup ys ^^ n) y"
proof (cases "x \<in> set xs")
  case True
  have *: "cycle_lookup xs = cycle_lookup ys"
    by (intro cycle_lookup_cong ext assms refl)
  from True obtain i where i: "i < length xs" "x = xs ! i"
    by (auto simp: set_conv_nth)
  have "(cycle_lookup xs ^^ m) (xs ! i) = xs ! ((i + m) mod length xs)"
    using i assms by (intro funpow_cycle_lookup_nth) (auto simp: cycle_rel_def)
  also have "(i + (m mod length xs)) mod length xs = (i + (n mod length xs)) mod length xs"
    by (subst assms) auto
  hence "(i + m) mod length xs = (i + n) mod length xs"
    by (simp add: mod_add_right_eq)
  also have "xs ! ((i + n) mod length xs) = (cycle_lookup xs ^^ n) (xs ! i)"
    using i assms by (intro funpow_cycle_lookup_nth [symmetric]) (auto simp: cycle_rel_def)
  finally show ?thesis using i assms * by simp
qed (use assms in \<open>auto simp: cycle_rel_def\<close>)

lemma
  assumes "distinct xs"
  shows   bij_cycle_lookup [intro]: "bij (cycle_lookup xs)"
    and   bij_betw_cycle_lookup [intro]: "bij_betw (cycle_lookup xs) (set xs) (set xs)"
proof -
  show "bij_betw (cycle_lookup xs) (set xs) (set xs)"
  proof (cases "xs = []")
    case False
    show ?thesis
    proof (rule bij_betw_byWitness[where f' = "cycle_lookup (rev xs)"])
      from assms False show "cycle_lookup xs ` set xs \<subseteq> set xs"
        by (auto simp: set_conv_nth cycle_lookup_nth')
      from assms have "cycle_lookup (rev xs) ` set (rev xs) \<subseteq> set (rev xs)"
        unfolding set_conv_nth using False by (auto simp: cycle_lookup_nth')
      thus "cycle_lookup (rev xs) ` set xs \<subseteq> set xs"
        by simp
    qed (use assms in \<open>simp_all add: cycle_lookup_rev cycle_lookup_rev'\<close>)
  qed auto
  moreover {
    have "bij_betw id (-set xs) (-set xs)"
      by simp
    also have "?this \<longleftrightarrow> bij_betw (cycle_lookup xs) (-set xs) (-set xs)"
      by (intro bij_betw_cong) auto
    finally have \<dots> .
  }
  ultimately have "bij_betw (cycle_lookup xs) (set xs \<union> (-set xs)) (set xs \<union> (-set xs))"
    by (intro bij_betw_combine) auto
  also have "set xs \<union> (-set xs) = UNIV"
    by simp
  finally show "bij (cycle_lookup xs)" .
qed


subsubsection \<open>Definition of cycles\<close>

quotient_type 'a cycle = "'a list" / partial: cycle_rel
  by (rule part_equivp_cycle_rel)

lift_definition cycle_of_list :: "'a list \<Rightarrow> 'a cycle" is 
  "\<lambda>xs. if distinct xs \<and> length xs \<noteq> 1 then xs else []"
  by auto

code_datatype cycle_of_list

lift_definition set_cycle :: "'a cycle \<Rightarrow> 'a set" is set
  by (auto simp: cycle_rel_def)

lift_definition apply_cycle :: "'a cycle \<Rightarrow> 'a \<Rightarrow> 'a" is cycle_lookup
  by (auto simp: cycle_rel_def)

lift_definition cycle_perm :: "'a cycle \<Rightarrow> 'a perm" is cycle_lookup
  by (auto simp: cycle_rel_def)

lemma apply_perm_cycle [simp]: "apply_perm (cycle_perm c) = apply_cycle c"
  by transfer auto

lemma set_perm_cycle [simp]: "set_perm (cycle_perm c) = set_cycle c"
  by transfer auto

lemma cycle_perm_not_in_set [simp]: "x \<notin> set_cycle c \<Longrightarrow> cycle_perm c x = x"
  by transfer auto

lemma cycle_perm_same_iff [simp]: "cycle_perm c x = x \<longleftrightarrow> x \<notin> set_cycle c"
  by transfer auto

lemma apply_cycle_not_in_set [simp]: "x \<notin> set_cycle c \<Longrightarrow> apply_cycle c x = x"
  by transfer auto

lemma apply_cycle_same_iff [simp]: "apply_cycle c x = x \<longleftrightarrow> x \<notin> set_cycle c"
  by transfer auto

lemma finite_set_cycle [intro]: "finite (set_cycle c)"
  by transfer auto

lemma apply_cycle_in_set_iff [simp]: "apply_cycle c x \<in> set_cycle c \<longleftrightarrow> x \<in> set_cycle c"
proof (transfer, goal_cases)
  case (1 xs x)
  thus ?case using bij_betw_cycle_lookup[of xs]
    by (auto simp: bij_betw_def)
qed

lemma funpow_cycle_perm_in_set_cycle [simp]:
  "((apply_cycle c ^^ n) x \<in> set_cycle c) = (x \<in> set_cycle c)"
  by (induction n) auto



instantiation cycle :: (type) size
begin

lift_definition size_cycle :: "'a cycle \<Rightarrow> nat" is length
  by (auto simp: cycle_rel_def)

instance ..
end

lemma card_set_cycle [simp]: "card (set_cycle c) = size c"
  by transfer (auto simp: distinct_card)

lemma set_cycle_ex_funpow:
  assumes "x \<in> set_cycle c" and "y \<in> set_cycle c"
  shows "\<exists>n. n < size c \<and> y = (apply_cycle c ^^ n) x"
  using assms
proof (transfer, goal_cases)
  case (1 x xs y)
  then obtain n where n: "n < length xs" "xs ! n = x"
    by (auto simp: set_conv_nth)
  define xs' where "xs' = rotate n xs"
  have "y \<in> set xs'"
    using 1 by (auto simp: xs'_def)
  then obtain i where i: "i < length xs'" "xs' ! i = y"
    by (auto simp: set_conv_nth)
  have "y = (cycle_lookup xs' ^^ i) (xs' ! 0)"
    using 1 i by (subst funpow_cycle_lookup_nth) (auto simp: xs'_def)
  also have "\<dots> = (cycle_lookup xs ^^ i) x"
    using 1 i n unfolding xs'_def by (subst rotate_nth) (auto simp add: rotate_nth)
  finally show ?case using i
    by (auto simp: xs'_def)
qed

lemma size_perm_cycle [simp]: "size (cycle_perm c) = size c"
  by (auto simp: size_cycle_def size_perm_def)

lemma set_cycle_altdef: "set_cycle c = {x. apply_cycle c x \<noteq> x}"
  by transfer auto

lemma funpow_apply_cycle_cong:
  assumes "m mod size c = n mod size c'" "c = c'" "x = x'"
  shows   "(apply_cycle c ^^ m) x = (apply_cycle c' ^^ n) x'"
  using assms(1) unfolding assms(2,3)[symmetric]
  by (transfer, intro funpow_cycle_lookup_cong) auto

lemma funpow_apply_cycle_eq_id [simp]:
  assumes "size c dvd n"
  shows   "(apply_cycle c ^^ n) = id"
proof
  fix x :: 'a
  have "(apply_cycle c ^^ n) x = (apply_cycle c ^^ 0) x"
    using assms by (intro funpow_apply_cycle_cong) auto
  thus "(apply_cycle c ^^ n) x = id x"
    by simp
qed

lemma cycle_eqI:
  assumes "apply_cycle c1 = apply_cycle c2"
  shows   "c1 = c2"
proof -
  have set_eq: "set_cycle c1 = set_cycle c2"
    unfolding set_cycle_altdef assms ..
  moreover have "size c1 = size c2"
    unfolding card_set_cycle [symmetric] set_eq ..
  ultimately show ?thesis using assms
proof (transfer, goal_cases)
  case (1 xs ys)
  show ?case
  proof (cases "xs = []")
    case [simp]: False
    with 1 have "ys \<noteq> []" by auto
    hence "hd xs \<in> set xs" by auto
    also have "set xs = set ys" by fact
    finally obtain n where n: "n < length ys" "ys ! n = hd xs"
      by (auto simp: set_conv_nth)

    define ys' where "ys' = rotate n ys"
    have [simp]: "length ys' = length xs" "ys' \<noteq> []" and "distinct ys'"
      using 1 by (auto simp add: ys'_def)
    have "hd ys' = hd xs"
      unfolding ys'_def using n by (subst hd_rotate_conv_nth) auto
    have "xs ! i = ys' ! i" if "i < length xs" for i
      using that
    proof (induction i)
      case 0
      thus ?case using \<open>hd ys' = hd xs\<close>
        by (auto simp: hd_conv_nth)
    next
      case (Suc i)
      hence "xs ! Suc i = cycle_lookup xs (xs ! i)"
        using 1 by (subst cycle_lookup_nth') auto
      also have "\<dots> = cycle_lookup ys (ys' ! i)"
        using 1 Suc by simp
      also have "\<dots> = cycle_lookup ys' (ys' ! i)"
        using 1 by (simp add: ys'_def)
      also have "\<dots> = ys' ! Suc i"
        using 1 Suc.prems \<open>distinct ys'\<close> by (subst cycle_lookup_nth') auto
      finally show ?case .
    qed
    moreover have "length xs = length ys'"
      using 1 by (simp add: ys'_def)
    ultimately have "xs = ys'"
      by (intro nth_equalityI) 
    hence "cycle_rel ys xs"
      using 1 by (auto simp: cycle_rel_def ys'_def)
    thus "cycle_rel xs ys"
      by (simp add: cycle_rel_commute)
    qed (use 1 in auto)
  qed
qed 

lemma cycle_eqI_by_orbit:
  assumes "x \<in> set_cycle c1" "x \<in> set_cycle c2"
  assumes "\<And>n. (apply_cycle c1 ^^ n) x = (apply_cycle c2 ^^ n) x"
  shows   "c1 = c2"
proof (intro cycle_eqI ext)
  have *: "apply_cycle c1 z = apply_cycle c2 z"
          if "z \<in> set_cycle c1" "x \<in> set_cycle c1" "x \<in> set_cycle c2"
             "\<forall>n. (apply_cycle c1 ^^ n) x = (apply_cycle c2 ^^ n) x" for c1 c2 z
  proof -
    from that obtain i where i: "z = (apply_cycle c1 ^^ i) x"
      using set_cycle_ex_funpow[of x c1 z] by auto
    have "apply_cycle c1 z = (apply_cycle c1 ^^ Suc i) x"
      using i by simp
    also have "\<dots> = (apply_cycle c2 ^^ Suc i) x"
      using that by blast
    also have "\<dots> = apply_cycle c2 ((apply_cycle c2 ^^ i) x)"
      by simp
    also have "(apply_cycle c2 ^^ i) x = (apply_cycle c1 ^^ i) x"
      using that by force
    also have "\<dots> = z"
      using i by simp
    finally show ?thesis .
  qed

  fix z
  show "apply_cycle c1 z = apply_cycle c2 z"
  proof (cases "z \<in> set_cycle c1 \<union> set_cycle c2")
    case True
    thus ?thesis using *[of z c1 c2] *[of z c2 c1] assms by auto
  qed auto
qed 

lemma cycle_eqI_by_orbit':
  assumes "\<And>x. x \<in> set_cycle c1 \<inter> set_cycle c2 \<Longrightarrow> apply_cycle c1 x = apply_cycle c2 x"
  assumes "x \<in> set_cycle c1 \<inter> set_cycle c2"
  shows   "c1 = c2"
proof (rule cycle_eqI_by_orbit)
  show "x \<in> set_cycle c1" "x \<in> set_cycle c2"
    using assms by blast+
next
  fix n :: nat
  show "(apply_cycle c1 ^^ n) x = (apply_cycle c2 ^^ n) x"
  proof (induction n)
    case (Suc n)
    have "(apply_cycle c2 ^^ n) x \<in> set_cycle c1"
      using assms by (subst Suc [symmetric]) auto
    hence "apply_cycle c1 ((apply_cycle c2 ^^ n) x) = apply_cycle c2 ((apply_cycle c2 ^^ n) x)"
      using assms by auto
    thus ?case using Suc.IH by simp
  qed auto
qed



lift_definition id_cycle :: "'a cycle" is "[]"
  by auto

lemma size_cycle_eq_0_iff [simp]: "size c = 0 \<longleftrightarrow> c = id_cycle"
  by transfer auto

lemma size_cycle_eq_0_iff' [simp]: "0 = size c \<longleftrightarrow> c = id_cycle"
  by transfer auto

lemma size_id_cycle [simp]: "size id_cycle = 0"
  by transfer auto

lemma cycle_perm_id [simp]: "cycle_perm id_cycle = id_perm"
  by transfer auto

lemma set_cycle_empty_iff [simp]: "set_cycle c = {} \<longleftrightarrow> c = id_cycle"
  by transfer auto

lemma set_cycle_id [simp]: "set_cycle id_cycle = {}"
  by transfer auto

lemma cycle_of_list_Nil [simp]: "cycle_of_list [] = id_cycle"
  by transfer auto

lemma cycle_of_list_singleton [simp]: "length xs = 1 \<Longrightarrow> cycle_of_list xs = id_cycle"
  by transfer auto

lemma cycle_of_list_not_distinct [simp]: "\<not>distinct xs \<Longrightarrow> cycle_of_list xs = id_cycle"
  by transfer auto

lemma size_cycle_not_1 [simp]: "size (c :: 'a cycle) \<noteq> 1"
  by transfer (auto simp: size_cycle_def)

lemma size_cycle_not_Suc_0 [simp]: "size (c :: 'a cycle) \<noteq> Suc 0"
  by transfer (auto simp: size_cycle_def)

lemma size_cycle_not_1' [simp]: "1 \<noteq> size (c :: 'a cycle)"
  by transfer (auto simp: size_cycle_def)

lemma size_cycle_not_Suc_0' [simp]: "Suc 0 \<noteq> size (c :: 'a cycle)"
  by transfer (auto simp: size_cycle_def)

lemma apply_cycle_id [simp]: "apply_cycle id_cycle = id"
  by (rule ext, transfer) auto

lemma cycle_of_list_eq_id_iff [simp]:
  "cycle_of_list xs = id_cycle \<longleftrightarrow> \<not>distinct xs \<or> length xs \<le> 1"
  by (transfer fixing: xs, cases xs) auto

lemma id_eq_cycle_of_list_iff [simp]:
  "id_cycle = cycle_of_list xs \<longleftrightarrow> \<not>distinct xs \<or> length xs \<le> 1"
  by (transfer fixing: xs, cases xs) auto

lemma set_cycle_of_list:
  "set_cycle (cycle_of_list xs) = (if distinct xs \<and> length xs \<noteq> 1 then set xs else {})"
  by transfer auto

lemma apply_cycle_of_list [simp]:
  "distinct xs \<Longrightarrow> apply_cycle (cycle_of_list xs) = cycle_lookup xs"
  by transfer auto

lemma size_cycle_of_list [simp]:
  "distinct xs \<Longrightarrow> length xs \<noteq> 1 \<Longrightarrow> size (cycle_of_list xs) = length xs"
  by transfer auto

lemma ex_cycle_of_list: "\<exists>xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs"
  by transfer auto

lemma finite_cycles_subset [intro]:
  assumes "finite A"
  shows   "finite {c. set_cycle c \<subseteq> A}"
proof -
  have *: "\<exists>xs. c = cycle_of_list xs \<and> distinct xs \<and> length xs \<noteq> 1" for c :: "'a cycle"
    by transfer force
  have "{c. set_cycle c \<subseteq> A} \<subseteq> cycle_of_list ` {xs. distinct xs \<and> set xs \<subseteq> A}"
  proof safe
    fix c assume "set_cycle c \<subseteq> A"
    from *[of c] obtain xs where "c = cycle_of_list xs" "distinct xs" "length xs \<noteq> 1"
      by blast
    moreover from this and \<open>set_cycle c \<subseteq> A\<close> have "xs \<in> lists A"
      by (auto simp: set_cycle_of_list)
    ultimately show "c \<in> cycle_of_list ` {xs. distinct xs \<and> set xs \<subseteq> A}" by blast
  qed
  moreover have "finite (cycle_of_list ` {xs. distinct xs \<and> set xs \<subseteq> A})"
    using assms by (intro finite_imageI finite_distinct_lists)
  ultimately show ?thesis
    using finite_subset by blast
qed

lemma finite_cycles_set_eq [intro]: "finite A \<Longrightarrow> finite {c. set_cycle c = A}"
  by (rule finite_subset[OF _ finite_cycles_subset[of A]]) auto

lemma card_lists_cycle_of_list:
  "card {xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs} =
     (if c = id_cycle then 1 else size c)"
proof (cases "c = id_cycle")
  case False
  have "card {xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs} = size c"
    using False
  proof (transfer, goal_cases)
    case (1 xs)
    hence "length xs > 1" by (cases xs) auto
    have "{ys. distinct ys \<and> length ys \<noteq> 1 \<and>
                 cycle_rel xs (if distinct ys \<and> length ys \<noteq> 1 then ys else [])} =
          {ys. cycle_rel xs ys}"
      using 1 by (auto simp: cycle_rel_def)
    also have "card \<dots> = length xs"
      using 1 \<open>length xs > 1\<close> by (subst card_cycle_rel) auto
    finally show ?case by simp
  qed
  thus ?thesis using False by auto
next
  case True
  hence "{xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs} = {[]}"
    by (auto simp: le_Suc_eq)
  with True show ?thesis 
    by simp
qed

lemma card_cycles_set_eq:
  assumes "finite A" and "card A > 1"
  shows   "card {c. set_cycle c = A} = fact (card A - 1)"
proof -
  have "A \<noteq> {}"
    using assms by auto
  have "fact (card A) = card {xs. distinct xs \<and> set xs = A}"
    using card_distinct_lists_set_eq[of A] assms by simp
  also have "{xs. distinct xs \<and> set xs = A} =
        {xs. distinct xs \<and> length xs \<noteq> 1 \<and> set xs = A}"
    using assms by (auto simp: distinct_card)
  also have "{xs. distinct xs \<and> length xs \<noteq> 1 \<and> set xs = A} =
             (\<Union>c\<in>{c. set_cycle c = A}. {xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs})"
    using assms by (auto simp: set_cycle_of_list distinct_card split: if_splits)
  also have "card \<dots> = (\<Sum>c | set_cycle c = A. card {xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs})"
  proof (intro card_UN_disjoint finite_cycles_set_eq assms ballI impI)
    fix c assume "c \<in> {c. set_cycle c = A}"
    hence "{xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs} \<subseteq> {xs. distinct xs \<and> set xs \<subseteq> A}"
      using assms by (auto simp: set_cycle_of_list split: if_splits)
    moreover have "finite \<dots>"
      by (rule finite_distinct_lists[OF \<open>finite A\<close>])
    ultimately show "finite {xs. distinct xs \<and> length xs \<noteq> 1 \<and> c = cycle_of_list xs}"
      using finite_subset by blast
  qed auto
  also have "\<dots> = (\<Sum>c | set_cycle c = A. if c = id_cycle then 1 else size c)"
    by (subst card_lists_cycle_of_list) auto
  also have "\<dots> = (\<Sum>c | set_cycle c = A. card A)"
    using assms by (intro sum.cong) auto
  also have "\<dots> = card {c. set_cycle c = A} * card A" 
    by simp
  also have "fact (card A) = fact (card A - 1) * card A"
    using assms by (subst fact_reduce) auto
  finally show ?thesis
    using assms by (subst (asm) mult_cancel_right) auto
qed


instantiation cycle :: (equal) equal
begin

definition equal_cycle :: "'a cycle \<Rightarrow> 'a cycle \<Rightarrow> bool" where
  "equal_cycle = (=)"

instance by standard (auto simp: equal_cycle_def)
end


instantiation cycle :: (type) inverse
begin

lift_definition inverse_cycle :: "'a cycle \<Rightarrow> 'a cycle" is rev
proof (safe elim!: cycle_relE)
  fix xs :: "'a list" and n :: nat
  assume *: "n < length xs" "distinct xs" "length xs \<noteq> 1"
  have "rotate (length xs - (length xs - n) mod length xs) xs =
        rotate n xs"
    using * by (metis length_rev mod_if rev_rev_ident rotate_rev)
  hence "rotate ((length xs - n) mod length xs) (rev xs) = rev (rotate n xs)"
    using * by (auto simp: rotate_rev)
  thus "cycle_rel (rev xs) (rev (rotate n xs))"
    using * by (auto simp: cycle_rel_def )
qed auto

instance ..
end

lemma apply_cycle_inverse_left [simp]: "apply_cycle (inverse c) (apply_cycle c x) = x"
  by transfer (simp add: cycle_lookup_rev)

lemma apply_cycle_rev_left' [simp]: "apply_cycle (inverse c) \<circ> cycle_perm c = id"
  by (simp add: fun_eq_iff)

lemma apply_cycle_inverse_right [simp]: "apply_cycle c (apply_cycle (inverse c) x) = x"
  by transfer (simp add: cycle_lookup_rev')

lemma apply_cycle_inverse_right' [simp]: "apply_cycle c \<circ> apply_cycle (inverse c) = id"
  by (simp add: fun_eq_iff)

lemma cycle_perm_inverse [simp]: "cycle_perm (inverse c) = inverse (cycle_perm c)"
proof -
  have "cycle_perm (inverse c) * cycle_perm c = 1"
    by (rule perm_eqI) (auto simp: apply_perm_simps)
  thus ?thesis
    by (metis perm.inverse_inverse perm.inverse_unique)
qed

lemma inverse_eq_inverse_cycle_iff [simp]: "inverse (c1 :: 'a cycle) = inverse c2 \<longleftrightarrow> c1 = c2"
  by transfer auto

lemma inverse_eq_id_cycle_iff [simp]: "inverse c = id_cycle \<longleftrightarrow> c = id_cycle"
  by transfer auto

lemma id_cycle_eq_inverse_iff [simp]: "id_cycle = inverse c \<longleftrightarrow> c = id_cycle"
  by transfer auto

lemma inverse_inverse_cycle [simp]: "inverse (inverse c :: 'a cycle) = c"
  by transfer auto

lemma set_inverse_cycle [simp]: "set_cycle (inverse c) = set_cycle c"
  by transfer auto

lemma size_inverse_cycle [simp]: "size (inverse c :: 'a cycle) = size c"
  by transfer auto

lemma cycle_of_list_inverse [simp]:
  "cycle_of_list (rev xs) = inverse (cycle_of_list xs)"
  by transfer auto


context
begin

qualified fun find_index :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index acc x [] = None"
| "find_index acc x (y # ys) = (if x = y then Some acc else find_index (Suc acc) x ys)"

qualified lemma find_index_None: "x \<notin> set xs \<Longrightarrow> find_index acc x xs = None"
  by (induction xs arbitrary: acc) auto

qualified lemma find_index_Some:
  assumes "i < length xs" "distinct xs"
  shows   "find_index acc (xs ! i) xs = Some (acc + i)"
  using assms
  by (induction xs arbitrary: acc i) (auto simp: nth_Cons split: nat.splits)

definition equal_cycle_impl :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "equal_cycle_impl xs ys \<longleftrightarrow> xs = [] \<and> ys = [] \<or> xs \<noteq> [] \<and> ys \<noteq> [] \<and>
     (case find_index 0 (hd xs) ys of
        None \<Rightarrow> False
      | Some i \<Rightarrow> rotate i ys = xs)"

lemma equal_cycle_impl_correct:
  assumes "distinct xs" "distinct ys" "length xs \<noteq> 1" "length ys \<noteq> 1"     
  shows   "equal_cycle_impl xs ys \<longleftrightarrow> cycle_rel xs ys"
proof
  assume "cycle_rel xs ys"
  show "equal_cycle_impl xs ys"
  proof (cases "xs = [] \<and> ys = []")
    case True
    thus ?thesis by (auto simp: equal_cycle_impl_def)
  next
    case False
    from \<open>cycle_rel xs ys\<close> have \<open>cycle_rel ys xs\<close>
      by (simp add: cycle_rel_commute)
    then obtain n where [simp]: "xs = rotate n ys" and "n < length ys"
      using False by (elim cycle_relE) auto
    have "find_index 0 (ys ! n) ys = Some n"
      using assms False \<open>n < length ys\<close> by (subst find_index_Some) auto
    thus ?thesis
      using False \<open>n < length ys\<close>
      by (simp add: equal_cycle_impl_def hd_rotate_conv_nth)
  qed
next
  assume "equal_cycle_impl xs ys"
  hence "cycle_rel ys xs"
    using assms by (auto simp: cycle_rel_def equal_cycle_impl_def split: option.splits)
  thus "cycle_rel xs ys" by (simp add: cycle_rel_commute)
qed

lemma equal_cycle_code [code]:
  "HOL.equal (cycle_of_list xs) (cycle_of_list ys) \<longleftrightarrow>
     (let a = xs = [] \<or> \<not>distinct xs \<or> length xs = 1;
          b = ys = [] \<or> \<not>distinct ys \<or> length ys = 1
      in  a \<and> b \<or> (\<not>a \<and> \<not>b \<and> equal_cycle_impl xs ys))"
  unfolding equal_cycle_def by transfer (auto simp: equal_cycle_impl_correct)

lemma apply_cycle_code [code]:
  "apply_cycle (cycle_of_list xs) x =
     (if length xs \<noteq> 1 \<and> distinct xs then cycle_lookup xs x else x)"
  by transfer auto

lemma cycle_size_code [code]:
  "size (cycle_of_list xs) = (if length xs \<noteq> 1 \<and> distinct xs then length xs else 0)"
  by transfer (auto simp: size_cycle_def)

lemma set_cycle_code [code]:
  "set_cycle (cycle_of_list xs) = (if length xs \<noteq> 1 \<and> distinct xs then set xs else {})"
  by transfer auto

end


subsubsection \<open>Representing cycles as products of transpositions\<close>

definition swaps_of_cycle_list :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "swaps_of_cycle_list xs = zip xs (tl xs)"

lemma length_swaps_of_cycle_list [simp]:
   "length (swaps_of_cycle_list xs) = length xs - 1"
  by (simp add: swaps_of_cycle_list_def)

lemma swaps_of_cycle_list_simps:
  "swaps_of_cycle_list [] = []"
  "swaps_of_cycle_list [x] = []"
  "swaps_of_cycle_list (x # y # xs) = (x, y) # swaps_of_cycle_list (y # xs)"
  by (auto simp: swaps_of_cycle_list_def)

lemma cycle_perm_of_list_Cons_Cons:
  assumes "distinct (x # y # xs)"
  shows   "cycle_perm (cycle_of_list (x # y # xs)) = \<langle>x \<leftrightarrow> y\<rangle> * cycle_perm (cycle_of_list (y # xs))"
  using assms by transfer (simp add: cycle_lookup_Cons_Cons)

lemma swaps_of_cycle_list_elems_neq:
  assumes "distinct xs"
  shows   "(\<forall>(x,y)\<in>set (swaps_of_cycle_list xs). x \<noteq> y)"
  using assms by (induction xs rule: induct_list012) (auto simp: swaps_of_cycle_list_simps)

lemma perm_swaps_of_cycle_list [simp]:
  assumes "distinct xs"
  shows   "perm_swaps (swaps_of_cycle_list xs) = cycle_perm (cycle_of_list xs)"
  using assms
proof (induction xs rule: induct_list012)
  case (3 x y xs)
  have "\<langle>x \<leftrightarrow> y\<rangle> * cycle_perm (cycle_of_list (y # xs)) =
        cycle_perm (cycle_of_list (x # y # xs))"
    using "3.prems" by (subst cycle_perm_of_list_Cons_Cons) auto
  thus ?case using 3
    by (simp add: swaps_of_cycle_list_simps)
qed (auto simp: swaps_of_cycle_list_def)

text \<open>
  In particular, we can now show that a cycle is even iff it is the trivial cycle or
  has odd length.
\<close>
lemma even_perm_cycle_iff: "even_perm (cycle_perm c) \<longleftrightarrow> c = id_cycle \<or> odd (size c)"
proof -
  obtain xs where xs: "distinct xs" "length xs \<noteq> 1" "c = cycle_of_list xs"
    using ex_cycle_of_list by blast
  have "even_perm (cycle_perm c) \<longleftrightarrow> even_perm (perm_swaps (swaps_of_cycle_list xs))"
    using xs by simp
  also have "\<dots> \<longleftrightarrow> xs = [] \<or> even (length xs - 1)"
    using swaps_of_cycle_list_elems_neq[of xs] xs by (subst even_perm_perm_swaps_iff) auto
  also have "\<dots> \<longleftrightarrow> c = id_cycle \<or> odd (size c)"
    using xs by (auto simp: le_Suc_eq)
  finally show ?thesis .
qed

lemma even_perm_cycle_iff' [simp]: "c \<noteq> id_cycle \<Longrightarrow> even_perm (cycle_perm c) \<longleftrightarrow> odd (size c)"
  by (simp add: even_perm_cycle_iff)



subsection \<open>Orbit of an element\<close>

text \<open>
  The orbit of an element is the (unique) cycle on which it lies. We choose a slightly more
  concrete definition here and will show the other one later.
\<close>

definition perm_orbit_impl :: "'a perm \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "perm_orbit_impl p x =
     (let n = (LEAST n. n > 0 \<and> (p ^ n) x = x) in map (\<lambda>n. (p ^ n) x) [0..<n])"

lemma perm_orbit_impl:
  fixes p x
  defines "xs \<equiv> perm_orbit_impl p x"
  shows   "x \<in> set xs \<and> distinct xs \<and> set xs \<subseteq> insert x (set_perm p) \<and>
           (\<forall>x\<in>set xs. cycle_lookup xs x = p x)"
proof (cases "x \<in> set_perm p")
  case False
  hence [simp]: "p x = x"
    by auto
  let ?n = "(LEAST n. n > 0 \<and> (apply_perm p ^^ n) x = x)" 
  have "?n \<le> 1"
    by (rule Least_le) auto
  moreover have "?n > 0 \<and> (apply_perm p ^^ ?n) x = x"
    by (rule LeastI_ex, rule exI[of _ 1]) auto
  ultimately have "?n = 1" by linarith
  hence [simp]: "xs = [x]"
    by (auto simp: perm_orbit_impl_def xs_def apply_perm_simps)
  show ?thesis by auto
next
  case True
  define A where "A = set_perm p"
  have "\<exists>n\<in>{0<..card A}. (apply_perm p ^^ n) x = x \<and> inj_on (\<lambda>n. (apply_perm p ^^ n) x) {..<n}"
    using True by (intro inj_funpow_cycle_exists) (auto simp: A_def)
  then obtain n where n: "n > 0" "n \<le> card A" "(p ^ n) \<langle>$\<rangle> x = x"
                         "inj_on (\<lambda>n. (p ^ n) \<langle>$\<rangle> x) {..<n}"
    by (force simp: apply_perm_simps)

  have n_eq: "n = (LEAST n. n > 0 \<and> (p ^ n) \<langle>$\<rangle> x = x)" (is "n = ?n")
  proof (rule antisym)
    show "n \<ge> ?n"
      by (rule Least_le) (use n in auto)
  next
    have "(p ^ i) \<langle>$\<rangle> x \<noteq> x" if "i > 0" "i < n" for i
      using inj_onD[OF \<open>inj_on _ _\<close>, of 0 i] \<open>n > 0\<close> that by auto
    moreover have "?n > 0 \<and> (p ^ ?n) \<langle>$\<rangle> x = x"
      by (rule LeastI_ex) (use n in auto)
    ultimately have "\<not>(?n < n)"
      by meson
    thus "?n \<ge> n" by simp
  qed
  have xs_eq: "xs = map (\<lambda>n. (p ^ n) \<langle>$\<rangle> x) [0..<n]"
    by (simp add: xs_def perm_orbit_impl_def n_eq)

  have "distinct xs"
    using n by (auto simp: distinct_conv_nth xs_eq inj_on_def)
  moreover have "x \<in> set xs"
    using \<open>n > 0\<close> by (auto simp: xs_eq set_conv_nth intro: exI[of _ 0])
  moreover have "cycle_lookup xs z = p z" if "z \<in> set xs" for z
  proof -
    from that obtain i where i: "i < length xs" "xs ! i = z"
      by (auto simp: set_conv_nth)
    show ?thesis
    proof (cases "i = n - 1")
      case True
      hence "cycle_lookup xs z = hd (map (\<lambda>n. (p ^ n) \<langle>$\<rangle> x) [0..<n])"
        using i \<open>distinct xs\<close> n by (subst cycle_lookup_last') (auto simp: last_conv_nth xs_eq)
      also have "\<dots> = (p ^ n) \<langle>$\<rangle> x"
        using n by (subst hd_map) auto
      also have "n = Suc i"
        using True n by simp
      also have "(p ^ Suc i) \<langle>$\<rangle> x = p z"
        using i by (simp add: xs_eq apply_perm_simps)
      finally show ?thesis .
    next
      case False
      thus ?thesis using \<open>distinct xs\<close> i n
        by (subst cycle_lookup_nth[where i = i]) (auto simp: xs_eq apply_perm_simps)
    qed
  qed
  moreover have "(p ^ i) x \<in> A" for i
    using assms True by (induction i) (auto simp: A_def apply_perm_simps)
  hence "set xs \<subseteq> insert x A"
    by (auto simp: xs_eq)
  ultimately show ?thesis unfolding A_def by blast
qed

lemma perm_orbit_impl_neq_Nil [simp]: "perm_orbit_impl p x \<noteq> []"
  using perm_orbit_impl[of x p] by auto

lift_definition perm_orbit :: "'a perm \<Rightarrow> 'a \<Rightarrow> 'a cycle" is
  "\<lambda>p x. if p \<langle>$\<rangle> x = x then [] else perm_orbit_impl p x"
proof goal_cases
  case (1 p x)
  show ?case
  proof (cases "p x = x")
    case False
    have "length (perm_orbit_impl p x) \<noteq> 1"
    proof
      assume "length (perm_orbit_impl p x) = 1"
      then obtain y where eq: "perm_orbit_impl p x = [y]"
        by (auto simp: length_Suc_conv)
      from perm_orbit_impl[of x p] have "p x = x"
        by (simp add: eq)
      with \<open>p x \<noteq> x\<close> show False by contradiction
    qed
    moreover have "distinct (perm_orbit_impl p x)"
      using perm_orbit_impl[of x p] by simp
    ultimately show ?thesis by auto
  qed auto
qed

lemma apply_cycle_perm_orbit [simp]:
  "z \<in> set_cycle (perm_orbit p x) \<Longrightarrow> apply_cycle (perm_orbit p x) z = p \<langle>$\<rangle> z"
proof (transfer', goal_cases)
  case (1 z p x)
  thus ?case
    using perm_orbit_impl[of x p] by (auto simp: split: if_splits)
qed

lemma apply_perm_in_perm_orbit_iff [simp]:
  "p \<langle>$\<rangle> z \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> z \<in> set_cycle (perm_orbit p x)"
  by (metis apply_cycle_in_set_iff apply_cycle_perm_orbit apply_perm_cycle apply_perm_inverse_eq_iff)

lemma funpow_apply_perm_in_perm_orbit_iff [simp]:
  "(apply_perm p ^^ n) z \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> z \<in> set_cycle (perm_orbit p x)"
  by (induction n) auto

lemma funpow_apply_cycle_perm_orbit [simp]:
  assumes "z \<in> set_cycle (perm_orbit p x)"
  shows   "(apply_cycle (perm_orbit p x) ^^ n) z = (p ^ n) z"
  using assms
proof (induction n arbitrary: z)
  case (Suc n)
  have "(apply_cycle (perm_orbit p x) ^^ Suc n) z =
        (apply_cycle (perm_orbit p x) ^^ n) (apply_cycle (perm_orbit p x) z)"
    by (subst funpow_Suc_right) auto
  also have "apply_cycle (perm_orbit p x) z = p \<langle>$\<rangle> z"
    by (simp add: Suc)
  also have "(apply_cycle (perm_orbit p x) ^^ n) \<dots> = (p ^ n) (p \<langle>$\<rangle> z)"
    using Suc.prems by (intro Suc) auto
  also have "\<dots> = (p ^ Suc n) \<langle>$\<rangle> z"
    by (simp add: apply_perm_sequence power_commutes)
  finally show ?case .
qed auto

lemma start_in_perm_orbit:
  assumes "p \<langle>$\<rangle> x \<noteq> x"
  shows   "x \<in> set_cycle (perm_orbit p x)"
  using assms
proof (transfer, goal_cases)
  case (1 p x)
  thus ?case
    using perm_orbit_impl[of x p] by (auto simp: split: if_splits)
qed

lemma set_perm_orbit_subset: "set_cycle (perm_orbit p x) \<subseteq> set_perm p"
proof (transfer', goal_cases)
  case (1 p x)
  hence "set (perm_orbit_impl p x) \<subseteq> insert x (set_perm p)"
    using perm_orbit_impl[of x p] by (auto simp: split: if_splits)
  thus ?case
    using 1 by (cases "x \<in> set_perm p") auto
qed

lemma perm_orbit_eq_id_cycle_iff [simp]:
   "perm_orbit p x = id_cycle \<longleftrightarrow> p x = x"
  by transfer' auto

lemma id_cycle_eq_perm_orbit_iff [simp]:
   "id_cycle = perm_orbit p x \<longleftrightarrow> p x = x"
  by transfer' auto

lemma perm_orbit_fixpoint [simp]:
  "p \<langle>$\<rangle> x = x \<Longrightarrow> perm_orbit p x = id_cycle"
  by auto

lemma start_in_perm_orbit_iff [simp]:
  "x \<in> set_cycle (perm_orbit p x) \<longleftrightarrow> p \<langle>$\<rangle> x \<noteq> x"
  by (auto simp: start_in_perm_orbit)

lemma perm_orbit_eqI:
  assumes "x \<in> set_cycle c" and "\<And>x. x \<in> set_cycle c \<Longrightarrow> p \<langle>$\<rangle> x = cycle_perm c x"
  shows   "perm_orbit p x = c"
  using assms by (intro cycle_eqI_by_orbit'[of _ _ x]) auto

lemma apply_cycle_perm_orbit' [simp]: "apply_cycle (perm_orbit p x) x = p \<langle>$\<rangle> x"
  by (cases "p \<langle>$\<rangle> x = x") auto

lemma funpow_apply_cycle_perm_orbit' [simp]: "(apply_cycle (perm_orbit p x) ^^ n) x = (p ^ n) \<langle>$\<rangle> x"
proof (cases "p \<langle>$\<rangle> x = x")
  case False
  thus ?thesis by (intro funpow_apply_cycle_perm_orbit) auto
next
  case True
  thus ?thesis by (induction n) (auto simp: apply_perm_simps)
qed

lemma inj_on_funpow_apply_cycle:
  assumes "x \<in> set_cycle c"
  shows   "inj_on (\<lambda>n. (apply_cycle c ^^ n) x) {..<size c}"
  using assms
proof (transfer, goal_cases)
  case (1 x xs)
  then obtain i where i: "i < length xs" "x = xs ! i"
    by (auto simp: set_conv_nth)
  define ys where "ys = rotate i xs"
  from 1 have "cycle_rel xs ys"
    by (auto simp: ys_def)

  have "inj_on (\<lambda>n. (cycle_lookup ys ^^ n) x) {..<length ys}"
  proof
    fix m n assume mn: "m \<in> {..<length ys}" "n \<in> {..<length ys}"
    assume eq: "(cycle_lookup ys ^^ m) x = (cycle_lookup ys ^^ n) x"
    from mn have [simp]: "xs \<noteq> []" by (auto simp: ys_def)
    have "distinct ys"
      using \<open>cycle_rel xs ys\<close> by (auto simp: cycle_rel_def)
    have "ys ! m = (cycle_lookup ys ^^ m) (ys ! 0)"
      using \<open>cycle_rel xs ys\<close> mn by (subst funpow_cycle_lookup_nth) (auto simp: cycle_rel_def)
    also have "\<dots> = (cycle_lookup ys ^^ n) (ys ! 0)"
      using eq i mn by (simp add: ys_def rotate_nth hd_rotate_conv_nth flip: hd_conv_nth)
    also have "\<dots> = ys ! n"
      using \<open>cycle_rel xs ys\<close> mn by (subst funpow_cycle_lookup_nth) (auto simp: cycle_rel_def)
    finally show "m = n"
      using \<open>distinct ys\<close> mn by (auto simp: cycle_rel_def distinct_conv_nth)
  qed
  also have "cycle_lookup ys = cycle_lookup xs"
    using 1 by (simp add: ys_def)
  also have "length ys = length xs"
    by (simp add: ys_def)
  finally show ?case .
qed

lemma funpow_apply_cycle_eq_id_iff:
  assumes "x \<in> set_cycle c"
  shows   "(apply_cycle c ^^ n) x = x \<longleftrightarrow> size c dvd n"
proof
  assume *: "(apply_cycle c ^^ n) x = x"
  from assms have "size c > 0"
    by (intro Nat.gr0I) auto
  have "(apply_cycle c ^^ (n mod size c)) x = (apply_cycle c ^^ n) x"
    by (intro funpow_apply_cycle_cong) auto
  also have "\<dots> = (apply_cycle c ^^ 0) x"
    using * by simp
  finally have "n mod size c = 0"
    by (rule inj_onD[OF inj_on_funpow_apply_cycle[OF assms]])
       (use \<open>size c > 0\<close> in auto)
  thus "size c dvd n"
    by blast
qed auto



subsection \<open>Unique representation of a permutation as a set of disjoint cycles\<close>

definition disjoint_cycles where
  "disjoint_cycles C \<longleftrightarrow> id_cycle \<notin> C \<and> finite C \<and> disjoint_family_on set_cycle C"

definition perm_of_cycles :: "'a cycle set \<Rightarrow> 'a perm" where
  "perm_of_cycles C = Perm
     (\<lambda>x. if disjoint_cycles C \<and> x \<in> (\<Union>c\<in>C. set_cycle c) then
            apply_cycle (THE c. c \<in> C \<and> x \<in> set_cycle c) x
          else x)"

lemma disjoint_cycles_Uniq:
  assumes "disjoint_cycles C"
  shows   "\<exists>\<^sub>\<le>\<^sub>1c. c \<in> C \<and> x \<in> set_cycle c"
  using assms
  by (auto simp: disjoint_cycles_def disjoint_family_on_def intro!: Uniq_I)

lemma disjoint_cycles_subset: "disjoint_cycles C \<Longrightarrow> C' \<subseteq> C \<Longrightarrow> disjoint_cycles C'"
  by (auto simp: disjoint_cycles_def disjoint_family_on_def intro: finite_subset)

lemma disjoint_cycles_UnD [dest]:
  assumes "disjoint_cycles (C \<union> C')"
  shows   "disjoint_cycles C" "disjoint_cycles C'"
  using assms by (rule disjoint_cycles_subset; simp)+

lemma disjoint_cycles_UnD2 [dest]:
  assumes "disjoint_cycles (C \<union> C')" "C \<inter> C' = {}"
  shows   "(\<Union>x\<in>C. set_cycle x) \<inter> (\<Union>x\<in>C'. set_cycle x) = {}"
  using assms unfolding disjoint_cycles_def disjoint_family_on_def by force

lemma disjoint_cycles_UnI [intro]:
  assumes "disjoint_cycles C" "disjoint_cycles C'"
  assumes "(\<Union>c\<in>C. set_cycle c) \<inter> (\<Union>c\<in>C'. set_cycle c) = {}"
  shows   "disjoint_cycles (C \<union> C')"
  using assms by (auto simp: disjoint_cycles_def)

lemma disjoint_cycles_Un_iff:
  "C \<inter> C' = {} \<Longrightarrow> disjoint_cycles (C \<union> C') \<longleftrightarrow>
    disjoint_cycles C \<and> disjoint_cycles C' \<and> (\<Union>c\<in>C. set_cycle c) \<inter> (\<Union>c\<in>C'. set_cycle c) = {}"
  by blast

lemma disjoint_cycles_singleton [simp]: "disjoint_cycles {c} \<longleftrightarrow> c \<noteq> id_cycle"
  by (auto simp: disjoint_cycles_def disjoint_family_on_def)

lemma disjoint_cycles_insert:
  assumes "c \<notin> C"
  shows   "disjoint_cycles (insert c C) \<longleftrightarrow> c \<noteq> id_cycle \<and> 
             disjoint_cycles C \<and> \<Union>(set_cycle ` C) \<inter> set_cycle c = {}"
  using disjoint_cycles_Un_iff[of C "{c}"] assms by auto

lemma disjoint_cycles_inverse [intro]:
  "disjoint_cycles C \<Longrightarrow> disjoint_cycles (inverse ` C)"
  by (auto simp: disjoint_cycles_def disjoint_family_on_def)


context
  fixes ex_c :: "'a cycle set \<Rightarrow> 'a \<Rightarrow> bool" and get_c f
  defines "ex_c \<equiv> (\<lambda>C x. x \<in> (\<Union>c\<in>C. set_cycle c))"
  defines "get_c \<equiv> (\<lambda>C x. THE c. c \<in> C \<and> x \<in> set_cycle c)"
  defines "f \<equiv> (\<lambda>C x. if ex_c C x then apply_cycle (get_c C x) x else x)"
begin

lemma perm_of_cycles_aux1:
  assumes disjoint: "disjoint_cycles C"
  shows "f (inverse ` C) (f C x) = x"
proof (cases "ex_c C x")
  case True
  define c where "c = get_c C x"
  have "\<exists>!c. c \<in> C \<and> x \<in> set_cycle c" using True disjoint_cycles_Uniq[OF disjoint, of x]
    unfolding c_def ex_c_def get_c_def ex1_iff_ex_Uniq by blast
  hence c: "c \<in> C \<and> x \<in> set_cycle c"
    unfolding c_def get_c_def by (rule theI')
  have f_C_eq [simp]: "f C x = apply_cycle c x"
    using True by (auto simp: f_def c_def)

  define c' where "c' = inverse c"
  have c': "c' \<in> inverse ` C \<and> apply_cycle c x \<in> set_cycle c'"
    unfolding c'_def using c by auto
  moreover have "\<exists>\<^sub>\<le>\<^sub>1c'. c' \<in> inverse ` C \<and> apply_cycle c x \<in> set_cycle c'"
    by (intro disjoint_cycles_Uniq disjoint_cycles_inverse disjoint)
  ultimately have *: "\<exists>!c'. c' \<in> inverse ` C \<and> apply_cycle c x \<in> set_cycle c'"
    unfolding ex_c_def by (auto simp: ex1_iff_ex_Uniq)

  hence "f (inverse ` C) (apply_cycle c x) =
           apply_cycle (get_c (inverse ` C) (apply_cycle c x)) (apply_cycle c x)"
    by (auto simp add: f_def ex_c_def)
  also have "get_c (inverse ` C) (apply_cycle c x) = c'"
    using c' * unfolding ex_c_def get_c_def by (intro the1_equality)
  finally show ?thesis by (simp add: c'_def)
next
  case False
  hence not_ex: "\<not>ex_c (inverse ` C) x"
    by (auto simp: ex_c_def)
  show ?thesis using False not_ex
    by (simp add: f_def)
qed

lemma perm_of_cycles_aux2: "disjoint_cycles C \<Longrightarrow> f C (f (inverse ` C) x) = x"
  using perm_of_cycles_aux1[of "inverse ` C" x]
  by (simp add: image_image disjoint_cycles_inverse)

lemma apply_perm_of_cycles:
  "(perm_of_cycles (C :: 'a cycle set)) \<langle>$\<rangle> x =
     (if disjoint_cycles C \<and> x \<in> (\<Union>c\<in>C. set_cycle c) then
        apply_cycle (THE c. c \<in> C \<and> x \<in> set_cycle c) x
      else x)"
  (is "_ = ?rhs x") unfolding perm_of_cycles_def
proof (subst Perm_inverse, safe, goal_cases)
  define g where "g = (\<lambda>C x. if disjoint_cycles C \<and> x \<in> (\<Union>c\<in>C. set_cycle c)
                             then apply_cycle (get_c C x) x else x)"
  have "bij (g C)"
  proof (cases "disjoint_cycles C")
    case True
    have "bij (f C)"
      by (intro bij_betw_byWitness[of _ "f (inverse ` C)"])
         (use perm_of_cycles_aux1[OF True] perm_of_cycles_aux2[OF True] in auto)
    also have "f C = g C"
      using True by (simp add: f_def g_def ex_c_def)
    finally show ?thesis .
  qed (simp_all add: g_def)
  thus "bij ?rhs"
    by (simp add: g_def get_c_def cong: if_cong)

  show "finite {x. ?rhs x \<noteq> x}"
  proof (cases "disjoint_cycles C")
    case True
    hence "{x. ?rhs x \<noteq> x} \<subseteq> (\<Union>c\<in>C. set_cycle c)"
      by auto
    moreover have "finite \<dots>"
      using True by (intro finite_UN_I) (auto simp: disjoint_cycles_def)
    ultimately show ?thesis using finite_subset by blast
  qed simp_all
qed

end

lemma perm_of_cycles_not_in:
  assumes "x \<notin> (\<Union>c\<in>C. set_cycle c)"
  shows   "perm_of_cycles C x = x"
  using assms unfolding apply_perm_of_cycles by auto

lemma perm_of_cycles_in:
  assumes "x \<in> set_cycle c" "disjoint_cycles C" "c \<in> C"
  shows   "(perm_of_cycles C) \<langle>$\<rangle> x = apply_cycle c x"
proof -
  from assms have Uniq: "\<exists>\<^sub>\<le>\<^sub>1 c. c \<in> C \<and> x \<in> set_cycle c"
    by (intro disjoint_cycles_Uniq)
  with assms have "\<exists>! c. c \<in> C \<and> x \<in> set_cycle c"
    by (auto simp: ex1_iff_ex_Uniq)
  moreover from assms Uniq have "(THE c. c \<in> C \<and> x \<in> set_cycle c) = c"
    by (intro the1_equality') auto
  ultimately show ?thesis
    using assms by (auto simp: apply_perm_of_cycles)
qed

lemma perm_of_cycles_code [code]:
  "apply_perm (perm_of_cycles C) = (\<lambda>x.
     (if \<not>disjoint_cycles C then x else
      let C' = Set.filter (\<lambda>c. x \<in> set_cycle c) C
      in  if is_singleton C' then cycle_perm (the_elem C') x else x))" (is "_ = ?rhs")
proof
  fix x
  show "apply_perm (perm_of_cycles C) x = ?rhs x"
  proof -
    consider "\<not>disjoint_cycles C" | "disjoint_cycles C" "x \<notin> (\<Union>c\<in>C. set_cycle c)"
      | "disjoint_cycles C" "x \<in> (\<Union>c\<in>C. set_cycle c)" by blast
    thus ?thesis
    proof cases
      assume disjoint: "disjoint_cycles C" and "x \<in> (\<Union>c\<in>C. set_cycle c)"
      from this(2) obtain c where c: "c \<in> C" "x \<in> set_cycle c"
        by (auto simp: Set.filter_def)
      have "c' = c" if "c' \<in> C" "x \<in> set_cycle c'" for c'
        by (rule Uniq_D[OF disjoint_cycles_Uniq[OF disjoint, of x]])
           (use c that in auto)
      hence "Set.filter (\<lambda>c. x \<in> set_cycle c) C = {c}"
        unfolding Set.filter_def using c by blast
      moreover have "(THE c. c \<in> C \<and> x \<in> set_cycle c) = c"
        using disjoint_cycles_Uniq[OF disjoint, of x] c
        by (intro the1_equality') simp_all
      ultimately show ?thesis
        using disjoint c by (auto simp: apply_perm_of_cycles Set.filter_def)
    next
      assume 1: "disjoint_cycles C" and 2: "x \<notin> (\<Union>c\<in>C. set_cycle c)"
      from 2 have "\<not>is_singleton (Set.filter (\<lambda>c. x \<in> set_cycle c) C)"
        by (auto simp: Set.filter_def is_singleton_conv_Ex1)
      thus ?thesis
        using 1 2 by (simp add: apply_perm_of_cycles)
    qed (simp_all add: apply_perm_of_cycles)
  qed
qed

lemma perm_of_cycles_inverse_left:
  assumes "disjoint_cycles C"
  shows   "perm_of_cycles (inverse ` C) (perm_of_cycles C x) = x"
proof (cases "x \<in> (\<Union>c\<in>C. set_cycle c)")
  case True
  then obtain c where c: "c \<in> C" "x \<in> set_cycle c"
    by auto
  have "perm_of_cycles (inverse ` C) (perm_of_cycles C x) =
        perm_of_cycles (inverse ` C) (cycle_perm c x)"
    using c assms by (subst perm_of_cycles_in[where c = c]) auto
  also have "\<dots> = x"
    using c assms by (subst perm_of_cycles_in[where c = "inverse c"]) auto
  finally show ?thesis .
qed (auto simp: perm_of_cycles_not_in)

lemma perm_of_cycles_inverse_right:
  assumes "disjoint_cycles C"
  shows   "perm_of_cycles C (perm_of_cycles (inverse ` C) x) = x"
  using perm_of_cycles_inverse_left[OF disjoint_cycles_inverse[OF assms]]
  by (simp add: image_image)

lemma perm_of_cycles_union:
  assumes "disjoint_cycles (C \<union> C')" "C \<inter> C' = {}"
  shows   "perm_of_cycles (C \<union> C') = perm_of_cycles C * perm_of_cycles C'"
proof (rule perm_eqI)
  fix x :: 'a
  consider "x \<in> (\<Union>c\<in>C. set_cycle c)" | "x \<in> (\<Union>c\<in>C'. set_cycle c)" | "x \<notin> (\<Union>c\<in>C\<union>C'. set_cycle c)"
    by blast
  thus "perm_of_cycles (C \<union> C') x = (perm_of_cycles C * perm_of_cycles C') x"
  proof cases
    case 1
    from assms 1 obtain c where c: "c \<in> C" "x \<in> set_cycle c"
      by auto
    moreover have "x \<notin> (\<Union>c\<in>C'. set_cycle c)"
      using assms c by (subst (asm) disjoint_cycles_Un_iff) auto
    ultimately show ?thesis
      unfolding apply_perm_times o_def using assms perm_of_cycles_in[of _ c]
      by (subst (1 2) perm_of_cycles_in[of _ c]) (auto simp: perm_of_cycles_not_in)
  next
    case 2
    from assms 2 obtain c where c: "c \<in> C'" "x \<in> set_cycle c"
      by auto
    moreover have "cycle_perm c x \<in> set_cycle c"
      using assms c by auto
    hence "cycle_perm c x \<notin> (\<Union>c\<in>C. set_cycle c)"
      using assms c by (subst (asm) disjoint_cycles_Un_iff; fastforce)
    ultimately show ?thesis
      unfolding apply_perm_times o_def using assms perm_of_cycles_in[of _ c]
      by (subst (1 3) perm_of_cycles_in[of _ c]) (auto simp: perm_of_cycles_not_in)
  next
    case 3
    thus ?thesis by (simp add: perm_of_cycles_not_in apply_perm_simps)
  qed
qed

lemma perm_of_cycles_empty [simp]: "perm_of_cycles {} = id_perm"
  by (auto simp: fun_eq_iff apply_perm_of_cycles intro!: perm_eqI)

lemma perm_of_cycles_singleton [simp]: "perm_of_cycles {c} = cycle_perm c"
proof (rule perm_eqI)
  fix x
  show "perm_of_cycles {c} x = cycle_perm c x"
  proof (cases "x \<in> set_cycle c")
    case True
    hence "c \<noteq> id_cycle"
      by auto
    thus ?thesis
      using perm_of_cycles_in[of x c "{c}"] True
      by (auto simp: disjoint_cycles_def disjoint_family_on_def)
  qed (auto simp: perm_of_cycles_not_in)
qed

lemma perm_of_cycles_insert_left:
  assumes "disjoint_cycles (insert c C)" "c \<notin> C"
  shows   "perm_of_cycles (insert c C) = cycle_perm c * perm_of_cycles C"
  using perm_of_cycles_union[of "{c}" C] assms by auto

lemma perm_of_cycles_insert_right:
  assumes "disjoint_cycles (insert c C)" "c \<notin> C"
  shows   "perm_of_cycles (insert c C) = perm_of_cycles C * cycle_perm c"
  using perm_of_cycles_union[of C "{c}"] assms by auto  

definition cycles_of_perm :: "'a perm \<Rightarrow> 'a cycle set" where
  "cycles_of_perm p = perm_orbit p ` set_perm p"

lemma cycles_of_perm_altdef:
  "cycles_of_perm p = {c. c \<noteq> id_cycle \<and> (\<forall>x\<in>set_cycle c. cycle_perm c x = p x)}"
proof safe
  fix c :: "'a cycle" assume c: "c \<noteq> id_cycle" "\<forall>x\<in>set_cycle c. cycle_perm c x = p x"
  from c(1) have "set_cycle c \<noteq> {}"
    by auto
  then obtain x where x: "x \<in> set_cycle c"
    by blast
  have "perm_orbit p x \<in> cycles_of_perm p"
    using c x unfolding cycles_of_perm_def by (intro imageI in_set_permI) auto
  also have "perm_orbit p x = c"
    using x c by (intro perm_orbit_eqI) auto
  finally show "c \<in> cycles_of_perm p" .
qed (auto simp: cycles_of_perm_def)

lemma set_cycle_of_perm_subset:
  assumes "c \<in> cycles_of_perm p"
  shows   "set_cycle c \<subseteq> set_perm p"
  using assms by (auto simp: cycles_of_perm_altdef intro!: in_set_permI)

lemma finite_cycles_of_perm [intro]: "finite (cycles_of_perm p)"
  unfolding cycles_of_perm_def by (rule finite_imageI) auto

lemma perm_orbit_in_cycles_of_perm [intro]:
  assumes "x \<in> set_perm p"
  shows   "perm_orbit p x \<in> cycles_of_perm p"
  unfolding cycles_of_perm_altdef
proof safe
  assume "perm_orbit p x = id_cycle"
  thus False using assms by auto
qed (use assms in auto)


lemma id_cycle_not_in_cycles_of_perm [simp]: "id_cycle \<notin> cycles_of_perm p"
  by (auto simp: cycles_of_perm_def)

lemma perm_orbit_in_cycles_of_perm_iff [simp]: "perm_orbit p x \<in> cycles_of_perm p \<longleftrightarrow> p x \<noteq> x"
  by auto

lemma union_cycles_of_perm: "(\<Union>c\<in>cycles_of_perm p. set_cycle c) = set_perm p"
  unfolding set_perm_eq
proof (intro equalityI subsetI; clarify)
  fix x assume "p x \<noteq> x"
  hence "x \<in> set_cycle (perm_orbit p x)" "perm_orbit p x \<in> cycles_of_perm p"
    by auto
  thus "x \<in> (\<Union>c\<in>cycles_of_perm p. set_cycle c)"
    by blast
qed (auto simp: cycles_of_perm_altdef)

lemma disjoint_cycles_cycles_of_perms [intro]: "disjoint_cycles (cycles_of_perm p)"
proof -
  have *: "(p ^ n) x = (cycle_perm c ^ n) x"
    if "x \<in> set_cycle c" "\<And>x. x \<in> set_cycle c \<Longrightarrow> cycle_perm c x = p x" for c n x
    using that by (induction n) (auto simp: apply_perm_simps)

  have "disjoint_family_on set_cycle (cycles_of_perm p)"
    unfolding disjoint_family_on_def cycles_of_perm_altdef
  proof safe
    fix c1 c2 x assume c12: "c1 \<noteq> c2" "x \<in> set_cycle c1" "x \<in> set_cycle c2"
      "\<forall>x\<in>set_cycle c1. cycle_perm c1 x = p x" "\<forall>x\<in>set_cycle c2. cycle_perm c2 x = p x"
    hence "c1 = c2"
      by (intro cycle_eqI_by_orbit'[where x = x]) auto
    with \<open>c1 \<noteq> c2\<close> show "x \<in> {}" by contradiction
  qed
  thus ?thesis
    by (auto simp: disjoint_cycles_def)
qed

lemma perm_of_cycles_in_union_set_cycle:
  assumes "disjoint_cycles C" and "x \<in> (\<Union>c\<in>C. set_cycle c)"
  shows   "perm_of_cycles C x \<in> (\<Union>c\<in>C. set_cycle c)"
proof -
  from assms obtain c where c: "c \<in> C" "x \<in> set_cycle c"
    by auto
  from c have "apply_cycle c x \<in> set_cycle c"
    by auto
  also have "apply_cycle c x = perm_of_cycles C x"
    using c assms by (intro perm_of_cycles_in [symmetric]) auto
  also have "set_cycle c \<subseteq> (\<Union>c\<in>C. set_cycle c)"
    using c by blast
  finally show ?thesis .
qed

lemma perm_of_cycles_permutes:
  assumes "disjoint_cycles C"
  shows   "set_perm (perm_of_cycles C) = (\<Union>c\<in>C. set_cycle c)"
proof safe
  fix x assume "x \<in> set_perm (perm_of_cycles C)"
  thus "x \<in> \<Union> (set_cycle ` C)"
    using perm_of_cycles_not_in[of x C] by auto
next
  fix x c assume c: "c \<in> C" "x \<in> set_cycle c"
  hence "(perm_of_cycles C) \<langle>$\<rangle> x = apply_cycle c x"
    by (intro perm_of_cycles_in assms) auto
  also from c have "\<dots> \<noteq> x"
    by auto
  finally show "x \<in> set_perm (perm_of_cycles C)"
    by auto
qed

lemma perm_of_cycles_of_perm [simp]: "perm_of_cycles (cycles_of_perm p) = p"
proof (rule perm_eqI)
  fix x :: 'a
  show "perm_of_cycles (cycles_of_perm p) x = p x"
  proof (cases "x \<in> set_perm p")
    case False
    thus ?thesis
      by (subst perm_of_cycles_not_in; force simp: cycles_of_perm_altdef)
  next
    case True
    define c where "c = perm_orbit p x"
    have "c \<in> cycles_of_perm p" "x \<in> set_cycle c" "cycle_perm c x = p x"
      using True by (auto simp: c_def)
    thus ?thesis 
      by (subst perm_of_cycles_in[of _ c]) auto
  qed
qed

lemma cycles_of_perm_of_cycles [simp]:
  assumes "disjoint_cycles C"
  shows   "cycles_of_perm (perm_of_cycles C) = C"
proof -
  have 1: "c \<in> C"
      if "c \<noteq> id_cycle" "\<And>x. x \<in> set_cycle c \<Longrightarrow> cycle_perm c x = perm_of_cycles C x" for c
  proof -
    from \<open>c \<noteq> id_cycle\<close> have "set_cycle c \<noteq> {}"
      by auto
    then obtain x where x: "x \<in> set_cycle c"
      by blast
    with that have "cycle_perm c x = perm_of_cycles C x"
      by blast
    with x have "perm_of_cycles C x \<noteq> x"
      by auto
    hence "\<exists>c'. c' \<in> C \<and> x \<in> set_cycle c'"
      using perm_of_cycles_not_in[of x C] by auto
    then obtain c' where c': "c' \<in> C" "x \<in> set_cycle c'"
      by blast
    have "\<forall>x\<in>set_cycle c'. cycle_perm c' x = perm_of_cycles C x"
      using perm_of_cycles_in[of _ c' C] assms c' by auto
    with that x c' have "c = c'"
      by (intro cycle_eqI_by_orbit'[where x = x]) auto
    with c' show ?thesis by simp
  qed

  from assms have 2: "id_cycle \<notin> C"
    by (auto simp: disjoint_cycles_def)

  show ?thesis
    using assms perm_of_cycles_in[of _ _ C] 1 2
    by (auto simp: cycles_of_perm_altdef)
qed

lemma even_perm_iff_even_even_cycles:
  "even_perm p \<longleftrightarrow> even (card {c\<in>cycles_of_perm p. even (size c)})"
proof -
  define C where "C = cycles_of_perm p"
  have disj: "disjoint_cycles C" and "finite C"
    by (auto simp add: C_def)
  have "even_perm p \<longleftrightarrow> even_perm (perm_of_cycles C)"
    by (simp add: C_def)
  also have "\<dots> \<longleftrightarrow> even (card {c\<in>C. even (size c)})"
    using \<open>finite C\<close> disj
  proof (induction C rule: finite_induct)
    case (insert c C)
    from insert.prems insert.hyps have [simp]: "c \<noteq> id_cycle"
      by (auto simp: disjoint_cycles_def)
    have "even_perm (perm_of_cycles (insert c C)) = even_perm (cycle_perm c * perm_of_cycles C)"
      using insert by (subst perm_of_cycles_insert_left) auto
    also have "\<dots> \<longleftrightarrow> odd (size c) = even_perm (perm_of_cycles C)" using insert
      by (subst even_perm_times) (simp_all add: even_perm_cycle_iff)
    also have "even_perm (perm_of_cycles C) \<longleftrightarrow> even (card {c\<in>C. even (size c)})"
      using insert.prems by (intro insert.IH) (auto intro: disjoint_cycles_subset)
    also have "odd (size c) = even (card {c\<in>C. even (size c)}) \<longleftrightarrow>
               even (card {c\<in>C. even (size c)} + (if even (size c) then 1 else 0))"
      by auto
    also have "card {c\<in>C. even (size c)} + (if even (size c) then 1 else 0) =
               card ({c\<in>C. even (size c)} \<union> (if even (size c) then {c} else {}))"
      using insert.hyps by (subst card_Un_disjoint) auto
    also have "{c\<in>C. even (size c)} \<union> (if even (size c) then {c} else {}) =
               {c'\<in>insert c C. even (size c')}" by auto
    finally show ?case .
  qed auto
  finally show ?thesis
    by (simp only: C_def)
qed

lemma apply_cycle_cycles_of_perm [simp]:
  assumes "c \<in> cycles_of_perm p" "x \<in> set_cycle c"
  shows   "apply_cycle c x = p \<langle>$\<rangle> x"
  using assms by (metis disjoint_cycles_cycles_of_perms perm_of_cycles_in perm_of_cycles_of_perm)

lemma funpow_apply_cycle_cycles_of_perm [simp]:
  assumes "c \<in> cycles_of_perm p" "x \<in> set_cycle c"
  shows   "(apply_cycle c ^^ n) x = (p ^ n) \<langle>$\<rangle> x"
  using assms perm_orbit_eqI by fastforce
  

lemma card_cycles_of_perm_le: "card (cycles_of_perm p) \<le> card (set_perm p)"
  unfolding cycles_of_perm_def by (rule card_image_le) auto

lemma cycles_of_perm_id_perm [simp]: "cycles_of_perm id_perm = {}"
  by (auto simp: cycles_of_perm_def)

lemma cycles_of_perm_empty_iff [simp]: "cycles_of_perm p = {} \<longleftrightarrow> p = id_perm"
  by (auto simp: cycles_of_perm_def)

lemma cycle_perm_cycle_of_list_doubleton [simp]:
  "cycle_perm (cycle_of_list [a, b]) = \<langle>a \<leftrightarrow> b\<rangle>"
proof (cases "a = b")
  case False
  thus ?thesis
    by (intro perm_eqI) (auto simp: apply_perm_swap_eq)
qed auto

lemma cycles_of_perm_swap [simp]:
  assumes "a \<noteq> b"
  shows   "cycles_of_perm \<langle>a \<leftrightarrow> b\<rangle> = {cycle_of_list [a, b]}"
proof -
  from assms have "cycles_of_perm (perm_of_cycles {cycle_of_list [a, b]}) = {cycle_of_list [a, b]}"
    by (intro cycles_of_perm_of_cycles) auto
  thus ?thesis
    by simp
qed

lemma cycles_of_perm_cycle:
  "cycles_of_perm (cycle_perm c) = (if c = id_cycle then {} else {c})"
proof (cases "c = id_cycle")
  case False
  hence "cycles_of_perm (perm_of_cycles {c}) = {c}"
    by (intro cycles_of_perm_of_cycles) auto
  also have "perm_of_cycles {c} = cycle_perm c"
    by auto
  finally show ?thesis using False by simp
qed auto

lemma cycles_of_perm_cycle' [simp]:
  "c \<noteq> id_cycle \<Longrightarrow> cycles_of_perm (cycle_perm c) = {c}"
  by (subst cycles_of_perm_cycle) auto

text \<open>
  The type of a permutation is the multiset of the sizes of all its cycles. In accordance with
  our convention so far, we do not count fixpoints.
\<close>
definition perm_type :: "'a perm \<Rightarrow> nat multiset" where
  "perm_type p = image_mset size (mset_set (cycles_of_perm p))"

lemma perm_type_id [simp]: "perm_type id_perm = {#}"
  by (simp add: perm_type_def)

lemma perm_type_swap [simp]: "a \<noteq> b \<Longrightarrow> perm_type \<langle>a \<leftrightarrow> b\<rangle> = {#2#}"
  by (simp add: perm_type_def)

lemma perm_type_perm_of_cycles [simp]:
  assumes "disjoint_cycles C"
  shows   "perm_type (perm_of_cycles C) = image_mset size (mset_set C)"
  unfolding perm_type_def using assms by simp

lemma sum_mset_perm_type [simp]: "sum_mset (perm_type p) = size p"
proof -
  have "set_perm p = (\<Union>c\<in>cycles_of_perm p. set_cycle c)"
    by (rule union_cycles_of_perm [symmetric])
  also have "card \<dots> = (\<Sum>c\<in>cycles_of_perm p. size c)"
    using disjoint_cycles_cycles_of_perms[of p]
    by (subst card_UN_disjoint) (auto simp: disjoint_cycles_def disjoint_family_on_def)
  also have "\<dots> = sum_mset (image_mset size (mset_set (cycles_of_perm p)))"
    by (simp add: sum_unfold_sum_mset)
  finally show ?thesis
    by (simp add: perm_type_def)
qed

lemma zero_not_in_perm_type [simp]: "0 \<notin># perm_type p"
  by (auto simp add: perm_type_def finite_cycles_of_perm)

lemma Suc_0_not_in_perm_type [simp]: "Suc 0 \<notin># perm_type p"
  by (auto simp add: perm_type_def finite_cycles_of_perm)

lemma count_0_perm_type [simp]: "count (perm_type p) 0 = 0"
  using zero_not_in_perm_type[of p] by (meson not_in_iff)

lemma count_Suc_0_perm_type [simp]: "count (perm_type p) (Suc 0) = 0"
  using Suc_0_not_in_perm_type[of p] by (meson not_in_iff)


text \<open>
  The following notion of permutation type also counts fixpoints as cycles, but an explicit
  carrier set must be given. The definition only makes sense if \<^prop>\<open>set_perm p \<subseteq> A\<close>.
\<close>
definition perm_type_on :: "'a set \<Rightarrow> 'a perm \<Rightarrow> nat multiset" where
  "perm_type_on A p = perm_type p + replicate_mset (card (A - set_perm p)) 1"

lemma perm_type_on_id [simp]: "perm_type_on A id_perm = replicate_mset (card A) 1"
  by (simp add: perm_type_on_def)

lemma perm_type_on_swap:
  assumes "a \<in> A" "b \<in> A" "a \<noteq> b"
  shows   "perm_type_on A \<langle>a \<leftrightarrow> b\<rangle> = {#2#} + replicate_mset (card A - 2) 1"
  using assms by (simp add: perm_type_on_def card_Diff_subset numeral_2_eq_2)

lemma size_perm_type_on_set_perm [simp]: "perm_type_on (set_perm p) p = perm_type p"
  by (simp add: perm_type_on_def)

lemma size_perm_type_on [simp]:
  assumes "finite A" and "set_perm p \<subseteq> A"
  shows   "sum_mset (perm_type_on A p) = card A"
proof -
  from assms have "card (set_perm p) \<le> card A"
    by (intro card_mono) auto
  thus ?thesis
    using assms by (simp add: perm_type_on_def card_Diff_subset)
qed

lemma zero_not_in_perm_type_on [simp]: "0 \<notin># perm_type_on A p"
  by (auto simp add: perm_type_on_def finite_cycles_of_perm)

lemma count_0_perm_type_on [simp]: "count (perm_type_on A p) 0 = 0"
  using zero_not_in_perm_type_on[of A p] by (meson not_in_iff)

lemma count_perm_type_on_1:
  assumes "finite A"
  shows   "count (perm_type_on A p) 1 = card {x\<in>A. p x = x}"
proof -
  have "count (perm_type_on A p) 1 = card (A - set_perm p)"
    by (simp add: perm_type_on_def)
  also have "A - set_perm p = {x\<in>A. p x = x}"
    by auto
  finally show ?thesis .
qed

lemma count_perm_type_on: "n \<noteq> 1 \<Longrightarrow> count (perm_type_on A p) n = count (perm_type p) n"
  by (simp add: perm_type_on_def)



text \<open>
  The following function returns the number of cycles of a permutation, following the
  standard mathematical convention that a fixpoint counts as a cycle of length 1.
  The carrier set of the permutation must however be given explicitly for this.
\<close>
definition count_cycles_on :: "'a set \<Rightarrow> 'a perm \<Rightarrow> nat" where
  "count_cycles_on A p = size (perm_type_on A p)"



subsection \<open>Order\<close>

definition perm_order :: "'a perm \<Rightarrow> nat" where
  "perm_order p = (LCM c\<in>cycles_of_perm p. size c)"

lemma perm_order_altdef: "perm_order p = Lcm (set_mset (perm_type p))"
  by (simp add: perm_type_def perm_order_def finite_cycles_of_perm)

lemma Lcm_perm_type_on: "Lcm (set_mset (perm_type_on A p)) = perm_order p"
  by (simp add: perm_type_on_def perm_order_altdef)

lemma perm_order_not_0 [simp]: "perm_order p \<noteq> 0"
  by (intro notI) (auto simp: perm_order_def Lcm_0_iff finite_cycles_of_perm)

lemma perm_order_pos [simp, intro]: "perm_order p > 0"
  using perm_order_not_0[of p] by blast

lemma perm_order_id [simp]: "perm_order id_perm = 1"
  by (simp add: perm_order_def)

lemma perm_order_swap [simp]: "a \<noteq> b \<Longrightarrow> perm_order \<langle>a \<leftrightarrow> b\<rangle> = 2"
  by (simp add: perm_order_def)

lemma perm_order_swap': "perm_order \<langle>a \<leftrightarrow> b\<rangle> = (if a = b then 1 else 2)"
  by (simp add: perm_order_def)

lemma perm_order_cycle [simp]: "c \<noteq> id_cycle \<Longrightarrow> perm_order (cycle_perm c) = size c"
  by (simp add: perm_order_def)

lemma power_perm_order [simp]: "p ^ perm_order p = id_perm"
proof (rule perm_eqI)
  fix x
  show "(p ^ perm_order p) \<langle>$\<rangle> x = id_perm \<langle>$\<rangle> x"
  proof (cases "x \<in> set_perm p")
    case False
    hence "(p ^ perm_order p) \<langle>$\<rangle> x = x"
      by (meson apply_perm_eq_idI set_perm_powerD)
    thus ?thesis by auto
  next
    case True
    have "(p ^ perm_order p) \<langle>$\<rangle> x = (apply_cycle (perm_orbit p x) ^^ perm_order p) x"
      by simp
    also have "apply_cycle (perm_orbit p x) ^^ perm_order p = id"
      using True by (intro funpow_apply_cycle_eq_id) (auto simp: perm_order_def)
    finally show ?thesis by simp
  qed
qed

lemma power_perm_order_dvd:
  assumes "perm_order p dvd n"
  shows   "p ^ n = id_perm"
proof -
  from assms obtain k where "n = perm_order p * k"
    by auto
  hence "p ^ n = p ^ (perm_order p * k)"
    by simp
  also have "\<dots> = id_perm"
    by (simp add: power_mult)
  finally show ?thesis .
qed

lemma power_perm_eq_id_imp_perm_order_dvd:
  assumes "p ^ n = id_perm"
  shows   "perm_order p dvd n"
  unfolding perm_order_def
proof (rule Lcm_least, safe)
  fix c assume c: "c \<in> cycles_of_perm p"
  hence "set_cycle c \<noteq> {}"
    by auto
  then obtain x where x: "x \<in> set_cycle c"
    by blast
  from assms have "x = (p ^ n) \<langle>$\<rangle> x"
    by simp
  also have "\<dots> = (apply_cycle c ^^ n) x"
    using x c by simp
  finally show "size c dvd n"
    using funpow_apply_cycle_eq_id_iff[of x c n] x by auto
qed

lemma power_perm_eq_id_iff:
  "p ^ n = id_perm \<longleftrightarrow> perm_order p dvd n"
  using power_perm_eq_id_imp_perm_order_dvd[of p n] power_perm_order_dvd[of p n] by auto


definition cycle_of_fun :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a cycle" where
  "cycle_of_fun f = undefined"

definition insert_cycle_after :: "'a \<Rightarrow> 'a \<Rightarrow> 'a cycle \<Rightarrow> 'a cycle" where
  "insert_cycle_after x y c = (if y \<notin> set_cycle c \<or> x \<in> set_cycle c then c else
     cycle_of_fun (\<lambda>u. if u = y then x else if u = x then apply_cycle c y else apply_cycle c u))"

lemma filter_rotate:
  fixes xs :: "'a list" and n P
  defines "n' \<equiv> length (filter P (take n xs))"
  assumes n: "n < length xs"
  shows "filter P (rotate n xs) = rotate n' (filter P xs)"
proof -
  from n have "rotate n xs = drop n xs @ take n xs"
    by (simp add: rotate_drop_take)
  also have "filter P \<dots> = filter P (drop n xs) @ filter P (take n xs)"
    by simp
  also have "filter P (take n xs) = take n' (filter P xs)"
    unfolding n'_def by (metis append_eq_conv_conj append_take_drop_id filter_append)
  also have "filter P (drop n xs) = drop n' (filter P xs)"
    unfolding n'_def by (metis append_eq_conv_conj append_take_drop_id filter_append)
  also have "drop n' (filter P xs) @ take n' (filter P xs) = rotate n' (filter P xs)"
  proof (cases "n' < length (filter P xs)")
    case True
    thus ?thesis by (simp add: rotate_drop_take)
  next
    case False
    have "n' \<le> length (filter P xs)"
      unfolding n'_def by (simp add: \<open>filter P (take n xs) = take n' (filter P xs)\<close>)
    with False have "n' = length (filter P xs)"
      by simp
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma cycle_rel_filter:
  assumes "cycle_rel xs ys" "length (filter P xs) \<noteq> 1"
  shows   "cycle_rel (filter P xs) (filter P ys)"
proof (cases "xs = []")
  case False
  obtain n where n: "ys = rotate n xs" "n < length xs" "distinct xs" "length xs \<noteq> 1"
    using assms False by (elim cycle_relE) auto
  have "cycle_rel (filter P xs) (rotate (length (filter P (take n xs))) (filter P xs))"
    by (intro cycle_rel_rotate_right assms distinct_filter n)
  also have "rotate (length (filter P (take n xs))) (filter P xs) = filter P ys"
    unfolding n(1) by (intro filter_rotate[symmetric] n)
  finally show "cycle_rel (filter P xs) (filter P ys)" .
qed (use assms in auto)

lemma cycle_rel_imp_same_set: "cycle_rel xs ys \<Longrightarrow> set xs = set ys"
  by (auto simp: cycle_rel_def)

lift_definition delete_cycle :: "'a \<Rightarrow> 'a cycle \<Rightarrow> 'a cycle" is
  "\<lambda>x xs. if card (set xs - {x}) = 1 then [] else filter (\<lambda>y. y \<noteq> x) xs"
proof goal_cases
  case (1 x xs ys)
  have "length (filter (\<lambda>y. y \<noteq> x) xs) = card (set xs - {x})"
  proof -
    have "length (filter (\<lambda>y. y \<noteq> x) xs) = card (set (filter (\<lambda>y. y \<noteq> x) xs))"
      using 1 by (subst distinct_card) (auto simp: cycle_rel_def)
    also have "set (filter (\<lambda>y. y \<noteq> x) xs) = set xs - {x}"
      by auto
    finally show ?thesis .
  qed
  thus ?case using 1
    by (auto intro!: cycle_rel_filter dest: cycle_rel_imp_same_set)
qed

lemma ex_cycle_rel_with_hd:
  assumes "x \<in> set xs" "distinct xs" "length xs \<noteq> 1"
  obtains ys where "cycle_rel xs ys" "hd ys = x"
proof -
  from assms have [simp]: "xs \<noteq> []"
    by auto
  from assms obtain i where i: "i < length xs" "xs ! i = x"
    by (auto simp: set_conv_nth)
  hence "cycle_rel xs (rotate i xs)" "hd (rotate i xs) = x"
    using assms by (auto simp: hd_rotate_conv_nth)
  thus ?thesis by (rule that)
qed
                                      
lemma apply_cycle_delete:
  "apply_cycle (delete_cycle x c) y =
     (if y = x then x else if apply_cycle c y = x then apply_cycle c x else apply_cycle c y)"
proof (transfer, goal_cases)
  case (1 x xs y)
  define xs' where "xs' = filter (\<lambda>z. z \<noteq> x) xs"
  consider "y = x" | "x \<notin> set xs" | "y \<notin> set xs" 
    | "y \<noteq> x" "x \<in> set xs" "y \<in> set xs" "length xs' = 1"
    | "y \<noteq> x" "x \<in> set xs" "y \<in> set xs" "length xs' \<noteq> 1" by blast    
  thus ?case
  proof cases
    assume "x \<notin> set xs"
    hence "filter (\<lambda>y. y \<noteq> x) xs = xs"
      by (subst filter_id_conv) auto
    thus ?thesis using 1 \<open>x \<notin> set xs\<close>
      by (auto simp: distinct_card)
  next
    assume *: "y \<noteq> x" "x \<in> set xs" "y \<in> set xs" "length xs' = 1"
    have "{y} \<subseteq> set xs'"
      using * by (auto simp: length_Suc_conv xs'_def)
    hence "{y} = set xs'"
      using * by (intro card_subset_eq) (auto simp: length_Suc_conv)
    hence "xs' = [y]"
      using * by (cases xs') auto

    have "set xs = insert x (set xs')"
      using * by (auto simp: xs'_def)
    also have "\<dots> = {x, y}"
      by (simp add: \<open>xs' = [y]\<close>)
    finally have "set xs = {x, y}" .

    have "length xs = card (set xs)"
      using 1 by (simp add: distinct_card)
    also have "\<dots> = 2"
      by (subst \<open>set xs = {x, y}\<close>) (use * in auto)
    finally have "length xs = 2" .
    then obtain u v where "xs = [u, v]"
      by (auto simp: length_Suc_conv numeral_2_eq_2)
    have "u = x \<and> v = y \<or> u = y \<and> v = x"
      using \<open>set xs = {x, y}\<close> \<open>y \<noteq> x\<close> unfolding \<open>xs = [u, v]\<close> by fastforce
    hence "xs = [x, y] \<or> xs = [y, x]"
      using \<open>xs = [u, v]\<close> by auto
    thus ?thesis using \<open>y \<noteq> x\<close> by auto
  next
    assume *: "y \<noteq> x" "x \<in> set xs" "y \<in> set xs" "length xs' \<noteq> 1"
    from \<open>y \<in> set xs\<close> obtain ys where ys: "cycle_rel xs ys" "hd ys = y"
      using ex_cycle_rel_with_hd[of y xs] 1 by auto

    define ys' where "ys' = filter (\<lambda>z. z \<noteq> x) ys"
    have [simp]: "ys \<noteq> []" "length ys = length xs" and set_ys: "set ys = set xs" and "distinct ys"
      using ys 1 * by (auto simp: cycle_rel_def)
    have [simp]: "distinct ys'" "x \<notin> set ys'"
      using \<open>distinct ys\<close> by (auto simp: ys'_def)
    from * have "y \<in> set xs'"
      by (auto simp: xs'_def)
    hence "length xs' > 0"
      by (intro Nat.gr0I) auto
    with * have "length xs' > 1" by linarith

    have "card (set ys') = card (set xs')"
      by (simp add: ys'_def xs'_def set_ys)
    hence [simp]: "length ys' = length xs'"
      using * 1 by (subst (asm) (1 2) distinct_card) (auto simp: xs'_def)

    have "set ys = insert x (set ys')"
      using * \<open>set ys = set xs\<close> by (auto simp: ys'_def)
    also have "card \<dots> = Suc (length ys')"
      by (subst card.insert) (auto simp: distinct_card)
    finally have [simp]: "length xs = Suc (length xs')"
      using \<open>distinct ys\<close> by (simp add: distinct_card)
    have [simp]: "ys' \<noteq> []"
      using \<open>length xs' > 1\<close> \<open>length ys' = length xs'\<close>
      by (intro notI) (simp_all del: \<open>length ys' = length xs'\<close>)
    have [simp]: "ys' ! 0 = ys ! 0"
      using ys * by (cases ys) (auto simp: ys'_def)
    have [simp]: "cycle_lookup xs = cycle_lookup ys"
      using ys by (auto simp: cycle_rel_def)
    have "cycle_rel xs' ys'" using ys *
      unfolding xs'_def ys'_def by (intro cycle_rel_filter) auto
    hence [simp]: "cycle_lookup xs' = cycle_lookup ys'"
      by (auto simp: cycle_rel_def)

    have "cycle_lookup ys y = ys ! 1"
      using ys 1 \<open>distinct ys\<close>  by (subst cycle_lookup_nth[of _ _ 0]) (auto simp: hd_conv_nth)
    moreover have "(cycle_lookup ys ^^ 2) (ys ! 0) = ys ! 2"
      using ys 1 \<open>distinct ys\<close> \<open>length xs' > 1\<close>
      by (subst funpow_cycle_lookup_nth) (auto simp: hd_conv_nth numeral_2_eq_2)
    moreover {
      have "cycle_lookup ys' y = ys' ! 1"
        using ys 1 \<open>length xs' > 1\<close>
        by (subst cycle_lookup_nth[of _ _ 0]) (auto simp: hd_conv_nth)
      also have "\<dots> = (if ys ! 1 = x then ys ! 2 else ys ! 1)"
      proof -
        have "length ys \<ge> Suc (Suc (Suc 0))"
          using \<open>length xs' > 1\<close> by simp
        then obtain u v w ys'' where "ys = u # v # w # ys''"
          by (auto simp: Suc_le_length_iff simp del: \<open>length ys = length xs\<close>)
        moreover from this have "u = y"
          using ys * by (cases ys) auto
        ultimately have "ys = y # v # w # ys''"
          by simp
        thus ?thesis using \<open>distinct ys\<close> *
          by (auto simp: ys'_def)
      qed
      finally have "cycle_lookup ys' y = \<dots>" .
    }
    ultimately show ?thesis
      unfolding xs'_def [symmetric] using * 1 ys
      by (auto simp: distinct_card hd_conv_nth numeral_2_eq_2)
  qed auto
qed

lemma cycle_delete_not_in:
  assumes "x \<notin> set_cycle c"
  shows   "delete_cycle x c = c"
  using assms by (intro cycle_eqI) (auto simp: apply_cycle_delete)

lemma cycle_delete_swap:
  assumes "x \<in> set_cycle c" and "size c = 2"
  shows   "delete_cycle x c = id_cycle"
proof -
  obtain xs where xs: "distinct xs" "length xs \<noteq> 1" "c = cycle_of_list xs"
    using ex_cycle_of_list[of c] by blast
  have "size c = length xs"
    using xs by simp
  with assms have "length xs = 2"
    by auto
  then obtain u v where uv: "xs = [u, v]"
    by (auto simp: length_Suc_conv numeral_2_eq_2)
  have "u = x \<or> v = x"
    using xs assms by (auto simp: uv set_cycle_of_list)
  thus ?thesis using xs
    by (auto intro!: cycle_eqI simp: apply_cycle_delete fun_eq_iff uv Fun.swap_def)
qed

lemma set_cycle_delete:
  assumes "x \<in> set_cycle c" "size c \<noteq> 2"
  shows   "set_cycle (delete_cycle x c) = set_cycle c - {x}"
  using assms
proof (transfer, goal_cases)
  case (1 x xs)
  thus ?case
    by (cases "x \<in> set xs") (auto simp: distinct_card card_Diff_subset)
qed

lemma
  assumes "finite A"
  shows   "card {p. set_perm p \<subseteq> A \<and> count_cycles_on A p = k} = stirling (card A) k"
  using assms
proof (induction "card A" k arbitrary: A rule: stirling.induct)
  case (1 A)
  have "{p. set_perm p \<subseteq> A \<and> count_cycles_on A p = 0} = {id_perm}"
    using 1 by (auto simp: count_cycles_on_def)
  thus ?case using 1 by simp
next
  case (2 k A)
  have eq: "{p. set_perm p \<subseteq> A \<and> card {x \<in> A. p \<langle>$\<rangle> x = x} + card (cycles_of_perm p) = Suc k} = {}"
    using 2 finite_cycles_of_perm by (auto simp: card_eq_0_iff)
  show ?case
    unfolding count_cycles_on_def eq using 2 by simp
next
  case (3 n A)
  hence "A \<noteq> {}"
    by auto
  have eq: "{p. set_perm p \<subseteq> A \<and> card {x \<in> A. p \<langle>$\<rangle> x = x} + card (cycles_of_perm p) = 0} = {}"
    using finite_cycles_of_perm \<open>A \<noteq> {}\<close> 3 by (auto simp: card_eq_0_iff)
  thus ?case using 3
    unfolding count_cycles_on_def eq by simp
next
  case (4 n k A)
  from 4 have "A \<noteq> {}" by auto
  then obtain x where "x \<in> A" by auto
  define A' where "A' = A - {x}"
  from \<open>x \<in> A\<close> have A_eq: "A = insert x A'" and "finite A'" and x: "x \<notin> A'"
    using 4 by (auto simp: A'_def)
  have [simp]: "card A' = n"
    using \<open>Suc n = card A\<close> x \<open>finite A'\<close> unfolding A_eq
    by (subst (asm) card.insert) auto
  oops
  


subsection \<open>Parametricity\<close>

lifting_forget perm.lifting

context
  includes lifting_syntax
begin

definition rel_perm :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a perm \<Rightarrow> 'b perm \<Rightarrow> bool)" where
  "rel_perm r p q \<longleftrightarrow> rel_fun r r (apply_perm p) (apply_perm q) \<and> rel_set r (set_perm p) (set_perm q)"

lemma set_perms_parametric [transfer_rule]:
  "rel_fun (rel_perm r) (rel_set r) set_perm set_perm"
  unfolding rel_perm_def by (auto simp: rel_fun_def)

lemma apply_perm_parametric [transfer_rule]:
  "rel_fun (rel_perm r) (rel_fun r r) apply_perm apply_perm"
  by (auto simp: rel_fun_def rel_perm_def)

lemma left_unique_rel_perm [transfer_rule]:
  assumes "left_unique r" 
  shows   "left_unique (rel_perm r)"
  unfolding left_unique_def
proof safe
  fix p p' :: "'a perm" and q :: "'b perm"

  have eq: "p \<langle>$\<rangle> x = p' \<langle>$\<rangle> x" if "rel_perm r p q" "rel_perm r p' q" "x \<in> set_perm p" for p p' x
  proof -
    note [transfer_rule] = that(1,2)
    from that(1,3) obtain x' where [transfer_rule]: "r x x'"
      by (auto simp: rel_perm_def rel_set_def)
    have "r (p \<langle>$\<rangle> x) (q \<langle>$\<rangle> x')" "r (p' \<langle>$\<rangle> x) (q \<langle>$\<rangle> x')"
      by transfer_prover+
    with assms show ?thesis
      by (auto simp: left_unique_def)
  qed
    
  assume transfer [transfer_rule]: "rel_perm r p q" "rel_perm r p' q"
  show "p = p'"
  proof (rule perm_eqI)
    fix x :: 'a
    show "p \<langle>$\<rangle> x = p' \<langle>$\<rangle> x"
    proof (cases "x \<in> set_perm p \<union> set_perm p'")
      case True
      with eq[of p p' x] eq[of p' p x] transfer show ?thesis by auto
    next
      case False
      thus ?thesis 
        by (auto dest!: not_in_set_permD)
    qed
  qed
qed

lemma right_unique_rel_perm [transfer_rule]:
  assumes "right_unique r" 
  shows   "right_unique (rel_perm r)"
  unfolding right_unique_def
proof safe
  fix q q' :: "'b perm" and p :: "'a perm"

  have eq: "q \<langle>$\<rangle> x' = q' \<langle>$\<rangle> x'" if "rel_perm r p q" "rel_perm r p q'" "x' \<in> set_perm q" for q q' x'
  proof -
    note [transfer_rule] = that(1,2)
    from that(1,3) obtain x where [transfer_rule]: "r x x'"
      by (auto simp: rel_perm_def rel_set_def)
    have "r (p \<langle>$\<rangle> x) (q \<langle>$\<rangle> x')" "r (p \<langle>$\<rangle> x) (q' \<langle>$\<rangle> x')"
      by transfer_prover+
    with assms show ?thesis
      by (auto simp: right_unique_def)
  qed
    
  assume transfer [transfer_rule]: "rel_perm r p q" "rel_perm r p q'"
  show "q = q'"
  proof (rule perm_eqI)
    fix x' :: 'b
    show "q \<langle>$\<rangle> x' = q' \<langle>$\<rangle> x'"
    proof (cases "x' \<in> set_perm q \<union> set_perm q'")
      case True
      with eq[of q q'] eq[of q' q] transfer show ?thesis by auto
    next
      case False
      thus ?thesis 
        by (auto dest!: not_in_set_permD)
    qed
  qed
qed

lemma bi_unique_rel_perm [transfer_rule]:
  assumes "bi_unique r"
  shows   "bi_unique (rel_perm r)"
  using left_unique_rel_perm right_unique_rel_perm assms unfolding bi_unique_alt_def by blast

lemma id_perm_parametric [transfer_rule]: "rel_perm r id_perm id_perm"
  by (auto simp: rel_perm_def rel_set_def)

lemma times_perm_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows   "rel_fun (rel_perm r) (rel_fun (rel_perm r) (rel_perm r)) (*) (*)"
proof (safe intro!: rel_funI)
  fix p p' q q'
  assume [transfer_rule]: "rel_perm r p p'" "rel_perm r q q'"
  show "rel_perm r (p * q) (p' * q')"
    unfolding rel_perm_def
  proof
    show "rel_fun r r (apply_perm (p * q)) (apply_perm (p' * q'))"
      unfolding apply_perm_times by transfer_prover
  next
    let ?A = "Set.filter (\<lambda>x. p \<langle>$\<rangle> q \<langle>$\<rangle> x \<noteq> x) (set_perm p \<union> set_perm q)"
    let ?B = "Set.filter (\<lambda>x. p' \<langle>$\<rangle> q' \<langle>$\<rangle> x \<noteq> x) (set_perm p' \<union> set_perm q')"
    have "rel_set r ?A ?B" by transfer_prover
    also have "?A = set_perm (p * q)"
      by (auto simp: Set.filter_def set_perm_eq apply_perm_simps)
    also have "?B = set_perm (p' * q')"
      by (auto simp: Set.filter_def set_perm_eq apply_perm_simps)
    finally show "rel_set r (set_perm (p * q)) (set_perm (p' * q'))" .
  qed
qed

lemma swap_perm_parametric [transfer_rule]:
  "bi_unique r \<Longrightarrow> rel_fun r (rel_fun r (rel_perm r)) swap_perm swap_perm"
  by (auto simp: rel_fun_def rel_perm_def apply_perm_swap_eq Fun.swap_def
                 bi_unique_def set_perm_swap' rel_set_def)

lemma perm_swaps_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "rel_fun (list_all2 (rel_prod r r)) (rel_perm r) perm_swaps perm_swaps"
  unfolding perm_swaps_def by transfer_prover

lemma transfer_Sigma [transfer_rule]:
  "(rel_set r1 ===> (r1 ===> rel_set r2) ===> rel_set (rel_prod r1 r2)) Sigma Sigma"
  unfolding Sigma_def by transfer_prover

lemma even_perm_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "rel_fun (rel_perm r) (=) even_perm even_perm"
  unfolding even_perm_def_parametric by transfer_prover

lemma sgn_perm_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "rel_fun (rel_perm r) (=) sgn_perm sgn_perm"
  unfolding sgn_perm_def by transfer_prover

definition map_perm :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a perm \<Rightarrow> 'b perm" where
  "map_perm f p =
     Perm (\<lambda>x. if x \<in> f ` set_perm p then (f \<circ> apply_perm p \<circ> inv_into (set_perm p) f) x else x)"

definition comap_perm :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b perm \<Rightarrow> 'a perm" where
  "comap_perm A f p =
     Perm (\<lambda>x. if x \<in> A then (inv_into A f \<circ> apply_perm p \<circ> f) x else x)"

(* TODO: missing transfer rules for cycles *)

end


text \<open>
  The following locale is intended to lift permutations along bijections and transfer
  facts accordingly.
\<close>

locale perm_transfer =
  fixes A :: "'a set" and B :: "'b set" and f :: "'a \<Rightarrow> 'b" and f' :: "'b \<Rightarrow> 'a"
  assumes bij_f: "bij_betw f A B" and f'_f [simp]: "\<And>x. x \<in> A \<Longrightarrow> f' (f x) = x"
begin

lemma f_in [simp]: "x \<in> A \<Longrightarrow> f x \<in> B"
  using bij_f by (auto simp: bij_betw_def)

lemma f_f' [simp]: "y \<in> B \<Longrightarrow> f (f' y) = y"
  using bij_f by (auto simp: bij_betw_def)

lemma bij_f': "bij_betw f' B A"
  using bij_f by (auto simp: bij_betw_def inj_on_def image_image)

lemma f'_in [simp]: "y \<in> B \<Longrightarrow> f' y \<in> A"
  using bij_f' by (auto simp: bij_betw_def)

lemma f_eq_iff [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  using bij_f by (auto simp: bij_betw_def inj_on_def)

lemma f'_eq_iff [simp]: "x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> f' x = f' y \<longleftrightarrow> x = y"
  using bij_f' by (auto simp: bij_betw_def inj_on_def)


definition R where "R x y \<longleftrightarrow> x \<in> A \<and> f x = y"

lemma bi_unique_R [transfer_rule]: "bi_unique R"
  by (auto simp: bi_unique_def R_def)

lemma R_I1: "x \<in> A \<Longrightarrow> R x (f x)"
  by (auto simp: R_def)

lemma R_I2: "y \<in> B \<Longrightarrow> R (f' y) y"
  by (auto simp: R_def)

lemma inv_into_f [simp]: "y \<in> B \<Longrightarrow> inv_into A f y = f' y"
  using bij_betw_inv_into_left[OF bij_f, of "f' y"] by auto

lemma inv_into_f' [simp]: "x \<in> A \<Longrightarrow> inv_into B f' x = f x"
  using bij_betw_inv_into_left[OF bij_f', of "f x"] by auto

lemma inv_into_f_strong:
  assumes "A' \<subseteq> A" "y \<in> f ` A'"
  shows   "inv_into A' f y = f' y"
proof -
  have *: "bij_betw f A' (f ` A')"
    by (rule bij_betw_subset[OF bij_f]) (use assms in auto)
  from assms obtain x where x: "x \<in> A'" "f x = y"
    by (auto simp: bij_betw_def)
  have "inv_into A' f (f x) = x"
    using x assms by (subst bij_betw_inv_into_left[OF *]) auto
  also have "x = f' (f x)"
    using x assms by (subst f'_f) auto
  finally show ?thesis using x by simp
qed

lemma inv_into_f'_strong:
  assumes "B' \<subseteq> B" "x \<in> f' ` B'"
  shows   "inv_into B' f' x = f x"
proof -
  have *: "bij_betw f' B' (f' ` B')"
    by (rule bij_betw_subset[OF bij_f']) (use assms in auto)
  from assms obtain y where y: "y \<in> B'" "f' y = x"
    by (auto simp: bij_betw_def)
  have "inv_into B' f' (f' y) = y"
    using y assms by (subst bij_betw_inv_into_left[OF *]) auto
  also have "y = f (f' y)"
    using y assms by (subst f_f') auto
  finally show ?thesis using y by simp
qed

definition lift1 where "lift1 = map_perm f"
definition lift2 where "lift2 p = comap_perm (f' ` set_perm p) f  p"

lemma
  assumes "set_perm p \<subseteq> A"
  shows    perm_apply_lift1: "(lift1 p) \<langle>$\<rangle> y = (if y \<in> B then f (p \<langle>$\<rangle> (f' y)) else y)"
    and    set_lift1: "set_perm (lift1 p) = f ` set_perm p"
    and    set_lift1': "bij_betw f (set_perm p) (set_perm (lift1 p))"
    and    lift1_transfer: "rel_perm R p (lift1 p)"
proof -
  define h where "h = (\<lambda>x. if x \<in> f ` set_perm p then
                             (f \<circ> apply_perm p \<circ> inv_into (set_perm p) f) x else x)"
  define h' where "h' = (\<lambda>x. if x \<in> f ` set_perm p then
                               (f \<circ> apply_perm (inverse p) \<circ> inv_into (set_perm p) f) x else x)"

  have "inj_on f A"
    using bij_f by (simp add: bij_betw_def)
  hence inj_f: "inj_on f (set_perm p)"
    by (rule inj_on_subset) (use assms in auto)
  note [simp] = inj_on_image_mem_iff[OF \<open>inj_on f A\<close>, of _ "set_perm p"]
  have bij: "bij_betw f (set_perm p) (f ` set_perm p)"
    by (intro inj_on_imp_bij_betw inj_f)
  have image_subset: "f ` set_perm p \<subseteq> B"
    using assms bij by (auto simp: bij_betw_def)

  have "bij_betw h (f ` set_perm p \<union> (-f ` set_perm p)) (f ` set_perm p \<union> (-f ` set_perm p))"
  proof (rule bij_betw_combine)
    have *: "bij_betw f ((\<langle>$\<rangle>) p ` set_perm p) (f ` set_perm p)"
      by (subst apply_perm_image) (auto intro: inj_on_imp_bij_betw inj_f)
    have "bij_betw (f \<circ> apply_perm p \<circ> inv_into (set_perm p) f) (f ` set_perm p) (f ` set_perm p)"
      by (rule bij_betw_trans bij_betw_inv_into inj_on_imp_bij_betw inj_f inj_on_apply_perm *)+
    also have "?this \<longleftrightarrow> bij_betw h (f ` set_perm p) (f ` set_perm p)"
      by (intro bij_betw_cong) (auto simp: h_def)
    finally show \<dots> .
  next
    have "bij_betw id (-f ` set_perm p) (-f ` set_perm p)"
      by auto
    also have "?this \<longleftrightarrow> bij_betw h (-f ` set_perm p) (-f ` set_perm p)"
      by (intro bij_betw_cong) (auto simp: h_def)
    finally show \<dots> .
  qed auto
  also have "f ` set_perm p \<union> (-f ` set_perm p) = UNIV"
    by auto
  finally have "bij h" .

  show map_perm_eq: "lift1 p y = (if y \<in> B then f (p (f' y)) else y)" for y
  proof -
    have "(lift1 p) \<langle>$\<rangle> y = h y"
      using \<open>bij h\<close> unfolding map_perm_def lift1_def h_def by (subst Perm_inverse) auto
    also have "\<dots> = (if y \<in> B then f (p (f' y)) else y)"
    proof (cases "y \<in> B - f ` set_perm p")
      case True
      have "f' y \<notin> set_perm p"
      proof
        assume "f' y \<in> set_perm p"
        hence "f (f' y) \<in> f ` set_perm p"
          by (intro imageI)
        thus False using True by auto
      qed
      hence "p (f' y) = f' y"
        by (intro apply_perm_eq_idI) auto
      thus ?thesis using True
        by (simp add: h_def)
    qed (use inj_f assms in \<open>auto simp: h_def\<close>)
    finally show ?thesis .
  qed

  have "set_perm (lift1 p) = {x\<in>B. f (p \<langle>$\<rangle> (f' x)) \<noteq> x}"
    unfolding set_perm_eq map_perm_eq[abs_def] by auto
  also have "B = f ` A"
    using bij_f unfolding bij_betw_def by simp
  also have "{x\<in>f`A. f (p \<langle>$\<rangle> (f' x)) \<noteq> x} = f ` set_perm p"
    using assms by (auto simp: apply_perm_in[OF assms] in_set_perm intro!: imageI)
  finally show set_perm_eq: "set_perm (lift1 p) = f ` set_perm p" .
  from bij_f show "bij_betw f (set_perm p) (set_perm (lift1 p))"
    by (rule bij_betw_subset) (use assms set_perm_eq in simp_all)

  have "rel_set R (set_perm p) (set_perm (lift1 p))"
    unfolding set_perm_eq R_def using assms by (auto simp: rel_set_def)
  moreover have "rel_fun R R (apply_perm p) (apply_perm (lift1 p))"
    unfolding R_def rel_fun_def using map_perm_eq assms by auto
  ultimately show "rel_perm R p (lift1 p)"
    by (simp add: rel_perm_def)
qed

lemma
  assumes "set_perm p \<subseteq> B"
  shows    perm_apply_lift2:
             "(lift2 p) \<langle>$\<rangle> x = (if x \<in> A then f' (p \<langle>$\<rangle> (f x)) else x)"
    and    set_lift2: "set_perm (lift2 p) = f -` set_perm p \<inter> A"
    and    set_lift2': "bij_betw f (set_perm (lift2 p)) (set_perm p)"
    and    lift2_transfer: "rel_perm R (lift2 p) p"
proof -
  define h where "h = (\<lambda>x. if x \<in> f' ` set_perm p then
                        (inv_into (f' ` set_perm p) f \<circ> apply_perm p \<circ> f) x else x)"
  define h' where "h' = (\<lambda>x. if x \<in> f' ` set_perm p then
                          (inv_into (f' ` set_perm p) f \<circ> apply_perm (inverse p) \<circ> f) x else x)"

  have inj: "inj_on f A"
    using bij_f by (simp add: bij_betw_def)

  have "bij_betw h (f' ` set_perm p \<union> -f' ` set_perm p) (f' ` set_perm p \<union> -f' ` set_perm p)"
  proof (rule bij_betw_combine)
    have inj': "inj_on f (f' ` set_perm p)"
      by (rule inj_on_subset[OF inj]) (use assms in auto)
    from assms have *: "(\<lambda>x. f (f' x)) ` set_perm p = id ` set_perm p"
      by (intro image_cong) auto
    have "bij_betw f (f' ` set_perm p) (set_perm p)"
      using bij_f by (rule bij_betw_subset) (use assms * in \<open>auto simp: image_image bij_betw_def\<close>)
    have f_f'_set_perm: "f ` f' ` set_perm p = id ` set_perm p"
      using assms unfolding image_image by (intro image_cong) auto

    have "bij_betw f' (set_perm p) (f' ` set_perm p)"
      by (rule bij_betw_subset[OF bij_f']) (use assms in auto)
    also have "?this \<longleftrightarrow> bij_betw (inv_into (f' ` set_perm p) f) (id ` set_perm p) (f' ` set_perm p)"
      unfolding id_def image_ident 
      by (intro bij_betw_cong, subst inv_into_f_strong) (use f_f'_set_perm assms in auto)
    also have "id ` set_perm p = (apply_perm p ` id ` set_perm p)"
        by (simp add: apply_perm_image)
    also have "id ` set_perm p = f ` f' ` set_perm p"
      using assms unfolding image_image by (intro image_cong) auto
    finally have **: "bij_betw (inv_into (f' ` set_perm p) f)
                        (apply_perm p ` f ` f' ` set_perm p) (f' ` set_perm p)" .
    have "bij_betw (inv_into (f' ` set_perm p) f \<circ> apply_perm p \<circ> f)
            (f' ` set_perm p) (f' ` set_perm p)"
      by (rule bij_betw_trans bij_betw_inv_into inj' inj_on_imp_bij_betw inj_on_apply_perm * **)+
    also have "?this \<longleftrightarrow> bij_betw h (f' ` set_perm p) (f' ` set_perm p)"
      using assms by (intro bij_betw_cong) (auto simp: h_def)
    finally show \<dots> .
  next
    have "bij_betw id (-f' ` set_perm p) (-f' ` set_perm p)"
      by auto
    also have "?this \<longleftrightarrow> bij_betw h (-f' ` set_perm p) (-f' ` set_perm p)"
      by (intro bij_betw_cong) (auto simp: h_def)
    finally show "bij_betw h (- f' ` set_perm p) (- f' ` set_perm p)" .
  qed auto
  also have "f' ` set_perm p \<union> - f' ` set_perm p = UNIV"
    by auto
  finally have "bij h" .

  show apply_eq: "(lift2 p) \<langle>$\<rangle> x = (if x \<in> A then f' (p \<langle>$\<rangle> (f x)) else x)" for x
  proof -
    have "f' ` set_perm p \<subseteq> A"
      using assms by auto
    have "(lift2 p) \<langle>$\<rangle> x = h x"
      unfolding lift2_def comap_perm_def using \<open>bij h\<close> by (subst Perm_inverse) (auto simp: h_def)
    also have "\<dots> = (if x \<in> A then f' (p \<langle>$\<rangle> (f x)) else x)"
    proof (cases "x \<in> A - f' ` set_perm p")
      case True
      have "f x \<notin> set_perm p"
      proof
        assume "f x \<in> set_perm p"
        hence "f' (f x) \<in> f' ` set_perm p"
          by (intro imageI)
        thus False using True by auto
      qed
      hence "p (f x) = f x"
        by (intro apply_perm_eq_idI) auto
      thus ?thesis using True
        by (simp add: h_def)
    next
      case False
      note * = this
      have [simp]: "f' z \<in> A" if "z \<in> set_perm p" for z
        using that assms bij_f' by (auto simp: bij_betw_def)
      show ?thesis
      proof (cases "x \<in> A")
        case True
        with False obtain y where [simp]: "x = f' y" and y: "y \<in> set_perm p"
          by auto
        have [simp]: "f (f' y) = y"
          using assms y by (intro f_f') auto
        have "h x = inv_into (f' ` set_perm p) f (p \<langle>$\<rangle> y)"
          using * y by (simp add: h_def)
        also have "f ` f' ` set_perm p = id ` set_perm p"
          using assms unfolding image_image by (intro image_cong) auto
        hence "inv_into (f' ` set_perm p) f (p \<langle>$\<rangle> y) = f' (p \<langle>$\<rangle> y)"
          using y by (intro inv_into_f_strong) auto
        finally show ?thesis
          using True * assms by simp
      qed (auto simp: h_def)
    qed
    finally show ?thesis .
  qed

  have "set_perm (lift2 p) = {x\<in>A. f' (p \<langle>$\<rangle> (f x)) \<noteq> x}"
    unfolding set_perm_eq apply_eq[abs_def] by auto
  also have "A = f' ` B"
    using bij_f' unfolding bij_betw_def by simp
  also have "{x\<in>f'`B. f' (p \<langle>$\<rangle> (f x)) \<noteq> x} = f' ` set_perm p"
    using assms by (auto simp: apply_perm_in[OF assms] in_set_perm intro!: imageI)
  finally have set_perm_eq: "set_perm (lift2 p) = f' ` set_perm p" .
  from bij_f' have "bij_betw f' (set_perm p) (set_perm (lift2 p))"
    by (rule bij_betw_subset) (use assms set_perm_eq in simp_all)
  hence "bij_betw (inv_into (set_perm p) f') (set_perm (lift2 p)) (set_perm p)"
    by (intro bij_betw_inv_into)
  also have "?this \<longleftrightarrow> bij_betw f (set_perm (lift2 p)) (set_perm p)"
    using assms set_perm_eq by (intro bij_betw_cong inv_into_f'_strong) auto
  finally show \<dots> .
  show "set_perm (lift2 p) = f -` set_perm p \<inter> A"
    using assms by (force simp: set_perm_eq)

  have "rel_set R (set_perm (lift2 p)) (set_perm p)"
    unfolding set_perm_eq R_def using assms by (force simp: rel_set_def)    
  moreover have "rel_fun R R (apply_perm (lift2 p)) (apply_perm p)"
    unfolding R_def rel_fun_def using apply_eq assms by auto
  ultimately show "rel_perm R (lift2 p) p"
    by (simp add: rel_perm_def)
qed

lemma lift2_lift1 [simp]:
  assumes "set_perm p \<subseteq> A"
  shows   "lift2 (lift1 p) = p"
proof (rule perm_eqI)
  fix x show "(lift2 (lift1 p)) \<langle>$\<rangle> x = p \<langle>$\<rangle> x"
  proof (cases "x \<in> A")
    case True
    hence "(lift2 (lift1 p)) \<langle>$\<rangle> x = f' ((lift1 p) \<langle>$\<rangle> f x)"
      using assms by (subst perm_apply_lift2) (auto simp: set_lift1)
    also have "\<dots> = p \<langle>$\<rangle> x"
      using True assms by (subst perm_apply_lift1) auto
    finally show ?thesis .
  next
    case False
    hence "(lift2 (lift1 p)) \<langle>$\<rangle> x = x"
      using assms by (subst perm_apply_lift2) (auto simp: set_lift1)
    moreover from False and assms have "x \<notin> set_perm p"
      by auto
    hence "p \<langle>$\<rangle> x = x"
      by auto
    ultimately show ?thesis by simp
  qed
qed

lemma lift1_lift2 [simp]:
  assumes "set_perm p \<subseteq> B"
  shows   "lift1 (lift2 p) = p"
proof (rule perm_eqI)
  fix x show "(lift1 (lift2 p)) \<langle>$\<rangle> x = p \<langle>$\<rangle> x"
  proof (cases "x \<in> B")
    case True
    hence "(lift1 (lift2 p)) \<langle>$\<rangle> x = f ((lift2 p) \<langle>$\<rangle> f' x)"
      using assms by (subst perm_apply_lift1) (auto simp: set_lift2)
    also have "\<dots> = p \<langle>$\<rangle> x"
      using True assms by (subst perm_apply_lift2) auto
    finally show ?thesis .
  next
    case False
    hence "(lift1 (lift2 p)) \<langle>$\<rangle> x = x"
      using assms by (subst perm_apply_lift1) (auto simp: set_lift2)
    moreover from False and assms have "x \<notin> set_perm p"
      by auto
    hence "p \<langle>$\<rangle> x = x"
      by auto
    ultimately show ?thesis by simp
  qed
qed

end


subsection \<open>Inversions\<close>

text \<open>
  For a permutation on a linearly ordered set, one can define the set of \<^emph>\<open>inversions\<close>.
  An inversion is a pair of elements \<open>x < y\<close> such that \<open>p x > p y\<close>. For convenience, we allow
  to also specify the carrier set because otherwise the set of inversions could potentially
  be infinite.
\<close>

definition inversions_on :: "'a set \<Rightarrow> ('a :: linorder perm) \<Rightarrow> ('a \<times> 'a) set" where
  "inversions_on A p = {(i,j). i \<in> A \<and> j \<in> A \<and> i < j \<and> p \<langle>$\<rangle> i > p \<langle>$\<rangle> j}"

lemma inversions_on_code [code]:
  "inversions_on A p = (SIGMA i:A. Set.filter (\<lambda>j. i < j \<and> p \<langle>$\<rangle> i > p \<langle>$\<rangle> j) A)"
  by (auto simp: inversions_on_def Set.filter_def)

lemma inversions_on_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r" "(rel_fun r (rel_fun r (=))) (<) (<)"
  shows "rel_fun (rel_set r) (rel_fun (rel_perm r) (rel_set (rel_prod r r)))
           inversions_on inversions_on"
  unfolding inversions_on_code by transfer_prover

lemma finite_inversions_on [intro]:
  assumes "finite A"
  shows   "finite (inversions_on A p)"
proof (rule finite_subset)
  show "inversions_on A p \<subseteq> A \<times> A"
    by (auto simp: inversions_on_def)
qed (use assms in auto)

lemma inversions_on_id [simp]: "inversions_on A id_perm = {}"
  by (auto simp: inversions_on_def)

text \<open>
  Considering a permutation on natural numbers such that \<open>p i < p (i+1)\<close>, swapping \<open>i\<close> and \<open>i + 1\<close>
  introduces an additional inversion.
\<close>
lemma inversions_on_nat_swap1:
  assumes "p \<langle>$\<rangle> i < p \<langle>$\<rangle> (Suc i)" "i \<in> A" "Suc i \<in> A" "set_perm p \<subseteq> A"
  defines "swp \<equiv> Fun.swap i (Suc i) id"
  shows "inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>) =
         insert (i, Suc i) (map_prod swp swp ` inversions_on A p)"
proof -
  have [simp]: "swp i = Suc i" "swp (Suc i) = i"
    by (auto simp: swp_def)
  have [simp]: "swp (swp x) = x" for x
    by (simp add: swp_def Fun.swap_def)
  have swp_id: "swp k = k" if "k \<noteq> i" "k \<noteq> Suc i" for k
    using that by (auto simp: swp_def)
  have [simp]: "i = swp x \<longleftrightarrow> x = Suc i" "Suc i = swp x \<longleftrightarrow> x = i" for x
    by (auto simp: swp_def Fun.swap_def)
  have [simp]: "swp x = i \<longleftrightarrow> x = Suc i" "swp x = Suc i \<longleftrightarrow> x = i" for x
    by (auto simp: swp_def Fun.swap_def)
  have [simp]: "swp x = swp y \<longleftrightarrow> x = y" for x y
    by (auto simp: swp_def Fun.swap_def)

  show ?thesis
  proof (intro equalityI subsetI)
    fix x assume "x \<in> inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>)"
    hence "map_prod swp swp x \<in> inversions_on A p \<or> x = (i, Suc i)"
      using \<open>i \<in> A\<close> \<open>Suc i \<in> A\<close>
      by (cases "fst x \<in> {i,Suc i}"; cases "snd x \<in> {i,Suc i}")
         (auto simp: inversions_on_def swp_id apply_perm_simps)
    hence "map_prod swp swp (map_prod swp swp x) \<in> map_prod swp swp ` inversions_on A p \<or> x = (i, Suc i)"
      by (rule disj_forward) auto
    also have "map_prod swp swp (map_prod swp swp x) = map_prod (swp \<circ> swp) (swp \<circ> swp) x"
      by (auto simp: map_prod_def case_prod_unfold)
    also have "swp \<circ> swp = id"
      by (simp add: swp_def o_def Fun.swap_def fun_eq_iff)
    finally show "x \<in> insert (i, Suc i) (map_prod swp swp ` inversions_on A p)"
      by auto
  next
    fix x assume "x \<in> insert (i, Suc i) (map_prod swp swp ` inversions_on A p)"
    thus "x \<in> inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>)"
      using assms(1) swp_id[of "fst x"] swp_id[of "snd x"] \<open>i \<in> A\<close> \<open>Suc i \<in> A\<close>
      by (cases "fst x \<in> {i,Suc i}"; cases "snd x \<in> {i,Suc i}")
         (auto simp: inversions_on_def apply_perm_simps)
  qed
qed

text \<open>
  In general, swapping two adjacent natural numbers either increases the number of inversions
  by 1 or decreases it by 1. In both cases, the parity is flipped.
\<close>
lemma count_inversions_on_swap:
  fixes i :: nat
  assumes "set_perm p \<subseteq> A" "finite A" "i \<in> A" "Suc i \<in> A"
  defines "swp \<equiv> Fun.swap i (Suc i) id"
  shows "int (card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>))) =
         int (card (inversions_on A p)) + (if p \<langle>$\<rangle> i < p \<langle>$\<rangle> (Suc i) then 1 else -1)"
proof -
  have inj: "inj_on (map_prod swp swp) A" for A
  proof -
    have "inj_on id A"
      by simp
    also have "id = map_prod id id"
      by (simp add: fun_eq_iff)
    also have "id = swp \<circ> swp"
      by (simp add: swp_def Fun.swap_def fun_eq_iff)
    also have "map_prod \<dots> \<dots> = map_prod swp swp \<circ> map_prod swp swp"
      by (simp add: map_prod_def fun_eq_iff)
    finally show "inj_on (map_prod swp swp) A"
      by (rule inj_on_imageI2)
  qed

  have *: "card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>)) = Suc (card (inversions_on A p))"
    if "p \<langle>$\<rangle> i < p \<langle>$\<rangle> (Suc i)" "set_perm p \<subseteq> A" for p
  proof -
    have *: "(i, Suc i) \<notin> map_prod swp swp ` inversions_on A p"
      by (auto simp: inversions_on_def swp_def Fun.swap_def split: if_splits)
    have "inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>) = insert (i, Suc i) (map_prod swp swp ` inversions_on A p)"
      unfolding swp_def using that assms by (subst inversions_on_nat_swap1) auto
    also have "card \<dots> = Suc (card (map_prod swp swp ` inversions_on A p))"
      using * that \<open>finite A\<close> by (subst card.insert) auto
    also have "card (map_prod swp swp ` inversions_on A p) = card (inversions_on A p)"
      using inj by (intro card_image) auto
    finally show "card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>)) = Suc (card (inversions_on A p))" .
  qed

  show ?thesis
  proof (cases "p i < p (Suc i)")
    case True
    thus ?thesis using *[of p] assms by simp
  next
    case False
    have "p i \<noteq> p (Suc i)"
      by auto
    with False have "p i > p (Suc i)"
      by linarith    

    define p' where "p' = p * \<langle>i \<leftrightarrow> Suc i\<rangle>"
    have "card (inversions_on A (p' * \<langle>i \<leftrightarrow> Suc i\<rangle>)) = Suc (card (inversions_on A p'))"
      by (rule *) (use \<open>p i > p (Suc i)\<close> assms in \<open>auto simp: p'_def apply_perm_simps\<close>)
    also have "p' * \<langle>i \<leftrightarrow> Suc i\<rangle> = p"
      by (auto simp: p'_def swp_def Fun.swap_def mult.assoc)
    finally show ?thesis
      using False by (simp add: p'_def swp_def o_def)
  qed
qed

lemma even_count_inversions_swap_iff:
  assumes "set_perm p \<subseteq> A" "finite A" "i \<in> A" "Suc i \<in> A"
  shows   "even (card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>))) \<longleftrightarrow>
           odd (card (inversions_on A p))"
proof -
  have "even (card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>))) =
        even (int (card (inversions_on A (p * \<langle>i \<leftrightarrow> Suc i\<rangle>))))"
    by simp
  also have "\<dots> \<longleftrightarrow> odd (card (inversions_on A p))"
    using assms by (subst count_inversions_on_swap) simp_all
  finally show ?thesis .
qed
    
text \<open>
  The following function converts a swap @{term "\<langle>(i::nat) \<leftrightarrow> j\<rangle>"} with \<open>i < j\<close> into a sequence
  of swaps of adjacent elements.
\<close>
function adj_swaps_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "adj_swaps_nat a b =
     (if a \<ge> b then []
      else if b = a + 1 then [a]
      else a # adj_swaps_nat (a+1) b @ [a])"
  by auto
termination by (relation "measure (\<lambda>(a,b). b - a)") auto

lemmas [simp del] = adj_swaps_nat.simps

lemma length_adj_swaps_nat:
  "a < b \<Longrightarrow> length (adj_swaps_nat a b) = 2 * (b - a) - 1"
  by (induction a b rule: adj_swaps_nat.induct; subst adj_swaps_nat.simps) auto

lemma adj_swaps_nat_correct:
  assumes "a < b"
  shows   "perm_swaps (map (\<lambda>i. (i, Suc i)) (adj_swaps_nat a b)) = \<langle>a \<leftrightarrow> b\<rangle>"
  using assms
proof (induction a b rule: adj_swaps_nat.induct)
  case (1 a b)
  show ?case
  proof (cases "b = a + 1")
    case True
    thus ?thesis
      by (subst adj_swaps_nat.simps) (auto simp: o_def Fun.swap_def)
  next
    case False
    hence "perm_swaps (map (\<lambda>i. (i, Suc i)) (adj_swaps_nat a b)) = 
            \<langle>a \<leftrightarrow> Suc a\<rangle> * \<langle>Suc a \<leftrightarrow> b\<rangle> * \<langle>a \<leftrightarrow> Suc a\<rangle>"
      using 1 by (subst adj_swaps_nat.simps) (simp_all add: mult.assoc)
    also have "\<dots> = \<langle>a \<leftrightarrow> b\<rangle>" using False 1
      by (intro perm_eqI) (auto simp: apply_perm_simps apply_perm_swap_eq Fun.swap_def)
    finally show ?thesis .
  qed
qed

lemma set_perm_apply_adj_transps:
  assumes "\<forall>x\<in>set xs. x \<in> A \<and> Suc x \<in> A"
  shows   "set_perm (perm_swaps (map (\<lambda>i. (i, Suc i)) xs)) \<subseteq> A"
  using assms by (intro order.trans[OF set_perm_swaps]) (auto simp: swaps_set_def)

lemma set_adj_swaps_nat:
  "a < b \<Longrightarrow> set (adj_swaps_nat a b) = {a..<b}"
  by (induction a b rule: adj_swaps_nat.induct, subst adj_swaps_nat.simps) auto

lemma count_inversion_diff_swap_odd_nat:
  fixes a b :: nat
  assumes "set_perm p \<subseteq> A" "finite A" "{min a b..max a b} \<subseteq> A" "a \<noteq> b"
  shows "odd (int (card (inversions_on A (p * \<langle>a \<leftrightarrow> b\<rangle>))) - int (card (inversions_on A p)))"
  using assms(3,4)
proof (induction a b rule: linorder_wlog)
  case (le a b)
  hence "a < b" by auto
  from le have "{a..b} \<subseteq> A"
    by (simp add: min_def max_def)
  define xs where "xs = adj_swaps_nat a b"
  define c where "c = (\<lambda>p::nat perm. int (card (inversions_on A p)))"

  have "\<forall>x\<in>set xs. x \<in> A \<and> Suc x \<in> A"
    using \<open>{a..b} \<subseteq> A\<close> \<open>a < b\<close> unfolding xs_def by (subst set_adj_swaps_nat) auto
  hence "even (c (p * perm_swaps (map (\<lambda>i. (i, Suc i)) xs)) - c p - int (length xs))"
  proof (induction xs rule: rev_induct)
    case (snoc x xs)
    define \<tau> where "\<tau> = perm_swaps (map (\<lambda>i. (i, Suc i)) xs)"
    have subset: "set_perm (p * \<tau>) \<subseteq> A" unfolding \<tau>_def using assms snoc
      by (intro order.trans[OF set_perm_times] Un_least assms set_perm_apply_adj_transps) auto
    have "even (c (p * \<tau>) - c p - int (length xs))"
      unfolding \<tau>_def using snoc.prems by (intro snoc.IH) auto
    moreover have "even (c (p * \<tau> * \<langle>x \<leftrightarrow> Suc x\<rangle>) - c (p * \<tau>) - 1)"
      unfolding c_def using \<open>finite A\<close> snoc.prems assms subset
      by (subst count_inversions_on_swap) auto
    ultimately have "even ((c (p * \<tau> * \<langle>x \<leftrightarrow> Suc x\<rangle>) - c (p * \<tau>) - 1) +
                             (c (p * \<tau>) - c p - int (length xs)))"
      by (subst even_add) blast+
    also have "\<dots> = c (p * perm_swaps (map (\<lambda>i. (i, Suc i)) (xs @ [x]))) -
                    c p - int (length (xs @ [x]))"
      by (simp add: o_assoc \<tau>_def mult.assoc)
    finally show ?case .
  qed auto
  moreover have "odd (length xs)"
    unfolding xs_def using \<open>a < b\<close> by (subst length_adj_swaps_nat) auto
  ultimately have "odd (c (p * perm_swaps (map (\<lambda>i. (i, Suc i)) xs)) - c p)"
    by simp
  also have "perm_swaps (map (\<lambda>i. (i, Suc i)) xs) = \<langle>a \<leftrightarrow> b\<rangle>"
    using \<open>a < b\<close> by (simp add: xs_def adj_swaps_nat_correct)
  finally show ?case
    by (simp add: c_def id_def)
qed (simp_all add: swap_commute min.commute max.commute)

text \<open>
  We thus obtain that a permutation on the natural numbers from 0 to \<open>n - 1\<close> is even iff
  it has an even number of inversions on that set.
\<close>
lemma evenperm_iff_even_inversions_nat:
  fixes p :: "nat perm"
  assumes "set_perm p \<subseteq> {..<n}"
  shows   "even_perm p \<longleftrightarrow> even (card (inversions_on {..<n} p))"
proof -
  from assms show ?thesis
  proof (induction p rule: perm_rev_induct')
    case (swap a b p)
    hence "even_perm (p * \<langle>a \<leftrightarrow> b\<rangle>) \<longleftrightarrow> odd (card (inversions_on {..<n} p))"
      using swap by (subst even_perm_times) auto
    also have "odd (int (card (inversions_on {..<n} (p * \<langle>a \<leftrightarrow> b\<rangle>))) -
                    int (card (inversions_on {..<n} p)))"
      by (rule count_inversion_diff_swap_odd_nat) (use swap in auto)
    hence "odd (card (inversions_on {..<n} p)) \<longleftrightarrow>
           even (card (inversions_on {..<n} (p * \<langle>a \<leftrightarrow> b\<rangle>)))"
      by simp
    finally show ?case .
  qed auto
qed

text \<open>
  Using our transfer machinery, we can now let \<open>f\<close> be the obvious strictly monotonic bijection
  between a finite set \<open>A\<close> and the natural numbers less than \<open>|A|\<close> and lift the above result
  along that bijection to obtain the result for arbitrary permutations:
\<close>
theorem even_perm_iff_even_inversions:
  fixes p :: "'a :: linorder perm"
  assumes "set_perm p \<subseteq> A" and "finite A"
  shows   "even_perm p \<longleftrightarrow> even (card (inversions_on A p))"
proof -
  include lifting_syntax
  obtain f :: "nat \<Rightarrow> 'a" where f: "f ` {..<card A} = A" "strict_mono_on f {..<card A}"
    using finite_bij_nats_lessThan[of A] assms by auto
  have [simp]: "f x < f y \<longleftrightarrow> x < y" if "x < card A" "y < card A" for x y
    using that strict_mono_onD[OF f(2), of x y] strict_mono_onD[OF f(2), of y x]
    by (cases x y rule: linorder_cases) auto

  interpret perm_transfer "{..<card A}" A f "inv_into {..<card A} f"
    using strict_mono_on_imp_inj_on[OF f(2)] f(1)
    by unfold_locales (auto intro!: inv_into_f_f simp: bij_betw_def)
  
  have [transfer_rule]: "rel_set R {..<card A} A"
    using f by (force simp: rel_set_def R_def image_def)
  have [transfer_rule]: "(R ===> R ===> (=)) (<) (<)"
    using f(2) by (auto simp: rel_fun_def R_def intro: strict_mono_onD[OF f(2)])
  have [transfer_rule]: "rel_perm R (lift2 p) p"
    by (rule lift2_transfer) fact
  show "even_perm p = even (card (inversions_on A p))"
    using \<open>set_perm p \<subseteq> A\<close> by transfer (rule evenperm_iff_even_inversions_nat)
qed


subsection \<open>The number of permutations on a set\<close>

lemma bij_betw_perms_nat_lessThan:
  "bij_betw (\<lambda>xs. Perm (\<lambda>i. if i < n then xs ! i else i))
     {xs. set xs = {..<n} \<and> distinct xs} {p. set_perm p \<subseteq> {..<n}}"
proof -
  define A where "A = {xs. set xs = {..<n} \<and> distinct xs}"
  define B where "B = {p. set_perm p \<subseteq> {..<n}}"
  define f where "f = (\<lambda>xs. Perm (\<lambda>i. if i < n then xs ! i else i))"
  define g where "g = (\<lambda>p. map (apply_perm p) [0..<n])"

  have length_A: "length xs = n" if "xs \<in> A" for xs
    using distinct_card[of xs] that by (auto simp: A_def)

  have f_eq: "(f xs) \<langle>$\<rangle> i = (if i < n then xs ! i else i)" if "xs \<in> A" for xs i
    unfolding f_def
  proof (subst apply_perm_Perm)
    show "finite {..<n}" by auto
    show "inj_on (\<lambda>i. if i < n then xs ! i else i) {..<n}"
      using that by (auto simp: A_def distinct_conv_nth set_conv_nth inj_on_def length_A[OF that])
  next
    fix i assume "i \<in> {..<n}"
    hence "xs ! i \<in> set xs"
      using that by (auto simp: set_conv_nth length_A)
    also have "\<dots> = {..<n}"
      using that by (simp add: A_def)
    finally show "(if i < n then xs ! i else i) \<in> {..<n}"
      using \<open>i \<in> _\<close> by simp
  qed auto

  have length_g [simp]: "length (g p) = n" for p
    by (simp add: g_def)
  have g_eq: "g p ! i = p i" if "i < n" for p i
    using that by (auto simp: g_def)

  have f_in_B [simp, intro]: "f xs \<in> B" if "xs \<in> A" for xs
    using that by (auto simp: B_def set_perm_eq f_eq)
  have g_in_A [simp, intro]: "g p \<in> A" if "p \<in> B" for p
  proof -
    from that have "bij_betw (apply_perm p) {..<n} {..<n}"
      by (intro bij_betw_apply_perm) (auto simp: B_def)
    thus ?thesis
      unfolding A_def find_theorems bij_betw apply_perm
      by (auto simp: g_def distinct_conv_nth bij_betw_def atLeast0LessThan)
  qed
  have [simp]: "p \<langle>$\<rangle> i = i" if "p \<in> B" "i \<ge> n" for i p
    using that by (auto simp: B_def)
  
  have "bij_betw f A B"
  proof (rule bij_betw_byWitness[of _ g])
    show "\<forall>xs\<in>A. g (f xs) = xs"
      by (auto simp: f_eq g_eq length_A intro!: nth_equalityI)
    show "\<forall>p\<in>B. f (g p) = p"
      by (auto simp: f_eq g_eq length_A intro!: nth_equalityI perm_eqI)
  qed auto
  thus ?thesis unfolding f_def A_def B_def .
qed

lemma card_set_perm_subset:
  assumes "finite A"
  shows   "card {p. set_perm p \<subseteq> A} = fact (card A)"
proof -
  obtain f where f: "bij_betw f {..<card A} A"
    using ex_bij_betw_nat_finite[OF assms] by (auto simp: atLeast0LessThan)
  interpret perm_transfer "{..<card A}" A f "inv_into {..<card A} f"
    using f by unfold_locales (auto simp: bij_betw_def)

  have "bij_betw lift1 {p. set_perm p \<subseteq> {..<card A}} {p. set_perm p \<subseteq> A}"
    by (rule bij_betw_byWitness[of _ lift2]) (auto simp: set_lift1 set_lift2 intro!: f_in)
  hence "card {p. set_perm p \<subseteq> {..<card A}} = card {p. set_perm p \<subseteq> A}"
    by (rule bij_betw_same_card)
  also have "card {p. set_perm p \<subseteq> {..<card A}} = fact (card A)"
    using bij_betw_same_card[OF bij_betw_perms_nat_lessThan[of "card A"]]
          card_distinct_lists_set_eq[of "{..<card A}"] by (simp add: conj_commute)
  finally show ?thesis ..
qed

end