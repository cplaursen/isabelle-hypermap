theory Walkup
  imports Hypermap
begin

context hypermap begin

definition skip1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
"skip1 z f \<equiv> \<lambda> y. (if f y = z then f z else f y)"

lemma inj_skip:
  assumes "inj_on f S"
  shows "inj_on (skip1 z f) (S - {z})"
  oops

definition skip_edge1 where
"skip_edge1 z x \<equiv> if (edge H z) = z then edge H x else
                  (if (face H (edge H x)) = z then edge H z else
                  (if edge H x = z then edge H (node H z) else edge H x))"

lemma skip_edge_subproof:
  assumes "u \<noteq> z"
  shows "skip_edge1 z u \<noteq> z"
  by (metis assms faceK nodeK skip_edge1_def)



end