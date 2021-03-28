theory Rel_Digraph
    imports "Graph_Theory.Graph_Theory"
begin

section \<open>Graphs on relations\<close>

definition digraph_of_rel :: "'a rel \<Rightarrow> 'a pair_pre_digraph" where
"digraph_of_rel r = \<lparr>pverts = Field r, parcs = r\<rparr>"

interpretation pair_wf_digraph "digraph_of_rel r"
  by (simp add: FieldI1 FieldI2 pair_wf_digraph_def digraph_of_rel_def)

lemma rel_nonempty_verts:
  assumes "r \<noteq> {}"
  shows "verts (digraph_of_rel r) \<noteq> {}" (is "verts ?G \<noteq> {}")
proof -
  have 1: "verts ?G = Field r" by (simp add: digraph_of_rel_def)
  also have "Field r \<noteq> {}" by (simp add: Field_def Range_empty_iff assms)
  ultimately show "verts ?G  \<noteq> {}" by simp
qed

lemma mk_symmetric_ip_sym:
  assumes "sym r"
  shows "mk_symmetric (digraph_of_rel r) = (digraph_of_rel r)"
    (is "mk_symmetric (with_proj ?G) = ?G")
proof -
  have "pverts (mk_symmetric ?G) = pverts ?G" by simp
  also have "parcs (mk_symmetric ?G) = parcs ?G"
    by (metis assms adj_mk_symmetric_eq digraph_of_rel_def pair_pre_digraph.select_convs(2)
        symmetric_def with_proj_simps(3))
  ultimately show ?thesis by simp
qed

lemma
  assumes "connected (digraph_of_rel r)" "sym r" "r \<noteq> {}"
  shows "strongly_connected (digraph_of_rel r)" (is "strongly_connected ?G")
proof
  show "verts ?G \<noteq> {}"
    using assms(3) rel_nonempty_verts by (auto)
next
  fix u v assume "u \<in> verts ?G" "v \<in> verts ?G"
  then have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric ?G\<^esub> v" using assms(1)
    by (meson wellformed_mk_symmetric wf_digraph.connected_awalkE wf_digraph.reachable_awalkI wf_digraph_axioms wf_digraph_wp_iff)
  also have "?G  = mk_symmetric ?G" using assms(2) mk_symmetric_ip_sym by fastforce
  ultimately show "u \<rightarrow>\<^sup>*\<^bsub>?G\<^esub> v" by simp
qed

end
