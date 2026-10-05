(*  File:       Votewise_Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance\<close>

theory Votewise_Distance
  imports "Social_Choice_Types/Norm"
          "Distance"
begin

text \<open>
  Votewise distances are a natural class of distances on elections
  which depend on the submitted votes in a simple and transparent manner.
  They are formed by using any distance d on individual orders and combining
  the components with a norm on \<open>\<real>\<^sup>n\<close>.
\<close>

subsection \<open>Definition\<close>

fun votewise_distance :: "'a Vote Distance \<Rightarrow> Norm \<Rightarrow>
        ('a, 'v :: linorder) Election Distance" where
  "votewise_distance d n (A, V, p) (A', V', p') =
    (if finite V \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')
    then n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))
    else \<infinity>)"


subsection \<open>Auxiliary Lemmas\<close>

lemma permute_invariant_under_map:
  fixes l l' :: "'a list"
  assumes "l <~~> l'"
  shows "map f l <~~> map f l'"
  using assms
  by simp

lemma sorted_list_of_set_nth_equals_card:
  fixes
    V :: "'v :: linorder set" and
    x :: "'v"
  assumes
    fin_V: "finite V" and
    x_V: "x \<in> V"
  shows "sorted_list_of_set V!(card {v \<in> V. v < x}) = x"
proof -
  let ?c = "card {v \<in> V. v < x}" and
      ?set = "{v \<in> V. v < x}"
  have "\<forall> v \<in> V. \<exists> n. n < card V \<and> (sorted_list_of_set V!n) = v"
    using length_sorted_list_of_set sorted_list_of_set_unique in_set_conv_nth fin_V
    by metis
  then obtain \<phi> :: "'v \<Rightarrow> nat" where
    index_\<phi>: "\<forall> v \<in> V. \<phi> v < card V \<and> (sorted_list_of_set V!(\<phi> v)) = v"
    by metis
  \<comment> \<open>\<open>\<phi> x = ?c\<close>, i.e., \<open>\<phi> x \<ge> ?c\<close> and \<open>\<phi> x \<le> ?c\<close>\<close>
  let ?i = "\<phi> x"
  have inj_\<phi>: "inj_on \<phi> V"
    using inj_onI index_\<phi>
    by metis
  have "\<forall> v \<in> V. \<forall> v' \<in> V. v < v' \<longrightarrow> \<phi> v < \<phi> v'"
    using leD linorder_le_less_linear sorted_list_of_set_unique
          sorted_sorted_list_of_set sorted_nth_mono fin_V index_\<phi>
    by metis
  hence "\<forall> j \<in> {\<phi> v | v. v \<in> ?set}. j < ?i"
    using x_V
    by blast
  moreover have fin_img: "finite ?set"
    using fin_V
    by simp
  ultimately have "?i \<ge> card {\<phi> v | v. v \<in> ?set}"
    using set_card_upper_bound
    by simp
  hence geq: "?c \<le> ?i"
    using inj_\<phi>
    by (simp add: card_image inj_on_subset setcompr_eq_image)
  have sorted_\<phi>:
    "\<forall> i < card V. \<forall> j < card V. i < j
        \<longrightarrow> (sorted_list_of_set V!i) < (sorted_list_of_set V!j)"
    by (simp add: sorted_wrt_nth_less)
  have leq: "?i \<le> ?c"
  proof (rule ccontr, cases "?c < card V")
    case True
    let ?A = "\<lambda> j. {sorted_list_of_set V!j}"
    assume "\<not> ?i \<le> ?c"
    hence "?c < ?i"
      by simp
    hence "\<forall> j \<le> ?c. sorted_list_of_set V!j \<in> V \<and> sorted_list_of_set V!j < x"
      using sorted_\<phi> geq index_\<phi> x_V fin_V set_sorted_list_of_set
            length_sorted_list_of_set nth_mem order.strict_trans1
      by (metis (mono_tags, lifting))
    hence "{sorted_list_of_set V!j | j. j \<le> ?c} \<subseteq> {v \<in> V. v < x}"
      by blast
    also have "{sorted_list_of_set V!j | j. j \<le> ?c} =
                  {sorted_list_of_set V!j | j. j \<in> {0 ..< (?c + 1)}}"
      using add.commute
      by auto
    also have "\<dots> = (\<Union> j \<in> {0 ..< (?c + 1)}. {sorted_list_of_set V!j})"
      by blast
    finally have subset: "(\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) \<subseteq> {v \<in> V. v < x}"
      by simp
    have "\<forall> i \<le> ?c. \<forall> j \<le> ?c.
              i \<noteq> j \<longrightarrow> sorted_list_of_set V!i \<noteq> sorted_list_of_set V!j"
      using True
      by (simp add: nth_eq_iff_index_eq)
    hence "\<forall> i \<in> {0 ..< (?c + 1)}. \<forall> j \<in> {0 ..< (?c + 1)}.
              (i \<noteq> j \<longrightarrow> {sorted_list_of_set V!i} \<inter> {sorted_list_of_set V!j} = {})"
      by fastforce
    hence "disjoint_family_on ?A {0 ..< (?c + 1)}"
      unfolding disjoint_family_on_def
      by simp
    moreover have "\<forall> j \<in> {0 ..< (?c + 1)}. card (?A j) = 1"
      by simp
    ultimately have
      "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = (\<Sum> j \<in> {0 ..< (?c + 1)}. 1)"
      using card_UN_disjoint'
      by fastforce
    hence "card (\<Union> j \<in> {0 ..< (?c + 1)}. ?A j) = ?c + 1"
      by simp
    hence "?c + 1 \<le> ?c"
      using subset card_mono fin_img
      by (metis (no_types, lifting))
    thus False
      by simp
  next
    case False
    thus False
      using x_V index_\<phi> geq order_le_less_trans
      by blast
  qed
  thus ?thesis
    using geq leq x_V index_\<phi>
    by simp
qed

lemma linorder_rank_injective:
  fixes
    V :: "'v :: linorder set" and
    v v' :: "'v"
  assumes
    v_in_V: "v \<in> V" and
    v'_in_V: "v' \<in> V" and
    v'_neq_v: "v' \<noteq> v" and
    fin_V: "finite V"
  shows "card {x \<in> V. x < v} \<noteq> card {x \<in> V. x < v'}"
proof -
  have "v < v' \<or> v' < v"
    using v'_neq_v linorder_less_linear
    by metis
  hence "{x \<in> V. x < v} \<subset> {x \<in> V. x < v'} \<or> {x \<in> V. x < v'} \<subset> {x \<in> V. x < v}"
    using v_in_V v'_in_V dual_order.strict_trans
    by blast
  thus ?thesis
    using assms sorted_list_of_set_nth_equals_card
    by (metis (full_types))
qed

lemma permute_invariant_under_coinciding_funs:
  fixes
    l :: "'v list" and
    \<pi>\<^sub>1 \<pi>\<^sub>2 :: "nat \<Rightarrow> nat"
  assumes "\<forall> i < length l. \<pi>\<^sub>1 i = \<pi>\<^sub>2 i"
  shows "permute_list \<pi>\<^sub>1 l = permute_list \<pi>\<^sub>2 l"
  using assms
  unfolding permute_list_def
  by simp

lemma to_list_permutes_under_bij:
  fixes
    \<pi> :: "'v :: linorder \<Rightarrow> 'v" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes "bij \<pi>"
  shows
    "let \<phi> = \<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)}
      in (to_list V p) = permute_list \<phi> (to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)))"
proof (cases "finite V")
  case False
  \<comment> \<open>If \<open>V\<close> is infinite, both lists are empty.\<close>
  hence "to_list V p = []"
    by simp
  moreover have "infinite (\<pi> ` V)"
    using False assms bij_betw_finite bij_betw_subset top_greatest
    by metis
  hence "to_list (\<pi> ` V) (\<lambda> x. p (the_inv \<pi> x)) = []"
    by simp
  ultimately show ?thesis
    by simp
next
  case True
  let
    ?q = "\<lambda> x. p (the_inv \<pi> x)" and
    ?img = "\<pi> ` V" and
    ?n = "length (to_list V p)" and
    ?perm = "\<lambda> i. card {v \<in> \<pi> ` V. v < \<pi> ((sorted_list_of_set V)!i)}"
    \<comment> \<open>These are auxiliary statements equating everything with \<open>?n\<close>.\<close>
  have card_eq: "card ?img = card V"
    using assms bij_betw_same_card bij_betw_subset top_greatest
    by metis
  also have card_length_V: "?n = \<dots>"
    by simp
  also have card_length_img: "length (to_list ?img ?q) = card ?img"
    using True
    by simp
  finally have eq_length: "length (to_list ?img ?q) = ?n"
    by simp
  show ?thesis
  proof (unfold Let_def permute_list_def, rule nth_equalityI)
    \<comment> \<open>The lists have equal lengths.\<close>
    show
      "length (to_list V p) =
          length (map
            (\<lambda> i. to_list ?img ?q!(card {v \<in> ?img.
                v < \<pi> (sorted_list_of_set V!i)}))
              [0 ..< length (to_list ?img ?q)])"
      using eq_length
      by simp
  next
    \<comment> \<open>The \<open>i\<close>th entries of the lists coincide.\<close>
    fix i :: "nat"
    assume in_bnds: "i < ?n"
    let ?c = "card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}"
    have "map (\<lambda> i. (to_list ?img ?q)!?c) [0 ..< ?n]!i =
            p ((sorted_list_of_set V)!i)"
    proof -
      have "\<forall> v. v \<in> ?img \<longrightarrow> {v' \<in> ?img. v' < v} \<subseteq> ?img - {v}"
        by blast
      moreover have elem_of_img: "\<pi> (sorted_list_of_set V!i) \<in> ?img"
        using True in_bnds image_eqI nth_mem card_length_V
              length_sorted_list_of_set set_sorted_list_of_set
        by metis
      ultimately have
        "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}
      \<subseteq> ?img - {\<pi> (sorted_list_of_set V!i)}"
        by simp
      hence "{v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)} \<subset> ?img"
        using elem_of_img
        by blast
      moreover have img_card_eq_V_length: "card ?img = ?n"
        using card_eq card_length_V
        by presburger
      ultimately have card_in_bnds: "?c < ?n"
        using True finite_imageI psubset_card_mono
        by (metis (mono_tags, lifting))
      moreover have img_list_map:
        "map (\<lambda> i. to_list ?img ?q!?c) [0 ..< ?n]!i = to_list ?img ?q!?c"
        using in_bnds
        by simp
      also have img_list_card_eq_inv_img_list:
        "\<dots> = ?q ((sorted_list_of_set ?img)!?c)"
        using in_bnds to_list_simp in_bnds img_card_eq_V_length card_in_bnds
        by (metis (no_types, lifting))
      also have img_card_eq_img_list_i:
        "\<dots> = ?q (\<pi> (sorted_list_of_set V!i))"
        using True elem_of_img
        by (simp add: sorted_list_of_set_nth_equals_card)
      finally show ?thesis
        using assms bij_betw_imp_inj_on the_inv_f_f
              img_list_map img_card_eq_img_list_i
              img_list_card_eq_inv_img_list
        by metis
    qed
    also have "to_list V p!i = p ((sorted_list_of_set V)!i)"
      using True in_bnds
      by simp
    finally show "to_list V p!i =
        map (\<lambda> i. (to_list ?img ?q)!(card {v \<in> ?img. v < \<pi> (sorted_list_of_set V!i)}))
          [0 ..< length (to_list ?img ?q)]!i"
      using in_bnds eq_length Collect_cong card_eq
      by simp
  qed
qed


subsection \<open>Inference Rules\<close>

lemma symmetric_norm_inv_under_map_permute:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm" and
    A A'  :: "'a set" and
    \<phi> :: "nat \<Rightarrow> nat" and
    p p'  :: "'a Preference_Relation list"
  assumes
    perm: "\<phi> permutes {0 ..< length p}" and
    len_eq: "length p = length p'" and
    sym_n: "symmetry n"
  shows "n (map2 (\<lambda> q q'. d (A, q) (A', q')) p p') =
      n (map2 (\<lambda> q q'. d (A, q) (A', q')) (permute_list \<phi> p) (permute_list \<phi> p'))"
proof -
  have "length (map2 (\<lambda> x y. d (A, x) (A', y)) p p') = length p"
    using len_eq
    by simp
  hence "n (map2 (\<lambda> q q'. d (A, q) (A', q')) p p') =
      n (permute_list \<phi> (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
    using perm sym_n mset_permute_list atLeast_upt
    unfolding symmetry_def
    by fastforce
  thus ?thesis
    using perm len_eq atLeast_upt permute_list_map[of _ _ "\<lambda> (q, q'). d (A, q) (A', q')"]
    by (simp add: permute_list_zip)
qed

lemma symmetric_norm_imp_distance_anonymous:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "distance_anonymity (votewise_distance d n)"
proof (unfold distance_anonymity_def, safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  let ?rn1 = "rename \<pi> (A, V, p)" and
      ?rn2 = "rename \<pi> (A', V', p')" and
      ?rn_V = "\<pi> ` V" and
      ?rn_V' = "\<pi> ` V'" and
      ?rn_p = "p \<circ> (the_inv \<pi>)" and
      ?rn_p' = "p' \<circ> (the_inv \<pi>)" and
      ?len = "length (to_list V p)" and
      ?sl_V = "sorted_list_of_set V"
  let ?perm = "\<lambda> i. card {v \<in> ?rn_V. v < \<pi> (?sl_V!i)}" and
      \<comment> \<open>Use a total permutation function in order to
          apply facts such as \<open>mset_permute_list\<close>.\<close>
      ?perm_total = "\<lambda> i. if i < ?len
                           then card {v \<in> ?rn_V. v < \<pi> (?sl_V!i)}
                           else i"
  assume bij_\<pi>: "bij \<pi>"
  show "votewise_distance d n (A, V, p) (A', V', p') =
            votewise_distance d n ?rn1 ?rn2"
  proof (cases "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')")
    case False
      \<comment> \<open>Case: Both distances are infinite.\<close>
    hence "votewise_distance d n (A, V, p) (A', V', p') = \<infinity>"
      by auto
    moreover have "infinite V \<longrightarrow> infinite ?rn_V"
      using bij_\<pi> bij_betw_finite bij_betw_subset subset_UNIV
      by metis
    moreover have "V \<noteq> V' \<longrightarrow> ?rn_V \<noteq> ?rn_V'"
      using bij_\<pi> inj_image_mem_iff subsetI subset_antisym
      unfolding bij_def
      by metis
    ultimately show "votewise_distance d n (A, V, p) (A', V', p') =
            votewise_distance d n ?rn1 ?rn2"
      using False
      by auto
  next
    case True
      \<comment> \<open>Case: Both distances are finite.\<close>
    have lengths_eq: "?len = length (to_list V' p')"
      using True
      by simp
    have rn_V_permutes: "to_list V p = permute_list ?perm (to_list ?rn_V ?rn_p)"
      using assms to_list_permutes_under_bij bij_\<pi>
      unfolding comp_def
      by (metis (no_types))
    hence len_V_rn_V_eq: "?len = length (to_list ?rn_V ?rn_p)"
      by simp
    hence "permute_list ?perm (to_list ?rn_V ?rn_p) =
              permute_list ?perm_total (to_list ?rn_V ?rn_p)"
      using permute_invariant_under_coinciding_funs[of "to_list ?rn_V ?rn_p"]
      by presburger
    hence rn_list_perm_list_V:
      "to_list V p = permute_list ?perm_total (to_list ?rn_V ?rn_p)"
      using rn_V_permutes
      by metis
    have "to_list V' p' = permute_list ?perm (to_list ?rn_V' ?rn_p')"
      unfolding comp_def
      using True bij_\<pi> to_list_permutes_under_bij
      by (metis (no_types))
    hence rn_list_perm_list_V':
      "to_list V' p' = permute_list ?perm_total (to_list ?rn_V' ?rn_p')"
      using lengths_eq permute_invariant_under_coinciding_funs[of "to_list ?rn_V' ?rn_p'"]
      by fastforce
    have "?perm_total permutes {0 ..< ?len}"
    proof -
      have "\<forall> i j. i < ?len \<and> j < ?len \<and> i \<noteq> j
                   \<longrightarrow> \<pi> ((sorted_list_of_set V)!i) \<noteq> \<pi> ((sorted_list_of_set V)!j)"
        using True bij_\<pi> bij_pointE nth_eq_iff_index_eq length_map
              sorted_list_of_set.distinct_sorted_key_list_of_set to_list.elims
        by (metis (mono_tags, opaque_lifting))
      moreover have in_bnds_imp_img_el:
        "\<forall> i. i < ?len \<longrightarrow> \<pi> ((sorted_list_of_set V)!i) \<in> \<pi> ` V"
        using True image_eqI length_map nth_mem to_list.simps
              sorted_list_of_set.set_sorted_key_list_of_set
        by (metis (no_types))
      ultimately have
        "\<forall> i < ?len. \<forall> j < ?len. ?perm_total i = ?perm_total j \<longrightarrow> i = j"
        using True linorder_rank_injective Collect_cong finite_imageI
        by (metis (no_types, lifting))
      hence inj: "inj_on ?perm_total {0 ..< ?len}"
        unfolding inj_on_def
        by simp
      have "\<forall> v' \<in> \<pi> ` V. card {v \<in> \<pi> ` V. v < v'} < card (\<pi> ` V)"
        using True card_seteq finite_imageI less_irrefl linorder_not_le
              mem_Collect_eq subsetI
        by (metis (no_types, lifting))
      moreover have "\<forall> i < ?len. \<pi> ((sorted_list_of_set V)!i) \<in> \<pi> ` V"
        using in_bnds_imp_img_el
        by simp
      moreover have "card (\<pi> ` V) = card V"
        using bij_\<pi> bij_betw_same_card bij_betw_subset top_greatest
        by metis
      moreover have "card V = ?len"
        by simp
      ultimately have
        "\<forall> i. i < ?len \<longrightarrow> ?perm_total i \<in> {0 ..< ?len}"
        using atLeast0LessThan lessThan_iff
        by (metis (full_types))
      hence "?perm_total ` {0 ..< ?len} \<subseteq> {0 ..< ?len}"
        by force
      hence "bij_betw ?perm_total {0 ..< ?len} {0 ..< ?len}"
        using inj card_image card_subset_eq atLeast0LessThan finite_atLeastLessThan
        unfolding bij_betw_def
        by blast
      thus ?thesis
        using atLeast0LessThan bij_imp_permutes
        by fastforce
    qed
    hence "votewise_distance d n ?rn1 ?rn2 =
              n (map2 (\<lambda> q q'. d (A, q) (A', q'))
                      (permute_list ?perm_total (to_list ?rn_V ?rn_p))
                      (permute_list ?perm_total (to_list ?rn_V' ?rn_p')))"
      using symmetric_norm_inv_under_map_permute[of _ "to_list ?rn_V ?rn_p"]
            True assms len_V_rn_V_eq
      by force
    also have "\<dots> = n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
      using rn_list_perm_list_V rn_list_perm_list_V'
      by presburger
    finally show
      "votewise_distance d n (A, V, p) (A', V', p') = votewise_distance d n ?rn1 ?rn2"
      using True
      by force
  qed
qed

lemma neutral_dist_imp_neutral_votewise_dist:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  defines "vote_action \<equiv> \<lambda> \<pi> (A, q). (\<pi> ` A, rel_rename \<pi> q)"
  assumes "invariance\<^sub>\<D> d (carrier bijection\<^sub>\<A>\<^sub>\<G>) UNIV vote_action"
  shows "distance_neutrality well_formed_elections (votewise_distance d n)"
proof (unfold distance_neutrality.simps rewrite_invariance\<^sub>\<D>, safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile" and
    \<pi> :: "'a \<Rightarrow> 'a"
  assume
    carrier: "\<pi> \<in> carrier bijection\<^sub>\<A>\<^sub>\<G>" and
    valid: "(A, V, p) \<in> well_formed_elections" and
    valid': "(A', V', p') \<in> well_formed_elections"
  hence bij_\<pi>: "bij \<pi>"
    unfolding bijection\<^sub>\<A>\<^sub>\<G>_def
    using rewrite_carrier
    by blast
  thus "votewise_distance d n (A, V, p) (A', V', p') =
          votewise_distance d n
            (\<phi>_neutral well_formed_elections \<pi> (A, V, p))
              (\<phi>_neutral well_formed_elections \<pi> (A', V', p'))"
  proof (cases "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> A = A')")
    case True
    hence "finite V \<and> V = V' \<and> (V \<noteq> {} \<or> \<pi> ` A = \<pi> ` A')"
      by metis
    hence "votewise_distance d n
            (\<phi>_neutral well_formed_elections \<pi> (A, V, p))
                (\<phi>_neutral well_formed_elections \<pi> (A', V', p')) =
        n (map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
          (to_list V (rel_rename \<pi> \<circ> p)) (to_list V' (rel_rename \<pi> \<circ> p')))"
      using valid valid'
      by auto
    also have
      "\<dots> =
      n (map2 (\<lambda> q q'. d (\<pi> ` A, q) (\<pi> ` A', q'))
        (map (rel_rename \<pi>) (to_list V p)) (map (rel_rename \<pi>) (to_list V' p')))"
      using to_list_comp
      by metis
    also have
      "\<dots> = n (map2 (\<lambda> q q'. d (\<pi> ` A, rel_rename \<pi> q) (\<pi> ` A', rel_rename \<pi> q'))
              (to_list V p) (to_list V' p'))"
      unfolding map_helper
      by simp
    also have
      "\<dots> = (n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p')))"
      using rewrite_invariance\<^sub>\<D>[of d _ UNIV vote_action] assms carrier
            UNIV_I case_prod_conv
      unfolding vote_action_def
      by (metis (no_types, lifting))
    finally have "votewise_distance d n
        (\<phi>_neutral well_formed_elections \<pi> (A, V, p))
              (\<phi>_neutral well_formed_elections \<pi> (A', V', p')) =
        n (map2 (\<lambda> q q'. d (A, q) (A', q')) (to_list V p) (to_list V' p'))"
      by simp
    thus ?thesis
      using True
      by auto
  next
    case False
    hence "\<not> (finite V \<and> V = V' \<and> (V \<noteq> {} \<or> \<pi> ` A = \<pi> ` A'))"
      using bij_\<pi> bij_is_inj inj_image_eq_iff
      by metis
    thus ?thesis
      using False valid valid'
      by force
  qed
qed

lemma dist_avg_norm_eq_normalized_dist:
  assumes "finite V" and "V \<noteq> {}"
  shows "votewise_distance d l_one_avg (A,V,p) (A',V,p') =
  votewise_distance d l_one (A,V,p) (A',V,p')/ ereal( real ( card V))"
  by (simp add: card_gt_0_iff)

end