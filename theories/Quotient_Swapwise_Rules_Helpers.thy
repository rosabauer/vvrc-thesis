theory Quotient_Swapwise_Rules_Helpers
  imports "Compositional_Structures/Basic_Modules/Component_Types/Quotient_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Quotients/Election_Quotients"
    "Compositional_Structures/Basic_Modules/Component_Types/Consensus"
    "Kemeny_Rule"
begin

lemma swap_l_one_simple:
  fixes A :: "'a set"
  assumes "finite A"
  shows "simple
           (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
           (elections_\<A> A)
           (votewise_distance swap l_one :: ('a, 'v :: linorder) Election Distance)"
  sorry

lemma anon_hom_equiv:
  fixes A :: "'a set"
  shows "equiv (elections_\<A> A) (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))"
proof -
  have "\<forall> E \<in> elections_\<A> A. finite (voters_\<E> E)"
    unfolding elections_\<A>.simps
    by blast
  thus ?thesis
    by (rule anonymity_homogeneity_is_equivalence)
qed

lemma (in result) limit_invar_anon_hom:
  "is_symmetry
      (\<lambda> E :: ('a, 'v) Election. limit (alternatives_\<E> E) UNIV)
      (Invariance (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)))"
proof -
  have "\<forall> E E' :: ('a, 'v) Election.
          (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)
            \<longrightarrow> alternatives_\<E> E = alternatives_\<E> E'"
  proof (intro allI impI)
    fix E E' :: "('a, 'v) Election"
    assume "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    hence "E \<in> elections_\<A> UNIV \<and> E' \<in> elections_\<A> UNIV"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
    hence "alternatives_\<E> E = UNIV \<and> alternatives_\<E> E' = UNIV"
      unfolding elections_\<A>.simps
      by blast
    thus "alternatives_\<E> E = alternatives_\<E> E'"
      by simp
  qed
  thus ?thesis
    unfolding is_symmetry.simps
    by metis
qed

lemma strong_unanimity_elections_subset:
  fixes A :: "'a set"
  shows "elections_\<K> strong_unanimity \<subseteq> elections_\<A> A"
  apply (auto simp add: well_formed_elections_def)
  done


end