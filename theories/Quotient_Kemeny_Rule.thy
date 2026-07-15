theory Quotient_Kemeny_Rule
  imports "Compositional_Structures/Basic_Modules/Component_Types/Quotient_Distance_Rationalization"
          "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance"
begin

lemma swap_l_one_simple:
  fixes A :: "'a set"
  assumes "finite A"
  shows "simple
           (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
           (elections_\<A> A)
           (votewise_distance swap l_one :: ('a, 'v :: linorder) Election Distance)"
  proof (unfold simple.simps distance_infimum\<^sub>\<Q>.simps, safe)

end