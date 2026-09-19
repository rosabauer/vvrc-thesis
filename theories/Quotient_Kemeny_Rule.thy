section ‹Quotient Kemeny Rule›

theory Quotient_Kemeny_Rule
  imports Quotient_Swapwise_Rules_Helpers
begin

text ‹
  The quotient counterpart of the Kemeny rule on anonymity-homogeneity
  classes of elections over a fixed alternative set A: the distance-
  rationalized quotient rule for the normalized (averaged) swap distance
  and the strong-unanimity consensus restricted to A.
  Note the two deltas to kemeny_rule (= swap_ℛ strong_unanimity):
  l_one_avg instead of l_one, since the raw swap distance is not invariant
  under homogeneity (copying an electorate scales it), and
  strong_unanimity_in A instead of strong_unanimity, since the relation
  fixes the alternative set. The equivalence of the induced winners is the
  interchangeability claim noted at strong_unanimity_in (TBD).
›

subsection ‹Definition›

fun kemeny_rule⇩𝒬 :: "'a set ⇒ ('a, 'v :: wellorder) Election set ⇒ 'a Result" where
  "kemeny_rule⇩𝒬 A E⇩𝒬 =
      𝒮𝒞ℱ_result.distance_ℛ⇩𝒬
        (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
        (votewise_distance swap l_one_avg)
        (strong_unanimity_in A) E⇩𝒬"

subsection ‹Invariance of the Winners (P5)›

lemma swap_dr_invar_anon_hom:
  fixes A :: "'a set"
  shows "is_symmetry
           (fun⇩ℰ (𝒮𝒞ℱ_result.ℛ⇩𝒲 (votewise_distance swap l_one_avg)
                      (strong_unanimity_in A)))
           (Invariance (anonymity_homogeneity⇩ℛ
              (elections_𝒜 A :: ('a, 'v :: wellorder) Election set)))"
  by (rule 𝒮𝒞ℱ_result.anon_hom_score_invar_imp_invar_dr)
     (rule swap_score_invar_anon_hom)

subsection ‹Quotient Instantiation Theorems›

theorem kemeny_rule⇩𝒬_winners:
  fixes
    A :: "'a set" and
    AC :: "('a, 'v :: wellorder) Election set"
  assumes "AC ∈ elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  shows "π⇩𝒬 (fun⇩ℰ (𝒮𝒞ℱ_result.ℛ⇩𝒲 (votewise_distance swap l_one_avg)
                        (strong_unanimity_in A))) AC
       = 𝒮𝒞ℱ_result.ℛ⇩𝒬 (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
            (votewise_distance swap l_one_avg) (strong_unanimity_in A) AC"
  by (rule 𝒮𝒞ℱ_result.invar_dr_simple_dist_imp_quotient_dr_winners[OF
        swap_l_one_avg_simple
        strong_unanimity_in_closed_under_anon_hom
        𝒮𝒞ℱ_result.limit_invar_anon_hom
        strong_unanimity_in_invar_anon_hom
        swap_dr_invar_anon_hom
        assms
        anon_hom_equiv
        strong_unanimity_elections_subset])

theorem kemeny_rule⇩𝒬_is_quotient_dr:
  fixes
    A :: "'a set" and
    AC :: "('a, 'v :: wellorder) Election set"
  assumes "AC ∈ elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  shows "π⇩𝒬 (fun⇩ℰ (𝒮𝒞ℱ_result.distance_ℛ (votewise_distance swap l_one_avg)
                        (strong_unanimity_in A))) AC
       = kemeny_rule⇩𝒬 A AC"
  unfolding kemeny_rule⇩𝒬.simps
  by (rule 𝒮𝒞ℱ_result.invar_dr_simple_dist_imp_quotient_dr[OF
        swap_l_one_avg_simple
        strong_unanimity_in_closed_under_anon_hom
        𝒮𝒞ℱ_result.limit_invar_anon_hom
        strong_unanimity_in_invar_anon_hom
        swap_dr_invar_anon_hom
        assms
        anon_hom_equiv
        strong_unanimity_elections_subset])

end