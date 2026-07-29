theory Quotient_Swapwise_Rules_Helpers
  imports "Compositional_Structures/Basic_Modules/Component_Types/Quotient_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Quotients/Election_Quotients"
    "Compositional_Structures/Basic_Modules/Component_Types/Consensus"
    "Kemeny_Rule"
    "Compositional_Structures/Basic_Modules/Component_Types/Consensus_Class"

begin

(* We define a version of strong unanmity that applies to a fixed alternative set
 and for all voters outside the voter set, returns an empty profile.

This is useful to do because it makes proving easier
 - that the assumptions of invar_dr_.. apply to rules with a DR set.


TBD: We prove later that this does not affect the minimum distance
to the consensus class - and thus would be the same as
 using the unrestricted strong_unanmity.  *)

definition strong_unanimity_in :: "'a set \<Rightarrow> ('a, 'v :: wellorder, 'a Result) Consensus_Class" where
  "strong_unanimity_in A \<equiv> consensus_choice
    (\<lambda> E. strong_unanimity\<^sub>\<C> E \<and> alternatives_\<E> E = A
    \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {}))
    elect_first_module"


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
  shows "elections_\<K> (strong_unanimity_in A)  \<subseteq> elections_\<A> A"
  apply (auto simp add: well_formed_elections_def strong_unanimity_in_def)
  done


lemma strong_unanimity_in_closed_under_anon_hom:
  fixes A :: "'a set"
  shows "closed_restricted_rel
           (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)) (elections_\<A> A)
           (elections_\<K> (strong_unanimity_in A)
               :: ('a, 'v :: wellorder) Election set)"
proof (unfold closed_restricted_rel.simps restricted_rel.simps elections_\<K>.simps, safe)
  fix
    A\<^sub>1 A\<^sub>2 :: "'a set" and
    V V' :: "('v :: wellorder) set" and
    p p' :: "('a, ('v :: wellorder)) Profile" and
    w :: "'a"
  assume
    rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p')) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)" and
    cons: "(A\<^sub>1, V, p) \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
  \<comment> \<open>Unpack the relation: both elections lie in the carrier and have equal
 vote fractions.\<close>
  have E'_in_A: "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
       eq_fract: "\<forall> q. vote_fraction q (A\<^sub>1, V, p) = vote_fraction q (A\<^sub>2, V', p')"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  hence alts': "A\<^sub>2 = A" and
        fin_V': "finite V'" and
        wf': "profile V' A\<^sub>2 p'" and
        nonvoter': "\<forall> v. v \<notin> V' \<longrightarrow> p' v = {}"
    unfolding elections_\<A>.simps well_formed_elections_def
    by auto
  \<comment> \<open>Unpack the consensus membership of the source election.\<close>
  have cond: "strong_unanimity\<^sub>\<C> (A\<^sub>1, V, p) \<and> A\<^sub>1 = A
                \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})" and
       fin: "finite_profile V A\<^sub>1 p" and
       elect_E: "elect (rule_\<K> (strong_unanimity_in A)) V A\<^sub>1 p = {w}"
    using cons
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
    by (simp_all add: Let_def split: if_split_asm)
  from cond obtain r where all_vote: "\<forall> v \<in> V. p v = r"
    unfolding strong_unanimity\<^sub>\<C>.simps equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
    by blast
  have A_nonempty: "A \<noteq> {}" and V_nonempty: "V \<noteq> {}"
    using cond
    unfolding strong_unanimity\<^sub>\<C>.simps nonempty_set\<^sub>\<C>.simps nonempty_profile\<^sub>\<C>.simps
    by auto
  \<comment> \<open>Vote-fraction transfer: the common ballot has fraction 1 in E, hence in E'.\<close>
  have "vote_count r (A\<^sub>1, V, p) = card V"
  proof -
    have "{v \<in> V. p v = r} = V"
      using all_vote
      by blast
    thus ?thesis
      unfolding vote_count.simps
      by simp
     qed
  hence "vote_fraction r (A\<^sub>1, V, p) = 1"
    using fin V_nonempty card_gt_0_iff
    unfolding vote_fraction.simps
    by (simp add: eq_rat One_rat_def)
  hence fract_one': "vote_fraction r (A\<^sub>2, V', p') = 1"
    using eq_fract
    by metis
  hence V'_nonempty: "V' \<noteq> {}"
    unfolding vote_fraction.simps
    by fastforce
  have "vote_count r (A\<^sub>2, V', p') = card V'"
    using fract_one' fin_V' V'_nonempty card_gt_0_iff
    unfolding vote_fraction.simps
    by (simp add: eq_rat One_rat_def split: if_splits)
  hence all_vote': "\<forall> v \<in> V'. p' v = r"
    using fin_V' card_subset_eq[of V' "{v \<in> V'. p' v = r}"]
    unfolding vote_count.simps voters_\<E>.simps profile_\<E>.simps
    by auto
  \<comment> \<open>Hence E' satisfies the restricted consensus condition.\<close>
  have cond': "strong_unanimity\<^sub>\<C> (A\<^sub>2, V', p') \<and> A\<^sub>2 = A
                \<and> (\<forall> v. v \<notin> V' \<longrightarrow> p' v = {})"
    using all_vote' alts' nonvoter' A_nonempty V'_nonempty
    unfolding strong_unanimity\<^sub>\<C>.simps nonempty_set\<^sub>\<C>.simps
              nonempty_profile\<^sub>\<C>.simps equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
    by auto
  have fin': "finite_profile V' A\<^sub>2 p'"
    using fin alts' fin_V' wf' cond
    by simp
  \<comment> \<open>Same elected singleton: both elections run elect_first_module on the same ballot r.\<close>
  have least_V: "least V \<in> V" and least_V': "least V' \<in> V'"
    using V_nonempty V'_nonempty LeastI_ex ex_in_conv
    unfolding least.simps
    by metis+
  have "elect (rule_\<K> (strong_unanimity_in A)) V' A\<^sub>2 p' =
          {a \<in> A\<^sub>2. above (p' (least V')) a = {a}}"
    using cond'
    unfolding strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  also have "\<dots> = {a \<in> A\<^sub>1. above r a = {a}}"
    using all_vote' least_V' alts' cond
    by simp
  also have "\<dots> = elect (rule_\<K> (strong_unanimity_in A)) V A\<^sub>1 p"
    using cond all_vote least_V
    unfolding strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  finally have elect_E': "elect (rule_\<K> (strong_unanimity_in A)) V' A\<^sub>2 p' = {w}"
    using elect_E
    by simp
  \<comment> \<open>Assemble membership.\<close>
  have  "(A\<^sub>2, V', p') \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
    using cond' fin' elect_E' A_nonempty
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  thus "(A\<^sub>2, V', p') \<in> \<Union> (range (\<K>\<^sub>\<E> (strong_unanimity_in A)))"
    by blast
qed
    






end