theory Quotient_Swapwise_Rules_Helpers
  imports "Compositional_Structures/Basic_Modules/Component_Types/Quotient_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Quotients/Election_Quotients"
    "Compositional_Structures/Basic_Modules/Component_Types/Consensus"
    "Compositional_Structures/Basic_Modules/Elect_First_Module"
    "Kemeny_Rule"
    "Compositional_Structures/Basic_Modules/Component_Types/Consensus_Class"

begin

text \<open>
  We define a variant of strong unanimity that fixes the alternative set and
  requires empty ballots for all voters outside the voter set. This makes it
  easier to prove that the assumptions of the invar_dr lemmas hold for rules
  with a distance-rationalization set.
  TBD: We prove later that this restriction does not change the minimum
  distance to the consensus class, so it is interchangeable with the
  unrestricted strong unanimity.
\<close>

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
  \<comment> \<open>The common ballot has fraction 1 in E, hence in E'.\<close>
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
  \<comment> \<open>Both elections elect the same singleton: both elections run elect_first_module on the same ballot r.\<close>
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
  have  "(A\<^sub>2, V', p') \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
    using cond' fin' elect_E' A_nonempty
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  thus "(A\<^sub>2, V', p') \<in> \<Union> (range (\<K>\<^sub>\<E> (strong_unanimity_in A)))"
    by blast
qed
    

lemma strong_unanimity_invar_anon_hom:
  "is_symmetry (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity))
     (Invariance (Restr (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))
                        (elections_\<K> strong_unanimity)))"
proof (unfold is_symmetry.simps, intro allI impI)
  fix E E' :: "('a, 'v :: wellorder) Election"
  assume rel: "(E, E') \<in> Restr (anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV))
                                (elections_\<K> strong_unanimity)"
  obtain A V p where E_eq: "E = (A, V, p)"
    using prod_cases3 by blast
  obtain A' V' p' where E'_eq: "E' = (A', V', p')"
    using prod_cases3 by blast
  from rel have
    memE:  "E \<in> elections_\<K> strong_unanimity" and
    memE': "E' \<in> elections_\<K> strong_unanimity" and
    mem:   "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> UNIV)"
    by blast+
  \<comment> \<open>1. Both are strong-unanimity consensus elections.\<close>
  have cons_eq: "consensus_\<K> strong_unanimity = strong_unanimity\<^sub>\<C>"
    unfolding strong_unanimity_def
    by (simp add: Let_def)
  from memE obtain w where "(A, V, p) \<in> \<K>\<^sub>\<E> strong_unanimity w"
    unfolding E_eq elections_\<K>.simps
    by blast
  hence raw: "consensus_\<K> strong_unanimity (A, V, p) \<and> finite_profile V A p"
    unfolding \<K>\<^sub>\<E>.simps
    by blast
  hence consE: "strong_unanimity\<^sub>\<C> (A, V, p)"
    using cons_eq
    by metis
  from raw have profE: "profile V A p" and finV: "finite V"
    by simp_all

  from memE' obtain w' where "(A', V', p') \<in> \<K>\<^sub>\<E> strong_unanimity w'"
    unfolding E'_eq elections_\<K>.simps
    by blast
  hence raw': "consensus_\<K> strong_unanimity (A', V', p') \<and> finite_profile V' A' p'"
    unfolding \<K>\<^sub>\<E>.simps
    by blast
  hence consE': "strong_unanimity\<^sub>\<C> (A', V', p')"
    using cons_eq
    by metis
  from raw' have profE': "profile V' A' p'" and finV': "finite V'"
    by simp_all
  \<comment> \<open>2. Extract the two unanimously agreed rankings.\<close>
  from consE have V_ne: "V \<noteq> {}"
    by simp
  from consE obtain r where all_r: "\<forall> v \<in> V. p v = r"
    by auto
  from consE' have V'_ne: "V' \<noteq> {}"
    by simp
  from consE' obtain r' where all_r': "\<forall> v \<in> V'. p' v = r'"
    by auto
  \<comment> \<open>3. Both alternative sets equal UNIV, and vote fractions coincide.\<close>
  from mem have in_A: "E \<in> elections_\<A> UNIV" and in_A': "E' \<in> elections_\<A> UNIV"
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  hence A_eq: "A = UNIV" and A'_eq: "A' = UNIV"
    unfolding E_eq E'_eq elections_\<A>.simps
    by auto
  from mem have eq_frac:
    "\<forall> q. vote_fraction q (A, V, p) = vote_fraction q (A', V', p')"
    unfolding E_eq E'_eq anonymity_homogeneity\<^sub>\<R>.simps
    by blast
  \<comment> \<open>4. The agreed ranking of E has vote fraction 1, \<dots>\<close>
  have "{v \<in> V. p v = r} = V"
    using all_r
    by blast
  hence count_E: "vote_count r (A, V, p) = card V"
    by simp
  have "card V \<noteq> 0"
    using finV V_ne
    by (simp add: card_eq_0_iff)
  hence "Fract (int (card V)) (int (card V)) = 1"
    by (simp add: Fract_of_int_quotient)
  hence frac_E: "vote_fraction r (A, V, p) = 1"
    using count_E finV V_ne
    by simp
  \<comment> \<open>\<dots> so equal fractions force the agreed rankings to coincide.\<close>
  have r_eq: "r' = r"
  proof (rule ccontr)
    assume "r' \<noteq> r"
    with all_r' have "{v \<in> V'. p' v = r} = {}"
      by blast
    hence "vote_count r (A', V', p') = 0"
      by (simp add: card_eq_0_iff)
    hence "vote_fraction r (A', V', p') = 0"
      by (simp add: rat_number_collapse)
    moreover have "vote_fraction r (A', V', p') = 1"
      using eq_frac frac_E
      by metis
    ultimately show False
      by simp
  qed
  \<comment> \<open>5. Same ranking and same alternatives: elect-first is fully determined.\<close>
  have cond: "nonempty_set\<^sub>\<C> (A, V, p) \<and> nonempty_profile\<^sub>\<C> (A, V, p)
                \<and> equal_vote\<^sub>\<C>' r (A, V, p)"
    using all_r V_ne A_eq
    by simp
  have cond': "nonempty_set\<^sub>\<C> (A', V', p') \<and> nonempty_profile\<^sub>\<C> (A', V', p')
                \<and> equal_vote\<^sub>\<C>' r (A', V', p')"
    using all_r' V'_ne A'_eq r_eq
    by simp
  have det: "elect_first_module V A p = elect_first_module V' A' p'"
    using strong_unanimity'consensus_imp_elect_fst_mod_completely_determined
          profE profE' cond cond' A_eq A'_eq
    unfolding well_formed_def
    by metis
  \<comment> \<open>6. On consensus elections, the rule is exactly elect-first.\<close>
  have res_E: "fun\<^sub>\<E> (rule_\<K> strong_unanimity) E = elect_first_module V A p"
    using consE
    unfolding E_eq strong_unanimity_def
    by (simp add: Let_def)
  have res_E': "fun\<^sub>\<E> (rule_\<K> strong_unanimity) E' = elect_first_module V' A' p'"
    using consE'
    unfolding E'_eq strong_unanimity_def
    by (simp add: Let_def)
  show "(elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) E
      = (elect_r \<circ> fun\<^sub>\<E> (rule_\<K> strong_unanimity)) E'"
    using res_E res_E' det
    by simp
qed

subsection \<open> Simple lemma \<close>

text \<open>
  The votewise swap distance from a profile to a unanimous consensus profile
  equals the sum, over all cast ballots, of the number of voters who cast that
  ballot times the swap distance of that ballot to the consensus ballot.
\<close>
lemma swap_dist_counting_formula:
  fixes
    A :: "'a set" and
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin:      "finite V" and
    nonempty: "V \<noteq> {}"
  shows
    "votewise_distance swap l_one (A, V, p) (A, V, \<lambda> v. R) =
       ereal (\<Sum> r \<in> p ` V. vote_count r (A, V, p)
                            * card (pairwise_disagreements A r R))"
proof -

  \<comment> \<open>Unfold votewise_distance. Its guard holds since V is finite and non-epty\<close>
  have unfold_vwd:
    "votewise_distance swap l_one (A, V, p) (A, V, \<lambda> v. R) =
       l_one (map2 (\<lambda> q q'. swap (A, q) (A, q'))
                (to_list V p)
                (to_list V (\<lambda> v. R)))"
    using fin nonempty
    by simp

 \<comment> \<open>The second list is constantly R,
   so map2 collapses to a single map over sorted_list_of_set V.\<close>
   have collapse_map2:
    "map2 (\<lambda> q q'. swap (A, q) (A, q')) (to_list V p) (to_list V (\<lambda> v. R)) =
       map (\<lambda> v. swap (A, p v) (A, R)) (sorted_list_of_set V)"
  proof -
    have "map2 (\<lambda> q q'. swap (A, q) (A, q')) (map p xs) (map (\<lambda> v. R) xs) =
            map (\<lambda> v. swap (A, p v) (A, R)) xs" for xs
      by (induction xs) simp_all
    moreover have "to_list V p = map p (sorted_list_of_set V)"
      using fin
      by simp
    moreover have "to_list V (\<lambda> v. R) = map (\<lambda> v. R) (sorted_list_of_set V)"
      using fin
      by simp
    ultimately show ?thesis
      by metis
  qed

  \<comment> \<open>Unfold l_one and turn the list sum into a set sum over V,
      using that sorted_list_of_set V is distinct and enumerates V.\<close>

    have list_to_set_sum:
    "l_one (map (\<lambda> v. swap (A, p v) (A, R)) (sorted_list_of_set V)) =
       ereal (\<Sum> v \<in> V. card (pairwise_disagreements A (p v) R))"
  proof -
    let ?sl = "sorted_list_of_set V"
    let ?c = "\<lambda> v. card (pairwise_disagreements A (p v) R)"
    have "map (\<lambda> v. swap (A, p v) (A, R)) ?sl = map (\<lambda> v. ereal (?c v)) ?sl"
      by simp
    moreover have "l_one (map (\<lambda> v. ereal (?c v)) ?sl) =
                     sum_list (map (\<lambda> v. ereal (?c v)) ?sl)"
      by (simp add: sum_list_sum_nth atLeast0LessThan)
    moreover have "sum_list (map (\<lambda> v. ereal (?c v)) ?sl) = (\<Sum> v \<in> V. ereal (?c v))"
      using fin sum_list_distinct_conv_sum_set
      by (metis distinct_sorted_list_of_set set_sorted_list_of_set)
    ultimately show ?thesis
      by simp
  qed

    \<comment> \<open>Group the voters by their cast ballot: all voters with ballot r
      contribute the same cost, and there are vote_count r (A, V, p) of them.\<close>

    have regroup:
    "(\<Sum> v \<in> V. card (pairwise_disagreements A (p v) R)) =
       (\<Sum> r \<in> p ` V. vote_count r (A, V, p) * card (pairwise_disagreements A r R))"
  proof -
    let ?c = "\<lambda> r. card (pairwise_disagreements A r R)"
    have "(\<Sum> v \<in> V. ?c (p v)) =
            (\<Sum> r \<in> p ` V. \<Sum> v \<in> {v \<in> V. p v = r}. ?c (p v))"
      using fin
      by (rule sum.image_gen)
    also have "\<dots> = (\<Sum> r \<in> p ` V. \<Sum> v \<in> {v \<in> V. p v = r}. ?c r)"
      by (intro sum.cong refl) auto
    also have "\<dots> = (\<Sum> r \<in> p ` V. card {v \<in> V. p v = r} * ?c r)"
      by simp
    also have "\<dots> = (\<Sum> r \<in> p ` V. vote_count r (A, V, p) * ?c r)"
      by simp
    finally show ?thesis .
  qed

 show ?thesis
    unfolding unfold_vwd collapse_map2 list_to_set_sum regroup
    by (simp only: of_nat_mult)
qed


text \<open>
  To prove that the swap distance to strong consensus classes is simple, we
  need an "engine lemma": if two elections lie in the same
  anonymity-homogeneity class, they have the same average distance to all
  consensus classes and hence yield the same result. With that, the simple
  lemma becomes straightforward.
\<close>

text \<open>
  Helper lemmas for the engine lemma swap_dist_avg_hom_invar.
\<close>

lemma vote_count_mem_image_iff:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    r :: "'a Preference_Relation"
  assumes fin: "finite V"
  shows "r \<in> image p V \<longleftrightarrow> vote_count r (A, V, p) \<noteq> 0"
proof -
  have "vote_count r (A, V, p) = card {v \<in> V. p v = r}"
    by simp
  thus ?thesis
    using fin
    by (auto simp: card_eq_0_iff)
qed

lemma image_eq_of_cross:
  fixes
    A :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile"
  assumes
    fin:    "finite V" and
    fin':   "finite V'" and
    n_pos:  "0 < card V" and
    n'_pos: "0 < card V'" and
    cross:  "\<forall> r. vote_count r (A, V, p) * card V'
                    = vote_count r (A, V', p') * card V"
  shows "p ` V = p' ` V'"
proof (rule Set.equalityI; rule subsetI)
  fix r assume "r \<in> p ` V"
  hence vc: "vote_count r (A, V, p) \<noteq> 0"
    using fin vote_count_mem_image_iff by blast
  have cross_r: "vote_count r (A, V, p) * card V'
                   = vote_count r (A, V', p') * card V"
    using cross by blast
  have "vote_count r (A, V, p) * card V' \<noteq> 0"
    using vc n'_pos by simp
  hence "vote_count r (A, V', p') * card V \<noteq> 0"
    by (metis cross_r)
  hence "vote_count r (A, V', p') \<noteq> 0"
    using n_pos by simp
  thus "r \<in> p' ` V'"
    using fin' vote_count_mem_image_iff by blast
next
  fix r assume "r \<in> p' ` V'"
  hence vc': "vote_count r (A, V', p') \<noteq> 0"
    using fin' vote_count_mem_image_iff by blast
  have cross_r: "vote_count r (A, V, p) * card V'
                   = vote_count r (A, V', p') * card V"
    using cross by blast
  have "vote_count r (A, V', p') * card V \<noteq> 0"
    using vc' n_pos by simp
  hence "vote_count r (A, V, p) * card V' \<noteq> 0"
    using cross_r by simp
  hence "vote_count r (A, V, p) \<noteq> 0"
    using n'_pos by simp
  thus "r \<in> p ` V"
    using fin vote_count_mem_image_iff by blast
qed

text \<open>
  Homogeneity half of the engine lemma: equal vote fractions imply equal
  normalized swap distance to the unanimity-R election on one's own voter set.
\<close>


lemma swap_dist_avg_hom_invar:
  fixes
    A :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin:      "finite V"      and fin':      "finite V'" and
    nonempty: "V \<noteq> {}"        and nonempty': "V' \<noteq> {}" and
    eq_frac:  "\<forall> r. vote_fraction r (A, V, p) = vote_fraction r (A, V', p')"
  shows
    "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)
       = votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)"
proof -
  let ?raw  = "votewise_distance swap l_one (A, V, p) (A, V, \<lambda> v. R)"
  let ?raw' = "votewise_distance swap l_one (A, V', p') (A, V', \<lambda> v. R)"
  let ?n    = "card V"
  let ?n'   = "card V'"

  define cost :: "'a Preference_Relation \<Rightarrow> real" where
    "cost = (\<lambda> r. real (card (pairwise_disagreements A r R)))"

  have n_pos:  "0 < ?n"  using fin  nonempty  card_gt_0_iff by blast
  have n'_pos: "0 < ?n'" using fin' nonempty' card_gt_0_iff by blast

 \<comment> \<open>Step 1: apply the counting formula and rewrite the nat sum as a real sum.\<close>
  have step1: "?raw = ereal (\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r)"
  proof -
    have "?raw = ereal (\<Sum> r \<in> p ` V.
                   vote_count r (A, V, p) * card (pairwise_disagreements A r R))"
      by (rule swap_dist_counting_formula[OF fin nonempty])
    also have "\<dots> = ereal (\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r)"
      by (simp add: cost_def)
    finally show ?thesis .
  qed

  have step1': "?raw' = ereal (\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r)"
  proof -
    have "?raw' = ereal (\<Sum> r \<in> p' ` V'.
                    vote_count r (A, V', p') * card (pairwise_disagreements A r R))"
      by (rule swap_dist_counting_formula[OF fin' nonempty'])
    also have "\<dots> = ereal (\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r)"
      by (simp add: cost_def)
    finally show ?thesis .
  qed

  have raw_fin:  "?raw  \<noteq> \<infinity>" using step1  by simp
  have raw'_fin: "?raw' \<noteq> \<infinity>" using step1' by simp

  \<comment> \<open>Step 2: l_one_avg is l_one divided by card V.\<close>
  have step2: "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)
                 = ?raw / ereal (real ?n)"
  proof -
    let ?xs = "map2 (\<lambda> q q'. swap (A, q) (A, q'))
                    (to_list V p) (to_list V (\<lambda> v. R))"
    have vwd_avg: "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R) = l_one_avg ?xs"
      using fin nonempty by simp
    have vwd_raw: "?raw = l_one ?xs"
      using fin nonempty by simp
    have len_xs: "length ?xs = ?n"
      using fin by simp
    have ne_xs: "?xs \<noteq> []"
      using len_xs n_pos fin by auto
    show ?thesis
      unfolding vwd_avg
      by (simp add: fin nonempty)
  qed

  have step2': "votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)
                  = ?raw' / ereal (real ?n')"
  proof -
    let ?xs' = "map2 (\<lambda> q q'. swap (A, q) (A, q'))
                     (to_list V' p') (to_list V' (\<lambda> v. R))"
    have vwd_avg': "votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)
                      = l_one_avg ?xs'"
      using fin' nonempty' by simp
    have vwd_raw': "?raw' = l_one ?xs'"
      using fin' nonempty' by simp
    have len_xs': "length ?xs' = ?n'"
      using fin' by simp
    have ne_xs': "?xs' \<noteq> []"
      using len_xs' n'_pos fin' by auto
        show ?thesis
      unfolding vwd_avg'
      by (simp add: fin' nonempty')
  qed

 \<comment> \<open>Step 3a: equal vote fractions give a cross-multiplication identity on counts.
      Both sides of vote_fraction's if-guard are in the true branch here.\<close>
  have cross: "\<forall> r. vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
  proof
    fix r
    have eq: "vote_fraction r (A, V, p) = vote_fraction r (A, V', p')"
      using eq_frac by blast
    hence "Fract (vote_count r (A, V, p)) ?n
             = Fract (vote_count r (A, V', p')) ?n'"
      using fin nonempty fin' nonempty'
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence "int (vote_count r (A, V, p)) * int ?n'
             = int (vote_count r (A, V', p')) * int ?n"
      using n_pos n'_pos
      by (simp add: eq_rat)
    thus "vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
      by (metis of_nat_eq_iff of_nat_mult)
  qed
  have img_eq: "p ` V = p' ` V'"
    by (rule image_eq_of_cross[OF fin fin' n_pos n'_pos cross])

  \<comment> \<open>Step 3b: distribute the factor, rewrite each summand via cross, collect.\<close>
  have raw_cross:
    "(\<Sum> r \<in> p ` V.  real (vote_count r (A, V, p))  * cost r) * real ?n'
   = (\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r) * real ?n"
  proof -
    have "(\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r) * real ?n'
            = (\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r * real ?n')"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum> r \<in> p ` V. real (vote_count r (A, V', p')) * cost r * real ?n)"
    proof (intro sum.cong refl)
      fix r assume "r \<in> p ` V"
      have "vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
        using cross by blast
      hence "real (vote_count r (A, V, p)) * real ?n'
               = real (vote_count r (A, V', p')) * real ?n"
        by (metis of_nat_mult)
      thus "real (vote_count r (A, V, p))  * cost r * real ?n'
              = real (vote_count r (A, V', p')) * cost r * real ?n"
          by (metis mult.assoc mult.commute)
    qed simp (* close remaining refl statement*)
    also have "\<dots> = (\<Sum> r \<in> p ` V. real (vote_count r (A, V', p')) * cost r) * real ?n"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r) * real ?n"
      by (simp add: img_eq)
    finally show ?thesis .
  qed

\<comment> \<open>Step 3c: cancel the factors and lift the equality into ereal.\<close>
  show ?thesis
  proof -
    let ?s  = "\<Sum> r \<in> p ` V.  real (vote_count r (A, V, p))  * cost r"
    let ?s' = "\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r"
    have real_eq: "?s / real ?n = ?s' / real ?n'"
      using raw_cross n_pos n'_pos
      by (auto simp: field_simps)
    have "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)
            = ereal (?s / real ?n)"
      using step1 step2 n_pos by simp
    also have "\<dots> = ereal (?s' / real ?n')"
      by (simp only: real_eq)
    also have "\<dots> = votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)"
      using step1' step2' n'_pos by simp
    finally show ?thesis .
  qed
qed

text \<open>
  The "engine" lemma phrased on the relation itself. Since
  anonymity_homogeneity R is defined by equal vote fractions rather than
  generated by renamings and copies, swap_dist_avg_hom_invar already covers
  renaming-invariance: renaming preserves all vote fractions. The only new
  content is the case of empty voter sets, which the engine lemma excludes
  but the relation permits.
\<close>

lemma swap_dist_avg_invar_anon_hom:
  fixes
    A A\<^sub>1 A\<^sub>2 :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p'))
                  \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "votewise_distance swap l_one_avg (A\<^sub>1, V, p) (A\<^sub>1, V, \<lambda> v. R)
       = votewise_distance swap l_one_avg (A\<^sub>2, V', p') (A\<^sub>2, V', \<lambda> v. R)"
proof -
  \<comment> \<open>1. Unpack the relation: carrier membership and equal vote fractions.\<close>
  have inA:  "(A\<^sub>1, V, p) \<in> elections_\<A> A" and
       inA': "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
       eq_frac: "\<forall> q. vote_fraction q (A\<^sub>1, V, p)
                        = vote_fraction q (A\<^sub>2, V', p')"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+

  \<comment> \<open>2. Carrier facts: fixed alternative set, finite voter sets.\<close>
  have alts: "A\<^sub>1 = A" and alts': "A\<^sub>2 = A" and
       fin: "finite V" and fin': "finite V'"
    using inA inA'
    unfolding elections_\<A>.simps
    by auto

  \<comment> \<open>3. Emptiness transfers between the two voter sets.\<close>
  have empty_to: "V \<noteq> {} \<Longrightarrow> V' \<noteq> {}"
  proof -
    assume ne: "V \<noteq> {}"
  \<comment> \<open>Any voter's ballot is cast at least once, so its fraction is positive.\<close>
    obtain v where v_in: "v \<in> V" using ne by blast
    have "vote_count (p v) (A\<^sub>1, V, p) \<noteq> 0"
      using fin v_in vote_count_mem_image_iff by blast
        hence num_pos: "0 < vote_count (p v) (A\<^sub>1, V, p)"
      by simp
    have den_pos: "0 < card V"
      using fin ne card_gt_0_iff by blast
    have "0 < Fract (int (vote_count (p v) (A\<^sub>1, V, p))) (int (card V))"
      using num_pos den_pos
      by (simp add: zero_less_Fract_iff)
    hence "vote_fraction (p v) (A\<^sub>1, V, p) > 0"
      using fin ne
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence pos': "vote_fraction (p v) (A\<^sub>2, V', p') > 0"
      using eq_frac by metis
   \<comment> \<open>An empty electorate would give fraction 0 -> contradiction.\<close>
    show "V' \<noteq> {}"
    proof
      assume "V' = {}"
       hence "vote_fraction (p v) (A\<^sub>2, V', p') = 0"
       unfolding vote_fraction.simps voters_\<E>.simps
       by (simp add: rat_number_collapse)
      thus False using pos' by simp
    qed
  qed
  have empty_from: "V' \<noteq> {} \<Longrightarrow> V \<noteq> {}"
 \<comment> \<open>analogous to  empty_to, with primed and unprimed roles swapped\<close>
      proof -
    assume ne': "V' \<noteq> {}"
    obtain v where v_in: "v \<in> V'" using ne' by blast
    have "vote_count (p' v) (A\<^sub>2, V', p') \<noteq> 0"
      using fin' v_in vote_count_mem_image_iff by blast
    hence num_pos: "0 < vote_count (p' v) (A\<^sub>2, V', p')"
      by simp
    have den_pos: "0 < card V'"
      using fin' ne' card_gt_0_iff by blast
    have "0 < Fract (int (vote_count (p' v) (A\<^sub>2, V', p'))) (int (card V'))"
      using num_pos den_pos
      by (simp add: zero_less_Fract_iff)
    hence pos': "vote_fraction (p' v) (A\<^sub>2, V', p') > 0"
      using fin' ne'
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence pos: "vote_fraction (p' v) (A\<^sub>1, V, p) > 0"
      using eq_frac by metis
    show "V \<noteq> {}"
    proof
      assume "V = {}"
      hence "vote_fraction (p' v) (A\<^sub>1, V, p) = 0"
        unfolding vote_fraction.simps voters_\<E>.simps
        by (simp add: rat_number_collapse)
      thus False using pos by simp
    qed
  qed

  \<comment> \<open>4. Case split: both voter sets  empty or both nonempty.\<close>
  show ?thesis
  proof (cases "V = {}")
    case True
    hence V'_empty: "V' = {}" using empty_from by blast
     \<comment> \<open>The profiles only enter via to_list, and to_list {} f = [] for any f,
        so both sides are the same computation over A.\<close>
    show ?thesis
      using True V'_empty alts alts'
      by simp
  next
    case False
    hence ne': "V' \<noteq> {}" using empty_to by blast
    \<comment> \<open>Rewrite both alternative sets to A, then the engine lemma
        closes it.\<close>
    have "\<forall> q. vote_fraction q (A, V, p) = vote_fraction q (A, V', p')"
      using eq_frac alts alts' by simp
    thus ?thesis
      using swap_dist_avg_hom_invar[OF fin fin' False ne'] alts alts'
      by metis
  qed
qed

text \<open>
  One unanimity class: all elections over A in which a finite, nonempty
  electorate unanimously votes R, with empty ballots outside the electorate.
  Conceptually, each such class is a single anonymity-homogeneity class,
  since every member gives R the vote fraction 1. The strong_unanimity_in
  consensus set decomposes into these classes, one per ranking R; that
  decomposition is proved later.
\<close>

definition unanimity_class :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> ('a, 'v) Election set" where
  "unanimity_class A R \<equiv>
     {E. alternatives_\<E> E = A
       \<and> finite (voters_\<E> E)
       \<and> voters_\<E> E \<noteq> {}
       \<and> (\<forall> v \<in> voters_\<E> E. profile_\<E> E v = R)
       \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {})}"

text \<open>
  Collapse lemma: the infimum of distances from (A, V, p) to the whole
  unanimity-R class is the distance to the unanimity-R election on its own
  voter set. Members over other voter sets are at distance \<infinity> by
  votewise_distance's guard, and the member over V attains exactly this
  distance.
\<close>

lemma swap_dist_avg_collapse:
  fixes
    A :: "'a set" and
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    ne:  "V \<noteq> {}"
  shows "Inf (votewise_distance swap l_one_avg (A, V, p) ` unanimity_class A R)
           = votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)"
    (is "Inf (?d ` ?B) = ?s")
proof -
  \<comment> \<open>The distinguished class member: unanimity-R on our own voter set,
      with empty ballots outside.\<close>
  define b\<^sub>0 :: "('a, 'v) Election" where
    "b\<^sub>0 = (A, V, \<lambda> v. if v \<in> V then R else {})"

  have b0_mem: "b\<^sub>0 \<in> unanimity_class A R"
    using fin ne
    unfolding b\<^sub>0_def unanimity_class_def
    by simp

  \<comment> \<open>Computational main step: to_list only evaluates a profile on V, so any
      profile equal to R on V is indistinguishable from the constant-R profile.\<close>
  have to_list_R: "to_list V q = to_list V (\<lambda> v. R)"
    if "\<forall> v \<in> V. q v = R" for q :: "('a, 'v) Profile"
  proof -
    have "to_list V q = map q (sorted_list_of_set V)"
      using fin by simp
    also have "\<dots> = map (\<lambda> v. R) (sorted_list_of_set V)"
      using that fin by (intro map_cong) auto
    also have "\<dots> = to_list V (\<lambda> v. R)"
      using fin by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Hence the distance to ANY same-voter-set class member is the score.\<close>
  have same_V_dist: "?d (A, V, q) = ?s"
    if q_R: "\<forall> v \<in> V. q v = R" for q :: "('a, 'v) Profile"
  proof -
    have "?d (A, V, q)
            = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y))
                              (to_list V p) (to_list V q))"
      using fin by simp
    also have "\<dots> = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y))
                                   (to_list V p) (to_list V (\<lambda> v. R)))"
      by (simp only: to_list_R[OF q_R])
    also have "\<dots> = ?s"
      using fin by simp
    finally show ?thesis .
  qed

  have diff_V_dist: "?d (A', W, q) = \<infinity>"
    if "W \<noteq> V" for A' :: "'a set" and W :: "'v set" and q :: "('a, 'v) Profile"
    using that
    by simp

  have lb: "?s \<le> x" if x_in: "x \<in> ?d ` unanimity_class A R" for x
  proof -
    from x_in obtain b where b_mem: "b \<in> unanimity_class A R" and x_eq: "x = ?d b"
      by blast
    obtain A' W q where b_eq: "b = (A', W, q)"
      using prod_cases3 by blast
    show ?thesis
       proof (cases "W = V")
      case True
      have A'_eq: "A' = A" and q_R: "\<forall> v \<in> V. q v = R"
        using b_mem True
        unfolding b_eq unanimity_class_def
        by simp_all
      have "x = ?d (A, V, q)"
        using x_eq
        unfolding b_eq True A'_eq
        by simp
      also have "\<dots> = ?s"
        by (rule same_V_dist[OF q_R])
      finally show ?thesis
        by simp
    next
      case False
      have "x = \<infinity>"
        using x_eq diff_V_dist False
        unfolding b_eq
        by simp
      thus ?thesis
        by simp
    qed
  qed

  have "?d b\<^sub>0 = ?s"
    unfolding b\<^sub>0_def
    by (intro same_V_dist) simp
  hence attained: "?s \<in> ?d ` unanimity_class A R"
    using b0_mem
    by (metis image_eqI)

  have "Inf (?d ` unanimity_class A R) \<le> ?s"
    using attained by (rule Inf_lower)
  moreover have "?s \<le> Inf (?d ` unanimity_class A R)"
    using lb by (blast intro: Inf_greatest)
  ultimately show ?thesis
    by simp
qed

subsection \<open> P1: simplicity of the normalized swap distance \<close>

(* Helper A: a unanimity election's vote-fraction profile is the
   indicator of its common ballot.
   True branch: copy of the frac_E block in strong_unanimity_invar_anon_hom.
   False branch: copy of the r_eq contradiction block there. *)
lemma unanimity_vote_fraction:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    R q :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    ne: "V \<noteq> {}" and
    unan: "\<forall> v \<in> V. p v = R"
  shows "vote_fraction q (A, V, p) = (if q = R then 1 else 0)"
proof (cases "q = R")
  case True
  have "{v \<in> V. p v = q} = V"
    using unan True by blast
  hence count: "vote_count q (A, V, p) = card V"
    by simp
  have "card V \<noteq> 0"
    using fin ne by (simp add: card_eq_0_iff)
  hence "Fract (int (card V)) (int (card V)) = 1"
    by (simp add: Fract_of_int_quotient)
  thus ?thesis
    using count fin ne True by simp
next
  case False
  hence "{v \<in> V. p v = q} = {}"
    using unan by auto
  hence "vote_count q (A, V, p) = 0"
    by (simp add: card_eq_0_iff)
  thus ?thesis
    using False by (simp add: rat_number_collapse)
qed

(* Helper B: fraction one forces unanimity.
   Both steps are copies from strong_unanimity_in_closed_under_anon_hom
   (the V'_nonempty and all_vote' blocks). *)
lemma vote_fraction_one_imp_unanimous:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    frac1: "vote_fraction R (A, V, p) = 1"
  shows "V \<noteq> {} \<and> (\<forall> v \<in> V. p v = R)"
proof -
  have ne: "V \<noteq> {}"
    using frac1
    unfolding vote_fraction.simps
    by fastforce
  have "vote_count R (A, V, p) = card V"
    using frac1 fin ne card_gt_0_iff
    unfolding vote_fraction.simps
    by (simp add: eq_rat One_rat_def split: if_splits)
  hence "\<forall> v \<in> V. p v = R"
    using fin card_subset_eq[of V "{v \<in> V. p v = R}"]
    unfolding vote_count.simps voters_\<E>.simps profile_\<E>.simps
    by auto
  thus ?thesis
    using ne by blast
qed


(* Helper C: the score doesn't care which unanimity-R partner it
   measures against, as long as the voter set is its own.
   This is same_V_dist + to_list_R from swap_dist_avg_collapse,
   lifted out and generalized; the proof is the same three-step
   calculation. Optional cleanup for item 10: make the collapse
   lemma cite this instead of its local copy. *)
lemma swap_dist_avg_to_unanimity:
  fixes
    A :: "'a set" and
    V :: "'v :: linorder set" and
    p q :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    qR: "\<forall> v \<in> V. q v = R"
  shows "votewise_distance swap l_one_avg (A, V, p) (A, V, q)
       = votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)"
proof -
  have to_list_R: "to_list V q = to_list V (\<lambda> v. R)"
    proof -
      have "to_list V q = map q (sorted_list_of_set V)"
        using fin by simp
also have "\<dots> = map (\<lambda> v. R) (sorted_list_of_set V)"
      using qR fin by (intro map_cong) auto
    also have "\<dots> = to_list V (\<lambda> v. R)"
      using fin by simp
    finally show ?thesis .
  qed
have "votewise_distance swap l_one_avg (A, V, p) (A, V, q)
          = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y))
                            (to_list V p) (to_list V q))"
  using fin by simp
also have "\<dots> = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y))
                                 (to_list V p) (to_list V (\<lambda> v. R)))"
  by (simp only: to_list_R)
also have "\<dots> = votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)"
    using fin by simp
  finally show ?thesis .
qed


(* Helper D: emptiness transfers along the relation.
   Extraction of empty_to / empty_from from swap_dist_avg_invar_anon_hom. *)

lemma anon_hom_empty_iff:
  fixes
    A A\<^sub>1 A\<^sub>2 :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile"
  assumes rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p')) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "(V = {}) = (V' = {})"
proof -
  have inA: "(A\<^sub>1, V, p) \<in> elections_\<A> A" and
      inA':  "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
      eq_frac: "\<forall> q. vote_fraction q (A\<^sub>1, V, p) = vote_fraction q (A\<^sub>2, V', p')"

    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+

  have fin: "finite V" and fin': "finite V'"
    using inA inA'
    unfolding elections_\<A>.simps
    by auto

  have empty_to: "V \<noteq> {} \<Longrightarrow> V' \<noteq> {}"
  proof -
    assume ne: "V \<noteq> {}"
    obtain v where v_in: "v \<in> V" using ne by blast
    have "vote_count (p v) (A\<^sub>1, V, p) \<noteq> 0"
      using fin v_in vote_count_mem_image_iff by blast
     hence num_pos: "0 < vote_count (p v) (A\<^sub>1, V, p)"
       by simp
     have den_pos: "0 < card V"
       using fin ne card_gt_0_iff by blast
     have "0 < Fract (int (vote_count (p v) (A\<^sub>1, V, p))) (int (card V))"
       using num_pos den_pos
       by (simp add: zero_less_Fract_iff)
    hence "vote_fraction (p v) (A\<^sub>1, V, p) > 0"
      using fin ne
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence pos': "vote_fraction (p v) (A\<^sub>2, V', p') > 0"
      using eq_frac by metis
    show "V' \<noteq> {}"
    proof
      assume "V' = {}"
      hence "vote_fraction (p v) (A\<^sub>2, V', p') = 0"
        unfolding vote_fraction.simps voters_\<E>.simps
        by (simp add: rat_number_collapse)
      thus False using pos' by simp
    qed
  qed
  have empty_from: "V' \<noteq> {} \<Longrightarrow> V \<noteq> {}"
  proof -
    assume ne': "V' \<noteq> {}"
    obtain v where v_in: "v \<in> V'" using ne' by blast
    have "vote_count (p' v) (A\<^sub>2, V', p') \<noteq> 0"
      using fin' v_in vote_count_mem_image_iff by blast
    hence num_pos: "0 < vote_count (p' v) (A\<^sub>2, V', p')"
      by simp
    have den_pos: "0 < card V'"
      using fin' ne' card_gt_0_iff by blast
    have "0 < Fract (int (vote_count (p' v) (A\<^sub>2, V', p'))) (int (card V'))"
      using num_pos den_pos
      by (simp add: zero_less_Fract_iff)
    hence pos': "vote_fraction (p' v) (A\<^sub>2, V', p') > 0"
      using fin' ne'
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence pos: "vote_fraction (p' v) (A\<^sub>1, V, p) > 0"
      using eq_frac by metis
    show "V \<noteq> {}"
    proof
      assume "V = {}"
      hence "vote_fraction (p' v) (A\<^sub>1, V, p) = 0"
        unfolding vote_fraction.simps voters_\<E>.simps
        by (simp add: rat_number_collapse)
      thus False using pos by simp
    qed
  qed
  show ?thesis
    using empty_to empty_from by blast
qed


lemma swap_l_one_avg_simple:
  fixes A :: "'a set"
  shows "simple_on
    (elections_\<K> (strong_unanimity_in A))
    (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
    (elections_\<A> A)
    (votewise_distance swap l_one_avg
      :: ('a, 'v :: wellorder) Election Distance)"
   (is "simple_on ?Y ?r ?X ?d")

proof (unfold simple_on.simps, intro ballI)
  fix AC :: "('a, 'v) Election set"
  assume AC_cls: "AC \<in> ?X // ?r"
  have equiv: "equiv ?X ?r"
    by (rule anon_hom_equiv)
  \<comment> \<open>the class is nonempty: pick ANY representative\<close>
  have "AC \<noteq> {}"
    using AC_cls equiv in_quotient_imp_non_empty by blast
  then obtain a where a_in: "a \<in> AC"
    by blast

obtain A\<^sub>a V\<^sub>a p\<^sub>a where a_eq: "a = (A\<^sub>a, V\<^sub>a, p\<^sub>a)"
    using prod_cases3 by blast
  \<comment> \<open>every class member is related to a, and a to itself\<close>
obtain x\<^sub>0 where AC_eq: "AC = ?r `` {x\<^sub>0}"
    using AC_cls by (blast elim: quotientE)
  have "(x\<^sub>0, a) \<in> ?r"
    using a_in AC_eq by blast
  hence AC_img: "AC = ?r `` {a}"
    using AC_eq equiv equiv_class_eq by metis
  have "AC \<subseteq> ?X"
    using AC_cls equiv Union_quotient Union_upper by metis
  hence a_carrier: "a \<in> ?X"
    using a_in by blast
  hence a_alts: "A\<^sub>a = A" and a_fin: "finite V\<^sub>a"
    unfolding a_eq elections_\<A>.simps
    by auto
  have a_eq': "a = (A, V\<^sub>a, p\<^sub>a)"
    using a_eq a_alts
    by simp

  show "\<exists> x \<in> AC. \<forall> BC \<in> ?Y // ?r.
    distance_infimum\<^sub>\<Q> ?d AC BC = Inf {?d x b | b. b \<in> BC}"
proof (rule bexI[OF _ a_in], intro ballI)
    fix BC :: "('a, 'v) Election set"
    assume BC_cls: "BC \<in> ?Y // ?r"
\<comment> \<open>STEP 1: unpack the consensus class. Its seed b₀ is a strong
        unanimity election; extract its common ballot R.\<close>
    obtain b\<^sub>0 where b0_Y: "b\<^sub>0 \<in> ?Y" and BC_img: "BC = ?r `` {b\<^sub>0}"
      using BC_cls by (blast elim: quotientE)
    obtain A\<^sub>0 V\<^sub>0 p\<^sub>0 where b0_eq: "b\<^sub>0 = (A\<^sub>0, V\<^sub>0, p\<^sub>0)"
      using prod_cases3 by blast

    from b0_Y obtain w where b0_cons: "b\<^sub>0 \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
      unfolding elections_\<K>.simps by blast
    have cond0: "strong_unanimity\<^sub>\<C> (A\<^sub>0, V\<^sub>0, p\<^sub>0) \<and> A\<^sub>0 = A
                  \<and> (\<forall> v. v\<notin>  V\<^sub>0 \<longrightarrow>  p\<^sub>0 v = {})" and
        fin0: "finite_profile V\<^sub>0 A\<^sub>0 p\<^sub>0"
      using b0_cons
      unfolding b0_eq \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
      by (simp_all add: Let_def split: if_split_asm)

    from cond0 obtain R where R_unan: "\<forall> v \<in> V\<^sub>0. p\<^sub>0 v = R"
      unfolding strong_unanimity\<^sub>\<C>.simps equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
      by blast
    have b0_fin: "finite V\<^sub>0"
      using fin0 by simp
    have b0_ne: "V\<^sub>0 \<noteq> {}"
      using cond0
      unfolding strong_unanimity\<^sub>\<C>.simps nonempty_set\<^sub>\<C>.simps nonempty_profile\<^sub>\<C>.simps
      by auto
    have b0_alts: "A\<^sub>0 = A"
      using cond0 by simp

have b0_carrier: "b\<^sub>0 \<in> ?X"
  using b0_Y strong_unanimity_elections_subset by blast

have b0_in_BC: "b\<^sub>0 \<in> BC"
      using BC_img b0_carrier equiv
      unfolding equiv_def refl_on_def
      by blast

\<comment> \<open>STEP 2: characterize the members of BC: all unanimity-R,
        finite, nonempty, over A, in the carrier.\<close>
    have BC_char: "\<exists> V\<^sub>b p\<^sub>b. b = (A, V\<^sub>b, p\<^sub>b) \<and> finite V\<^sub>b \<and> V\<^sub>b \<noteq> {}
                     \<and> (\<forall> v \<in> V\<^sub>b. p\<^sub>b v = R) \<and> b \<in> ?X"

    if b_in: "b \<in> BC" for b
       proof -
      obtain A\<^sub>b V\<^sub>b p\<^sub>b where b_eq: "b = (A\<^sub>b, V\<^sub>b, p\<^sub>b)"
        using prod_cases3 by blast
      have b_rel: "(b\<^sub>0, b) \<in> ?r"
        using b_in BC_img by blast
      have b_X: "b \<in> ?X" and
           eq_frac_b: "\<forall> q. vote_fraction q (A\<^sub>0, V\<^sub>0, p\<^sub>0)
                              = vote_fraction q (A\<^sub>b, V\<^sub>b, p\<^sub>b)"
        using b_rel
        unfolding b0_eq b_eq anonymity_homogeneity\<^sub>\<R>.simps
        by blast+
      have b_alts: "A\<^sub>b = A" and b_fin: "finite V\<^sub>b"
        using b_X
        unfolding b_eq elections_\<A>.simps
        by auto
      have "vote_fraction R (A\<^sub>0, V\<^sub>0, p\<^sub>0) = 1"
        using unanimity_vote_fraction[OF b0_fin b0_ne R_unan]
        by simp
      hence "vote_fraction R (A\<^sub>b, V\<^sub>b, p\<^sub>b) = 1"
        using eq_frac_b by metis
      hence "V\<^sub>b \<noteq> {} \<and> (\<forall> v \<in> V\<^sub>b. p\<^sub>b v = R)"
        using vote_fraction_one_imp_unanimous[OF b_fin] by blast
      thus ?thesis
        using b_eq b_alts b_fin b_X by blast
    qed


  show "distance_infimum\<^sub>\<Q> ?d AC BC = Inf {?d a b | b. b \<in> BC}"
  proof (cases "V\<^sub>a = {}")
    case False
  \<comment> \<open>STEP 3 (main case): the one-sided Inf from ANY finite nonempty
          x over A collapses to x's score against R.\<close>
        \<comment> \<open>(i) lower bound via the collapse lemma:
            BC \<subseteq> unanimity_class A R  (by BC_char; carrier gives
            the empty-outside condition), hence
            ?d x ` BC \<subseteq> ?d x ` unanimity_class A R, hence by
            Inf_superset_mono and swap_dist_avg_collapse[OF x_fin x_ne]:
            score \<le> Inf (?d x ` BC).
            Conversion: {?d x b | b. b \<in> BC} = ?d x ` BC is
            Setcompr_eq_image.\<close>
        \<comment> \<open>(ii) attainment: bx := (A, V x, \<lambda> v. if v \<in> V x then R else {})
            lies in BC: it is related to b0 because both are in the
            carrier and both have fraction profile (indicator of R),
            by unanimity_vote_fraction on each side.
            Its distance from x is the score, by
            swap_dist_avg_to_unanimity.\<close>
        \<comment> \<open>(iii) Inf_lower + antisym (or by order), as in the
            collapse lemma's step F.\<close>
  have one_sided:
        "Inf {?d (A, V\<^sub>x, p\<^sub>x) b | b. b \<in> BC}
           = ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
        if x_fin: "finite V\<^sub>x" and x_ne: "V\<^sub>x \<noteq> {}"
         for V\<^sub>x :: "'v set" and p\<^sub>x :: "('a, 'v) Profile"
  proof -
    have BC_sub: "BC \<subseteq> unanimity_class A R"
        proof
          fix b assume "b \<in> BC"
          then obtain V\<^sub>b p\<^sub>b where b_eq: "b = (A, V\<^sub>b, p\<^sub>b)" and
            b_fin: "finite V\<^sub>b" and b_ne: "V\<^sub>b \<noteq> {}" and
            b_unan: "\<forall> v \<in> V\<^sub>b. p\<^sub>b v = R" and b_X: "b \<in> ?X"
            using BC_char by blast
          have "\<forall> v. v \<notin> V\<^sub>b \<longrightarrow> p\<^sub>b v = {}"
            using b_X
            unfolding b_eq elections_\<A>.simps well_formed_elections_def
            by auto
          thus "b \<in> unanimity_class A R"
            using b_fin b_ne b_unan
            unfolding b_eq unanimity_class_def
            by simp
        qed
        have lower: "?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)
                       \<le> Inf (?d (A, V\<^sub>x, p\<^sub>x) ` BC)"
          using swap_dist_avg_collapse[OF x_fin x_ne] BC_sub
                Inf_superset_mono image_mono
          by metis

        define b\<^sub>x :: "('a, 'v) Election" where
          "b\<^sub>x = (A, V\<^sub>x, \<lambda> v. if v \<in> V\<^sub>x then R else {})"
        have unan_bx: "\<forall> v \<in> V\<^sub>x.
              (if v \<in> V\<^sub>x then R else ({} :: 'a Preference_Relation)) = R"
          by simp

        have unan_bx: "\<forall> v \<in> V\<^sub>x.
              (if v \<in> V\<^sub>x then R else ({} :: 'a Preference_Relation)) = R"
          by simp

        have prof0: "profile V\<^sub>0 A p\<^sub>0"
          using b0_carrier b0_alts
          unfolding b0_eq elections_\<A>.simps well_formed_elections_def
          by auto
        have lin_R: "linear_order_on A R"
        proof -
          obtain v\<^sub>0 where "v\<^sub>0 \<in> V\<^sub>0" using b0_ne by blast
          thus ?thesis
            using prof0 R_unan
            unfolding profile_def
            by metis
        qed
        have bx_X: "b\<^sub>x \<in> ?X"
          using x_fin lin_R
          unfolding b\<^sub>x_def elections_\<A>.simps well_formed_elections_def
          by (auto simp add: profile_def)
        have frac_bx: "\<forall> q. vote_fraction q (A\<^sub>0, V\<^sub>0, p\<^sub>0)
                              = vote_fraction q b\<^sub>x"
        proof
          fix q
          have "vote_fraction q (A\<^sub>0, V\<^sub>0, p\<^sub>0) = (if q = R then 1 else 0)"
            by (rule unanimity_vote_fraction[OF b0_fin b0_ne R_unan])
          moreover have "vote_fraction q b\<^sub>x = (if q = R then 1 else 0)"
            unfolding b\<^sub>x_def
            by (rule unanimity_vote_fraction[OF x_fin x_ne unan_bx])
          ultimately show
            "vote_fraction q (A\<^sub>0, V\<^sub>0, p\<^sub>0) = vote_fraction q b\<^sub>x"
            by simp
        qed
        have "(b\<^sub>0, b\<^sub>x) \<in> ?r"
          using b0_carrier bx_X frac_bx
          unfolding b0_eq anonymity_homogeneity\<^sub>\<R>.simps
          by fastforce (* unknown isues with blast here*)
        hence bx_BC: "b\<^sub>x \<in> BC"
          using BC_img by blast
        have dist_bx: "?d (A, V\<^sub>x, p\<^sub>x) b\<^sub>x
                         = ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
          unfolding b\<^sub>x_def
          by (rule swap_dist_avg_to_unanimity[OF x_fin unan_bx])
        have attained: "?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)
                          \<in> ?d (A, V\<^sub>x, p\<^sub>x) ` BC"
          using bx_BC dist_bx by (metis image_eqI)
        have upper: "Inf (?d (A, V\<^sub>x, p\<^sub>x) ` BC)
                       \<le> ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
          using attained by (rule Inf_lower)
        have img_eq: "{?d (A, V\<^sub>x, p\<^sub>x) b | b. b \<in> BC}
                        = ?d (A, V\<^sub>x, p\<^sub>x) ` BC"
          by blast
        show ?thesis
          using lower upper
          unfolding img_eq
          by order
      qed


\<comment> \<open>All class members of AC have the same score
          (engine wrapper), so inf_helper flattens the two-sided
          Inf to that constant.\<close>
   have "distance_infimum\<^sub>\<Q> ?d AC BC = Inf { Inf  {?d x b | b. b \<in> BC} | x. x \<in> AC } "
     unfolding distance_infimum\<^sub>\<Q>.simps
     by (rule inf_helper)
   also have "\<dots> = Inf {?d a b | b. b \<in> BC}"
    proof -
        have inner_const:
          "Inf {?d x b | b. b \<in> BC} = Inf {?d a b | b. b \<in> BC}"
          if x_in: "x \<in> AC" for x
        proof -
          obtain A\<^sub>x V\<^sub>x p\<^sub>x where x_eq: "x = (A\<^sub>x, V\<^sub>x, p\<^sub>x)"
            using prod_cases3 by blast
          have ax_rel: "(a, x) \<in> ?r"
            using x_in AC_img by blast
          have x_X: "x \<in> ?X"
            using ax_rel
            unfolding anonymity_homogeneity\<^sub>\<R>.simps
            by blast
          have x_alts: "A\<^sub>x = A" and x_fin: "finite V\<^sub>x"
            using x_X
            unfolding x_eq elections_\<A>.simps 
            by auto
          have x_eq': "x = (A, V\<^sub>x, p\<^sub>x)"
            using x_eq x_alts by simp
          have x_ne: "V\<^sub>x \<noteq> {}"
            using anon_hom_empty_iff[OF ax_rel[unfolded a_eq' x_eq']] False
            by blast
          have score_eq:
            "?d (A, V\<^sub>a, p\<^sub>a) (A, V\<^sub>a, \<lambda> v. R)
               = ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
            using swap_dist_avg_invar_anon_hom[OF ax_rel[unfolded a_eq' x_eq']]
            by simp
          have "Inf {?d x b | b. b \<in> BC}
                  = ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
            using one_sided[OF x_fin x_ne] x_eq' by simp
          also have "\<dots> = ?d (A, V\<^sub>a, p\<^sub>a) (A, V\<^sub>a, \<lambda> v. R)"
            using score_eq by simp
          also have "\<dots> = Inf {?d a b | b. b \<in> BC}"
            using one_sided[OF a_fin False] a_eq' by simp
          finally show ?thesis .
        qed
        have "{Inf {?d x b | b. b \<in> BC} | x. x \<in> AC}
                = {Inf {?d a b | b. b \<in> BC}}"
          using inner_const a_in by blast
        thus ?thesis
          by simp
      qed
   finally show ?thesis .

next
    case True
    have all_inf: "?d x b = \<infinity>"
      if x_in: "x \<in> AC" and b_in: "b \<in> BC" for x b
    proof -
      obtain A\<^sub>x V\<^sub>x p\<^sub>x where x_eq: "x = (A\<^sub>x, V\<^sub>x, p\<^sub>x)"
        using prod_cases3 by blast
       have "(a, x) \<in> ?r"
         using x_in AC_img by blast
       hence ax_rel: "((A\<^sub>a, V\<^sub>a, p\<^sub>a), (A\<^sub>x, V\<^sub>x, p\<^sub>x)) \<in> ?r"
         by (simp only: a_eq x_eq)
       have x_empty: "V\<^sub>x = {}"
         using anon_hom_empty_iff[OF ax_rel] True by blast
      obtain V\<^sub>b p\<^sub>b where b_eq: "b = (A, V\<^sub>b, p\<^sub>b)" and b_ne: "V\<^sub>b \<noteq> {}"
        using BC_char[OF b_in] by blast
      show ?thesis
        using x_empty b_ne
        unfolding x_eq b_eq
        by simp
    qed

    have inst: "?d a b\<^sub>0 = \<infinity>"
      using all_inf a_in b0_in_BC
      by blast
    have "{?d x b | x b. x \<in> AC \<and> b \<in> BC} = {\<infinity>}"
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> {?d x b | x b. x \<in> AC \<and> b \<in> BC}"
      then obtain x b where "y = ?d x b" and "x \<in> AC" and "b \<in> BC"
        by blast
      hence "y = \<infinity>"
        using all_inf
        by blast
      thus "y \<in> {\<infinity>}"
        by simp

    next
      fix y :: ereal
      assume "y \<in> {\<infinity>}"
      moreover have "?d a b\<^sub>0 \<in> {?d x b | x b. x \<in> AC \<and> b \<in> BC}"
        using a_in b0_in_BC
        by blast
      ultimately show "y \<in> {?d x b | x b. x \<in> AC \<and> b \<in> BC}"
        using inst
        by simp
    qed
    moreover have "{?d a b | b. b \<in> BC} = {\<infinity>}"
    proof (intro equalityI subsetI)
      fix y
      assume "y \<in> {?d a b | b. b \<in> BC}"
      then obtain b where "y = ?d a b" and "b \<in> BC"
        by blast
      hence "y = \<infinity>"
        using all_inf a_in
        by blast
      thus "y \<in> {\<infinity>}"
        by simp

    next
      fix y :: ereal
      assume "y \<in> {\<infinity>}"
      moreover have "?d a b\<^sub>0 \<in> {?d a b | b. b \<in> BC}"
        using b0_in_BC
        by blast
      ultimately show "y \<in> {?d a b | b. b \<in> BC}"
        using inst
        by simp
    qed
    ultimately show ?thesis
      unfolding distance_infimum\<^sub>\<Q>.simps
      by simp
  qed
qed
qed


end