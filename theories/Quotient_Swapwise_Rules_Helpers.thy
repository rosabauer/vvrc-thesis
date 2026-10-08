(*  File:       Quotient_Swapwise_Rules_Helpers.thy
*)
\<^marker>\<open>creator "Rosa Bauer, LMU Munich"\<close>

section \<open>Quotient Reasoning for the Normalized Swap Distance\<close>

theory Quotient_Swapwise_Rules_Helpers
  imports
    "Compositional_Structures/Basic_Modules/Component_Types/Quotient_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Votewise_Distance_Rationalization"
    "Compositional_Structures/Basic_Modules/Component_Types/Quotients/Election_Quotients"
begin

text \<open>
  This theory provides the ingredients for instantiating the quotient distance
  rationalization of \<open>Quotient_Distance_Rationalization\<close> with the normalized
  swap distance \<open>votewise_distance swap l_one_avg\<close> and the strong unanimity
  consensus on a fixed alternative set \<open>A\<close>, with respect to the
  anonymity-homogeneity relation on \<open>elections_\<A> A\<close>. The main results are
  \<open>swap_l_one_avg_simple\<close> (the distance is simple on the consensus classes),
  \<open>strong_unanimity_in_closed_under_anon_hom\<close> and
  \<open>strong_unanimity_in_invar_anon_hom\<close> (the consensus class is closed under the
  relation and its rule is invariant on it), and \<open>swap_score_invar_anon_hom\<close>
  together with \<open>anon_hom_score_invar_imp_invar_dr\<close> (the scores and hence the
  distance-rationalized winners are invariant). They are combined in
  \<open>Quotient_Kemeny_Rule\<close>.
\<close>

subsection \<open>Strong Unanimity on a Fixed Alternative Set\<close>

text \<open>
  We define a variant of strong unanimity that fixes the alternative set and
  demands that ballots outside of the voter set are simply empty. This makes it
  easier to prove that the assumptions of the invar_dr lemmas hold for rules
  with a DR set. Specifically, this restriction aligns with the definition of elections_A A which
  demands that an election with a unique profile leaves all ballots of non-voters empty.

  TBD: We prove later that this restriction does not change the minimum
  distance to the consensus class, so it is interchangeable with the
  unrestricted strong unanimity.
\<close>

definition strong_unanimity_in :: "'a set \<Rightarrow> ('a, 'v :: wellorder, 'a Result) Consensus_Class" where
  "strong_unanimity_in A \<equiv> consensus_choice
    (\<lambda> E. strong_unanimity\<^sub>\<C> E \<and> alternatives_\<E> E = A
    \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {}))
    elect_first_module"


lemma (in result) limit_invar_anon_hom:
  fixes A :: "'a set"
  shows  "is_symmetry
      (\<lambda> E :: ('a, 'v) Election. limit (alternatives_\<E> E) UNIV)
      (Invariance (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)))"
proof -
  have "\<forall> E E' :: ('a, 'v) Election.
          (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)
            \<longrightarrow> alternatives_\<E> E = alternatives_\<E> E'"
  proof (intro allI impI)
    fix E E' :: "('a, 'v) Election"
    assume "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    hence "E \<in> elections_\<A> A \<and> E' \<in> elections_\<A> A"
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
    hence "alternatives_\<E> E = A \<and> alternatives_\<E> E' = A"
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
  shows "elections_\<K> (strong_unanimity_in A) \<subseteq> elections_\<A> A"
  by (auto simp add: well_formed_elections_def strong_unanimity_in_def)

text \<open>
  Membership in a consensus class of \<open>strong_unanimity_in A\<close> unpacks to:
  the alternative set is \<open>A\<close>, the finite, nonempty electorate unanimously
  casts a ballot \<open>R\<close> that is empty for non-voters, and \<open>w\<close> is the unique
  alternative ranked first by \<open>R\<close>. The next two lemmas state the two directions.
\<close>

lemma strong_unanimity_in_\<K>\<^sub>\<E>D:
  fixes
    A A' :: "'a set" and
    V :: "'v :: wellorder set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assumes "(A', V, p) \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
  shows "A' = A \<and> A \<noteq> {} \<and> finite A \<and> finite V \<and> V \<noteq> {} \<and> profile V A p
          \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})
          \<and> (\<exists> R. (\<forall> v \<in> V. p v = R) \<and> {a \<in> A. above R a = {a}} = {w})"
proof -
  have cond: "strong_unanimity\<^sub>\<C> (A', V, p) \<and> A' = A \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})" and
       fin: "finite_profile V A' p" and
       elect: "elect (rule_\<K> (strong_unanimity_in A)) V A' p = {w}"
    using assms
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
    by (simp_all add: Let_def split: if_split_asm)
  from cond obtain R where unan: "\<forall> v \<in> V. p v = R"
    unfolding strong_unanimity\<^sub>\<C>.simps equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
    by blast
  have alts: "A' = A" and A_ne: "A \<noteq> {}" and V_ne: "V \<noteq> {}"
    using cond
    unfolding strong_unanimity\<^sub>\<C>.simps nonempty_set\<^sub>\<C>.simps nonempty_profile\<^sub>\<C>.simps
    by auto
  have least_V: "least V \<in> V"
    using V_ne LeastI_ex ex_in_conv
    unfolding least.simps
    by metis
  have "{a \<in> A. above R a = {a}} = {a \<in> A'. above (p (least V)) a = {a}}"
    using unan least_V alts
    by simp
  also have "\<dots> = elect (rule_\<K> (strong_unanimity_in A)) V A' p"
    using cond
    unfolding strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  also have "\<dots> = {w}"
    by (rule elect)
  finally have elect_R: "{a \<in> A. above R a = {a}} = {w}" .
  show ?thesis
    unfolding alts
    using cond[unfolded alts] fin[unfolded alts] unan elect_R A_ne V_ne
    by blast
qed

lemma strong_unanimity_in_\<K>\<^sub>\<E>I:
  fixes
    A :: "'a set" and
    V :: "'v :: wellorder set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation" and
    w :: "'a"
  assumes
    A_ne: "A \<noteq> {}" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    V_ne: "V \<noteq> {}" and
    prof: "profile V A p" and
    nonvoter: "\<forall> v. v \<notin> V \<longrightarrow> p v = {}" and
    unan: "\<forall> v \<in> V. p v = R" and
    elect_R: "{a \<in> A. above R a = {a}} = {w}"
  shows "(A, V, p) \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
proof -
  have cond: "strong_unanimity\<^sub>\<C> (A, V, p) \<and> A = A \<and> (\<forall> v. v \<notin> V \<longrightarrow> p v = {})"
    using A_ne V_ne unan nonvoter
    unfolding strong_unanimity\<^sub>\<C>.simps nonempty_set\<^sub>\<C>.simps nonempty_profile\<^sub>\<C>.simps
              equal_vote\<^sub>\<C>.simps equal_vote\<^sub>\<C>'.simps
    by auto
  have least_V: "least V \<in> V"
    using V_ne LeastI_ex ex_in_conv
    unfolding least.simps
    by metis
  have "elect (rule_\<K> (strong_unanimity_in A)) V A p = {a \<in> A. above (p (least V)) a = {a}}"
    using cond
    unfolding strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
  also have "\<dots> = {a \<in> A. above R a = {a}}"
    using unan least_V
    by simp
  finally have elect: "elect (rule_\<K> (strong_unanimity_in A)) V A p = {w}"
    using elect_R
    by simp
  show ?thesis
    using cond fin_A fin_V prof elect
    unfolding \<K>\<^sub>\<E>.simps strong_unanimity_in_def consensus_choice.simps
    by (simp add: Let_def)
qed

text \<open>
  The vote fractions of a unanimity election form the indicator of its
  common ballot.
\<close>

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

text \<open>
  Conversely, a ballot with vote fraction one is cast by every voter.
\<close>

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


text \<open>
  Unanimity for a ballot \<open>R\<close> transfers along the relation: the fraction of
  \<open>R\<close> is one on one side, hence on the other.
\<close>

lemma anon_hom_unanimous_transfer:
  fixes
    A A\<^sub>1 A\<^sub>2 :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p')) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)" and
    ne: "V \<noteq> {}" and
    unan: "\<forall> v \<in> V. p v = R"
  shows "V' \<noteq> {} \<and> (\<forall> v \<in> V'. p' v = R)"
proof -
  have inA: "(A\<^sub>1, V, p) \<in> elections_\<A> A" and
       inA': "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
       eq_frac: "\<forall> q. vote_fraction q (A\<^sub>1, V, p) = vote_fraction q (A\<^sub>2, V', p')"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have fin: "finite V" and fin': "finite V'"
    using inA inA'
    unfolding elections_\<A>.simps
    by auto
  have "vote_fraction R (A\<^sub>1, V, p) = 1"
    using unanimity_vote_fraction[OF fin ne unan]
    by simp
  hence "vote_fraction R (A\<^sub>2, V', p') = 1"
    using eq_frac
    by metis
  thus ?thesis
    by (rule vote_fraction_one_imp_unanimous[OF fin'])
qed

text \<open>
  Consensus membership with a fixed winner transfers along the
  anonymity-homogeneity relation. This is the strong form of the closedness
  lemma below, which forgets the winner.
\<close>

lemma strong_unanimity_in_anon_hom_transfer:
  fixes
    A :: "'a set" and
    E E' :: "('a, 'v :: wellorder) Election" and
    w :: "'a"
  assumes
    rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)" and
    cons: "E \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
  shows "E' \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
proof -
  obtain A\<^sub>1 :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (A\<^sub>1, V, p)"
    using prod_cases3
    by blast
  obtain A\<^sub>2 :: "'a set" and V' :: "'v set" and p' :: "('a, 'v) Profile" where
    E'_eq: "E' = (A\<^sub>2, V', p')"
    using prod_cases3
    by blast
  \<comment> \<open>Unpack the relation: the target lies in the carrier and the vote
      fractions coincide.\<close>
  have E'_in_A: "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
       eq_fract: "\<forall> q. vote_fraction q (A\<^sub>1, V, p) = vote_fraction q (A\<^sub>2, V', p')"
    using rel
    unfolding E_eq E'_eq anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  hence alts': "A\<^sub>2 = A" and
        fin_V': "finite V'" and
        wf': "profile V' A\<^sub>2 p'" and
        nonvoter': "\<forall> v. v \<notin> V' \<longrightarrow> p' v = {}"
    unfolding elections_\<A>.simps well_formed_elections_def
    by auto
  have prof': "profile V' A p'"
    using wf' alts'
    by simp
  \<comment> \<open>Unpack the consensus membership of the source election.\<close>
  obtain R :: "'a Preference_Relation" where
    A_ne: "A \<noteq> {}" and
    fin_A: "finite A" and
    fin_V: "finite V" and
    V_ne: "V \<noteq> {}" and
    unan: "\<forall> v \<in> V. p v = R" and
    elect_R: "{a \<in> A. above R a = {a}} = {w}"
    using strong_unanimity_in_\<K>\<^sub>\<E>D[OF cons[unfolded E_eq]]
    by blast
  \<comment> \<open>The common ballot has fraction one in the source, hence in the target,
      so the target is unanimous for the same ballot.\<close>
  have "vote_fraction R (A\<^sub>1, V, p) = 1"
    using unanimity_vote_fraction[OF fin_V V_ne unan]
    by simp
  hence "vote_fraction R (A\<^sub>2, V', p') = 1"
    using eq_fract
    by metis
  hence V'_ne: "V' \<noteq> {}" and unan': "\<forall> v \<in> V'. p' v = R"
    using vote_fraction_one_imp_unanimous[OF fin_V']
    by blast+
  have "(A, V', p') \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
    by (rule strong_unanimity_in_\<K>\<^sub>\<E>I[OF A_ne fin_A fin_V' V'_ne prof' nonvoter' unan' elect_R])
  thus ?thesis
    unfolding E'_eq alts' .
qed

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
    rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p'))\<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)" and
    cons: "(A\<^sub>1, V, p)\<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
  have "(A\<^sub>2, V', p') \<in>  \<K>\<^sub>\<E> (strong_unanimity_in A) w"
    by (rule strong_unanimity_in_anon_hom_transfer[OF rel cons])
  thus "(A\<^sub>2, V', p') \<in> \<Union> (range (\<K>\<^sub>\<E> (strong_unanimity_in A)))"
    by blast
qed


text ‹
  On its consensus set, the restricted strong-unanimity rule is invariant
  under the anonymity-homogeneity relation: related consensus elections
  elect the same singleton, by the transfer lemma.
›

lemma strong_unanimity_in_invar_anon_hom:
  fixes A :: "'a set"
  shows "is_symmetry
           (elect_r ∘ fun⇩ℰ (rule_𝒦 (strong_unanimity_in A)))
           (Invariance (Restr (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
              (elections_𝒦 (strong_unanimity_in A)
                  :: ('a, 'v :: wellorder) Election set)))"
proof (unfold is_symmetry.simps, intro allI impI)
  fix E E' :: "('a, 'v) Election"
  assume "(E, E') ∈ Restr (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
                          (elections_𝒦 (strong_unanimity_in A))"
  hence rel: "(E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)" and
        E_Y: "E ∈ elections_𝒦 (strong_unanimity_in A)"
    by blast+
  from E_Y obtain w where "E ∈ 𝒦⇩ℰ (strong_unanimity_in A) w"
    unfolding elections_𝒦.simps
    by blast
  hence cons_pair: "E ∈ 𝒦⇩ℰ (strong_unanimity_in A) w
                      ∧ E' ∈ 𝒦⇩ℰ (strong_unanimity_in A) w"
    using strong_unanimity_in_anon_hom_transfer[OF rel]
    by blast
  obtain A⇩1 V p where E_eq: "E = (A⇩1, V, p)"
    using prod_cases3 by blast
  obtain A⇩2 V' p' where E'_eq: "E' = (A⇩2, V', p')"
    using prod_cases3 by blast
  have "elect (rule_𝒦 (strong_unanimity_in A)) V A⇩1 p = {w}" and
       "elect (rule_𝒦 (strong_unanimity_in A)) V' A⇩2 p' = {w}"
    using cons_pair
    unfolding E_eq E'_eq 𝒦⇩ℰ.simps
    by blast+
  thus "(elect_r ∘ fun⇩ℰ (rule_𝒦 (strong_unanimity_in A))) E
          = (elect_r ∘ fun⇩ℰ (rule_𝒦 (strong_unanimity_in A))) E'"
    unfolding E_eq E'_eq
    by simp
qed

subsection \<open>The Normalized Swap Distance to Unanimity Elections\<close>

text \<open>
  The votewise swap distance from a profile to a unanimous consensus profile
  equals the sum, over all cast ballots, of the number of voters who cast that
  ballot times the swap distance of that ballot to the consensus ballot. Connects vote count
  and cardinality to the different type of the votewise swap distance.
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

  \<comment> \<open>Unfold votewise_distance. Its guard holds since V is finite and non-empty\<close>
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
    fin: "finite V" and
    fin': "finite V'" and
    n_pos: "0 < card V" and
    n'_pos: "0 < card V'" and
    cross: "\<forall> r. vote_count r (A, V, p) * card V' = vote_count r (A, V', p') * card V"
  shows "p ` V = p' ` V'"
proof -
  have "r \<in> p ` V \<longleftrightarrow> r \<in> p' ` V'" for r :: "'a Preference_Relation"
  proof -
    have "card V \<noteq> 0" and "card V' \<noteq> 0"
      using n_pos n'_pos
      by simp_all
    hence "(vote_count r (A, V, p) = 0) = (vote_count r (A, V', p') = 0)"
      using cross[rule_format, of r]
      by (metis mult_is_0)
    thus ?thesis
      using vote_count_mem_image_iff[OF fin, where A = A and p = p and r = r]
            vote_count_mem_image_iff[OF fin', where A = A and p = p' and r = r]
      by blast
  qed
  thus ?thesis
    by blast
qed

text \<open>
  On a finite, nonempty voter set, the normalized swap distance to the
  constant-R profile is the sum over the cast ballots of their vote count times
  their swap distance to R, divided by the number of voters. This combines the
  counting formula with the normalization of \<open>l_one_avg\<close>.
\<close>

lemma swap_dist_avg_as_sum:
  fixes
    A :: "'a set" and
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    ne: "V \<noteq> {}"
  shows "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)
          = ereal ((\<Sum> r \<in> p ` V. real (vote_count r (A, V, p))
                      * real (card (pairwise_disagreements A r R))) / real (card V))"
proof -
  have n_pos: "0 < card V"
    using fin ne card_gt_0_iff
    by blast
  have raw: "votewise_distance swap l_one (A, V, p) (A, V, \<lambda> v. R)
      = ereal (\<Sum> r \<in> p ` V. real (vote_count r (A, V, p))
                  * real (card (pairwise_disagreements A r R)))"
    unfolding swap_dist_counting_formula[OF fin ne]
    by simp
  show ?thesis
    unfolding dist_avg_norm_eq_normalized_dist[OF fin ne] raw
    using n_pos
    by simp
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
    fin: "finite V" and
    fin': "finite V'" and
    nonempty: "V \<noteq> {}" and
    nonempty': "V' \<noteq> {}" and
    eq_frac: "\<forall> r. vote_fraction r (A, V, p) = vote_fraction r (A, V', p')"
  shows "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)
          = votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)"
proof -
  let ?n = "card V"
  let ?n' = "card V'"
  define cost :: "'a Preference_Relation \<Rightarrow> real" where
    "cost = (\<lambda> r. real (card (pairwise_disagreements A r R)))"
  let ?s = "\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r"
  let ?s' = "\<Sum> r \<in> p' ` V'. real (vote_count r (A, V', p')) * cost r"
  have n_pos: "0 < ?n"
    using fin nonempty card_gt_0_iff
    by blast
  have n'_pos: "0 < ?n'"
    using fin' nonempty' card_gt_0_iff
    by blast
  \<comment> \<open>Equal vote fractions give a cross-multiplication identity on the counts.\<close>
  have cross: "\<forall> r. vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
  proof
    fix r :: "'a Preference_Relation"
    have eq: "vote_fraction r (A, V, p) = vote_fraction r (A, V', p')"
      using eq_frac
      by blast
    hence "Fract (vote_count r (A, V, p)) ?n = Fract (vote_count r (A, V', p')) ?n'"
      using fin nonempty fin' nonempty'
      unfolding vote_fraction.simps voters_\<E>.simps
      by simp
    hence "int (vote_count r (A, V, p)) * int ?n' = int (vote_count r (A, V', p')) * int ?n"
      using n_pos n'_pos
      by (simp add: eq_rat)
    thus "vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
      by (metis of_nat_eq_iff of_nat_mult)
  qed
  have img_eq: "p ` V = p' ` V'"
    by (rule image_eq_of_cross[OF fin fin' n_pos n'_pos cross])
  \<comment> \<open>Distribute the factor, rewrite each summand via the identity, collect.\<close>
  have raw_cross: "?s * real ?n' = ?s' * real ?n"
  proof -
    have "?s * real ?n' = (\<Sum> r \<in> p ` V. real (vote_count r (A, V, p)) * cost r * real ?n')"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum> r \<in> p ` V. real (vote_count r (A, V', p')) * cost r * real ?n)"
    proof (intro sum.cong refl)
      fix r :: "'a Preference_Relation"
      assume "r \<in> p ` V"
      have "vote_count r (A, V, p) * ?n' = vote_count r (A, V', p') * ?n"
        using cross
        by blast
      hence "real (vote_count r (A, V, p)) * real ?n' = real (vote_count r (A, V', p')) * real ?n"
        by (metis of_nat_mult)
      thus "real (vote_count r (A, V, p)) * cost r * real ?n'
              = real (vote_count r (A, V', p')) * cost r * real ?n"
        by (metis mult.assoc mult.commute)
    qed simp
    also have "\<dots> = (\<Sum> r \<in> p ` V. real (vote_count r (A, V', p')) * cost r) * real ?n"
      by (simp add: sum_distrib_right)
    also have "\<dots> = ?s' * real ?n"
      by (simp add: img_eq)
    finally show ?thesis .
  qed
  have real_eq: "?s / real ?n = ?s' / real ?n'"
    using raw_cross n_pos n'_pos
    by (auto simp: field_simps)
  have "votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R) = ereal (?s / real ?n)"
    unfolding cost_def
    by (rule swap_dist_avg_as_sum[OF fin nonempty])
  also have "\<dots> = ereal (?s' / real ?n')"
    by (simp only: real_eq)
  also have "\<dots> = votewise_distance swap l_one_avg (A, V', p') (A, V', \<lambda> v. R)"
    unfolding cost_def
    by (rule swap_dist_avg_as_sum[OF fin' nonempty', symmetric])
  finally show ?thesis .
qed

text \<open>
  A ballot cast by some voter has positive vote fraction, so equal vote
  fractions transfer non-emptiness of the voter set.
\<close>

lemma vote_fraction_eq_imp_nonempty:
  fixes
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assumes
    fin: "finite V" and
    ne: "V \<noteq> {}" and
    eq_frac: "\<forall> q. vote_fraction q (A, V, p) = vote_fraction q (A', V', p')"
  shows "V' \<noteq> {}"
proof -
  obtain v where v_in: "v \<in> V"
    using ne
    by blast
  have "vote_count (p v) (A, V, p) \<noteq> 0"
    using fin v_in vote_count_mem_image_iff
    by blast
  hence num_pos: "0 < vote_count (p v) (A, V, p)"
    by simp
  have den_pos: "0 < card V"
    using fin ne card_gt_0_iff
    by blast
  have "0 < Fract (int (vote_count (p v) (A, V, p))) (int (card V))"
    using num_pos den_pos
    by (simp add: zero_less_Fract_iff)
  hence "vote_fraction (p v) (A, V, p) > 0"
    using fin ne
    unfolding vote_fraction.simps voters_\<E>.simps
    by simp
  hence pos': "vote_fraction (p v) (A', V', p') > 0"
    using eq_frac
    by metis
  show "V' \<noteq> {}"
  proof
    assume "V' = {}"
    hence "vote_fraction (p v) (A', V', p') = 0"
      unfolding vote_fraction.simps voters_\<E>.simps
      by (simp add: rat_number_collapse)
    thus False
      using pos'
      by simp
  qed
qed

text \<open>
  Related elections have empty voter sets simultaneously.
\<close>

lemma anon_hom_empty_iff:
  fixes
    A A\<^sub>1 A\<^sub>2 :: "'a set" and
    V V' :: "'v :: linorder set" and
    p p' :: "('a, 'v) Profile"
  assumes rel: "((A\<^sub>1, V, p), (A\<^sub>2, V', p')) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "(V = {}) = (V' = {})"
proof -
  have inA: "(A\<^sub>1, V, p) \<in> elections_\<A> A" and
       inA': "(A\<^sub>2, V', p') \<in> elections_\<A> A" and
       eq_frac: "\<forall> q. vote_fraction q (A\<^sub>1, V, p) = vote_fraction q (A\<^sub>2, V', p')"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have fin: "finite V" and fin': "finite V'"
    using inA inA'
    unfolding elections_\<A>.simps
    by auto
  have eq_frac': "\<forall> q. vote_fraction q (A\<^sub>2, V', p') = vote_fraction q (A\<^sub>1, V, p)"
    using eq_frac
    by simp
  show ?thesis
    using vote_fraction_eq_imp_nonempty[OF fin _ eq_frac]
          vote_fraction_eq_imp_nonempty[OF fin' _ eq_frac']
    by blast
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
  have empty_iff: "(V = {}) = (V' = {})"
    by (rule anon_hom_empty_iff[OF rel])

  \<comment> \<open>4. Case split: both voter sets empty or both nonempty.\<close>
  show ?thesis
  proof (cases "V = {}")
    case True
    hence V'_empty: "V' = {}"
      using empty_iff
      by blast
     \<comment> \<open>The profiles only enter via to_list, and to_list {} f = [] for any f,
        so both sides are the same computation over A.\<close>
    show ?thesis
      using True V'_empty alts alts'
      by simp
  next
    case False
    hence ne': "V' \<noteq> {}"
      using empty_iff
      by blast
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
  The distance to a unanimity-R election on the same voter set does not depend
  on the ballots of its non-voters: votewise distances only read the ballots of
  voters (\<open>votewise_non_voters_irrelevant\<close>).
\<close>

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
      using fin
      by simp
    also have "\<dots> = map (\<lambda> v. R) (sorted_list_of_set V)"
      using qR fin
      by (intro map_cong) auto
    also have "\<dots> = to_list V (\<lambda> v. R)"
      using fin
      by simp
    finally show ?thesis .
  qed
  have "votewise_distance swap l_one_avg (A, V, p) (A, V, q)
          = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y)) (to_list V p) (to_list V q))"
    using fin
    by simp
  also have "\<dots> = l_one_avg (map2 (\<lambda> x y. swap (A, x) (A, y))
                              (to_list V p) (to_list V (\<lambda> v. R)))"
    by (simp only: to_list_R)
  also have "\<dots> = votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)"
    using fin
    by simp
  finally show ?thesis .
qed

text \<open>
  A unanimous ballot of a well-formed election is a linear order on the
  alternatives.
\<close>

lemma unanimous_ballot_lin_ord:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    ne: "V \<noteq> {}" and
    prof: "profile V A p" and
    unan: "\<forall> v \<in> V. p v = R"
  shows "linear_order_on A R"
proof -
  obtain v where "v \<in> V"
    using ne
    by blast
  thus ?thesis
    using prof unan
    unfolding profile_def
    by metis
qed

text \<open>
  The unanimity election on a voter set \<open>V\<close> with common ballot \<open>R\<close>:
  every voter casts \<open>R\<close>, every non-voter the empty ballot. It is the
  canonical partner of an election in the consensus class of \<open>R\<close>.
\<close>

definition unanimity_election :: "'a set \<Rightarrow> 'v set \<Rightarrow> 'a Preference_Relation
                                    \<Rightarrow> ('a, 'v) Election" where
  "unanimity_election A V R = (A, V, \<lambda> v. if v \<in> V then R else {})"

lemma unanimity_election_in_elections_\<A>:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    R :: "'a Preference_Relation"
  assumes
    fin: "finite V" and
    lin: "linear_order_on A R"
  shows "unanimity_election A V R \<in> elections_\<A> A"
  using fin lin
  unfolding unanimity_election_def elections_\<A>.simps well_formed_elections_def
  by (auto simp add: profile_def)

lemma swap_dist_avg_unanimity_election:
  fixes
    A :: "'a set" and
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes fin: "finite V"
  shows "votewise_distance swap l_one_avg (A, V, p) (unanimity_election A V R)
          = votewise_distance swap l_one_avg (A, V, p) (A, V, \<lambda> v. R)"
  unfolding unanimity_election_def
  by (rule swap_dist_avg_to_unanimity[OF fin]) simp

text \<open>
  A unanimity election with ballot \<open>R\<close> is related to the unanimity election
  with the same ballot on any other finite, nonempty voter set, since both
  have the indicator of \<open>R\<close> as their vote fractions.
\<close>

lemma unanimity_election_anon_hom_related:
  fixes
    A :: "'a set" and
    V V' :: "'v set" and
    p :: "('a, 'v) Profile" and
    R :: "'a Preference_Relation"
  assumes
    E_X: "(A, V, p) \<in> elections_\<A> A" and
    ne: "V \<noteq> {}" and
    unan: "\<forall> v \<in> V. p v = R" and
    fin': "finite V'" and
    ne': "V' \<noteq> {}"
  shows "((A, V, p), unanimity_election A V' R)
          \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
proof -
  have fin: "finite V" and prof: "profile V A p"
    using E_X
    unfolding elections_\<A>.simps well_formed_elections_def
    by auto
  have lin_R: "linear_order_on A R"
    by (rule unanimous_ballot_lin_ord[OF ne prof unan])
  have E'_X: "unanimity_election A V' R \<in> elections_\<A> A"
    by (rule unanimity_election_in_elections_\<A>[OF fin' lin_R])
  have unan': "\<forall> v \<in> V'. (\<lambda> v. if v \<in> V' then R else ({} :: 'a Preference_Relation)) v = R"
    by simp
  have "\<forall> q. vote_fraction q (A, V, p) = vote_fraction q (unanimity_election A V' R)"
    unfolding unanimity_election_def
    using unanimity_vote_fraction[OF fin ne unan] unanimity_vote_fraction[OF fin' ne' unan']
    by simp
  thus ?thesis
    using E_X E'_X fin fin'
    unfolding anonymity_homogeneity\<^sub>\<R>.simps unanimity_election_def
    by fastforce
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

  \<comment> \<open>The distance to any same-voter-set class member is the score.\<close>
  have same_V_dist: "?d (A, V, q) = ?s"
    if q_R: "\<forall> v \<in> V. q v = R" for q :: "('a, 'v) Profile"
    by (rule swap_dist_avg_to_unanimity[OF fin q_R])

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

subsection \<open>Simplicity of the Normalized Swap Distance\<close>

text \<open>
  The main result of this theory: the normalized swap distance is simple on the
  consensus classes. By \<open>inner_inf_const_imp_simple_on\<close> it suffices that, for a
  consensus class BC with common ballot R, the infimum of the distances from an
  election x to BC is the same for all x of one anonymity-homogeneity class.
  For an election with a nonempty voter set this infimum is attained at the
  unanimity-R election on its own voter set, and these values agree across the
  class by the engine lemma \<open>swap_dist_avg_invar_anon_hom\<close>. For an empty voter
  set the infimum is \<open>\<infinity>\<close>, since all members of BC have voters.
\<close>

lemma swap_l_one_avg_simple:
  fixes A :: "'a set"
  shows "simple_on
    (elections_\<K> (strong_unanimity_in A))
    (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))
    (elections_\<A> A)
    (votewise_distance swap l_one_avg :: ('a, 'v :: wellorder) Election Distance)"
    (is "simple_on ?Y ?r ?X ?d")
proof (rule inner_inf_const_imp_simple_on[OF anon_hom_equiv], intro ballI)
  fix
    AC BC :: "('a, 'v) Election set" and
    x x' :: "('a, 'v) Election"
  assume
    AC_cls: "AC \<in> ?X // ?r" and
    BC_cls: "BC \<in> ?Y // ?r" and
    x_in: "x \<in> AC" and
    x'_in: "x' \<in> AC"
  \<comment> \<open>The consensus class BC is generated by a strong unanimity election
      \<open>b\<^sub>0\<close> with common ballot R.\<close>
  obtain b\<^sub>0 :: "('a, 'v) Election" where
    b0_Y: "b\<^sub>0 \<in> ?Y" and
    BC_img: "BC = ?r `` {b\<^sub>0}"
    using BC_cls
    by (blast elim: quotientE)
  obtain w :: "'a" where b0_cons: "b\<^sub>0 \<in> \<K>\<^sub>\<E> (strong_unanimity_in A) w"
    using b0_Y
    unfolding elections_\<K>.simps
    by blast
  obtain A\<^sub>0 :: "'a set" and V\<^sub>0 :: "'v set" and p\<^sub>0 :: "('a, 'v) Profile" where
    b0_eq: "b\<^sub>0 = (A\<^sub>0, V\<^sub>0, p\<^sub>0)"
    using prod_cases3
    by blast
  obtain R :: "'a Preference_Relation" where
    b0_alts: "A\<^sub>0 = A" and
    b0_ne: "V\<^sub>0 \<noteq> {}" and
    R_unan: "\<forall> v \<in> V\<^sub>0. p\<^sub>0 v = R"
    using strong_unanimity_in_\<K>\<^sub>\<E>D[OF b0_cons[unfolded b0_eq]]
    by blast
  have b0_A: "b\<^sub>0 = (A, V\<^sub>0, p\<^sub>0)"
    using b0_eq b0_alts
    by simp
  have b0_X: "(A, V\<^sub>0, p\<^sub>0) \<in> ?X"
    using b0_Y[unfolded b0_A]
    by (rule subsetD[OF strong_unanimity_elections_subset])
  have b0_in_BC: "b\<^sub>0 \<in> BC"
    using BC_img b0_X anon_hom_equiv
    unfolding b0_A equiv_def refl_on_def
    by blast
  \<comment> \<open>Every member of BC is a unanimity-R election over A.\<close>
  have BC_sub: "BC \<subseteq> unanimity_class A R"
  proof
    fix b :: "('a, 'v) Election"
    assume b_in: "b \<in> BC"
    obtain A\<^sub>b :: "'a set" and V\<^sub>b :: "'v set" and p\<^sub>b :: "('a, 'v) Profile" where
      b_eq: "b = (A\<^sub>b, V\<^sub>b, p\<^sub>b)"
      using prod_cases3
      by blast
    have b_rel: "((A, V\<^sub>0, p\<^sub>0), (A\<^sub>b, V\<^sub>b, p\<^sub>b)) \<in> ?r"
      using b_in BC_img
      unfolding b0_A b_eq
      by blast
    have "(A\<^sub>b, V\<^sub>b, p\<^sub>b) \<in> ?X"
      using b_rel
      unfolding anonymity_homogeneity\<^sub>\<R>.simps
      by blast
    hence b_alts: "A\<^sub>b = A" and
          b_fin: "finite V\<^sub>b" and
          b_nonvoter: "\<forall> v. v \<notin> V\<^sub>b \<longrightarrow> p\<^sub>b v = {}"
      unfolding elections_\<A>.simps
      by auto
    have b_ne: "V\<^sub>b \<noteq> {}" and b_unan: "\<forall> v \<in> V\<^sub>b. p\<^sub>b v = R"
      using anon_hom_unanimous_transfer[OF b_rel b0_ne R_unan]
      by blast+
    show "b \<in> unanimity_class A R"
      using b_alts b_fin b_ne b_unan b_nonvoter
      unfolding b_eq unanimity_class_def
      by simp
  qed
  \<comment> \<open>Nonempty voter set: the infimum over BC is attained at the unanimity-R
      election on that voter set.\<close>
  have inner: "Inf {?d (A, V\<^sub>y, p\<^sub>y) b | b. b \<in> BC}
                 = ?d (A, V\<^sub>y, p\<^sub>y) (A, V\<^sub>y, \<lambda> v. R)"
    if y_fin: "finite V\<^sub>y" and y_ne: "V\<^sub>y \<noteq> {}"
    for V\<^sub>y :: "'v set" and p\<^sub>y :: "('a, 'v) Profile"
  proof -
    have lower: "?d (A, V\<^sub>y, p\<^sub>y) (A, V\<^sub>y, \<lambda> v. R) \<le> Inf (?d (A, V\<^sub>y, p\<^sub>y) ` BC)"
      using swap_dist_avg_collapse[OF y_fin y_ne] BC_sub Inf_superset_mono image_mono
      by metis
    have "((A, V\<^sub>0, p\<^sub>0), unanimity_election A V\<^sub>y R) \<in> ?r"
      by (rule unanimity_election_anon_hom_related[OF b0_X b0_ne R_unan y_fin y_ne])
    hence "unanimity_election A V\<^sub>y R \<in> BC"
      using BC_img
      unfolding b0_A
      by blast
    hence "?d (A, V\<^sub>y, p\<^sub>y) (unanimity_election A V\<^sub>y R) \<in> ?d (A, V\<^sub>y, p\<^sub>y) ` BC"
      by blast
    hence "Inf (?d (A, V\<^sub>y, p\<^sub>y) ` BC) \<le> ?d (A, V\<^sub>y, p\<^sub>y) (unanimity_election A V\<^sub>y R)"
      by (rule Inf_lower)
    hence upper: "Inf (?d (A, V\<^sub>y, p\<^sub>y) ` BC) \<le> ?d (A, V\<^sub>y, p\<^sub>y) (A, V\<^sub>y, \<lambda> v. R)"
      unfolding swap_dist_avg_unanimity_election[OF y_fin] .
    have img_eq: "{?d (A, V\<^sub>y, p\<^sub>y) b | b. b \<in> BC} = ?d (A, V\<^sub>y, p\<^sub>y) ` BC"
      by blast
    show ?thesis
      using lower upper
      unfolding img_eq
      by order
  qed
  \<comment> \<open>Empty voter set: every member of BC is at distance \<open>\<infinity>\<close>.\<close>
  have inner_empty: "Inf {?d (A, {}, p\<^sub>y) b | b. b \<in> BC} = \<infinity>"
    for p\<^sub>y :: "('a, 'v) Profile"
  proof -
    have "?d (A, {}, p\<^sub>y) b = \<infinity>" if b_in: "b \<in> BC" for b :: "('a, 'v) Election"
    proof -
      obtain A\<^sub>b :: "'a set" and V\<^sub>b :: "'v set" and p\<^sub>b :: "('a, 'v) Profile" where
        b_eq: "b = (A\<^sub>b, V\<^sub>b, p\<^sub>b)"
        using prod_cases3
        by blast
      have "V\<^sub>b \<noteq> {}"
        using BC_sub b_in
        unfolding b_eq unanimity_class_def
        by auto
      thus ?thesis
        unfolding b_eq
        by simp
    qed
    hence "{?d (A, {}, p\<^sub>y) b | b. b \<in> BC} = {\<infinity>}"
      using b0_in_BC
      by blast
    thus ?thesis
      by simp
  qed
  \<comment> \<open>Both elections lie in the class AC, so they are related; compare the
      two inner infima.\<close>
  have rel: "(x, x') \<in> ?r"
    using quotient_eq_iff[OF anon_hom_equiv AC_cls AC_cls x_in x'_in]
    by simp
  obtain A\<^sub>x :: "'a set" and V\<^sub>x :: "'v set" and p\<^sub>x :: "('a, 'v) Profile" where
    x_eq: "x = (A\<^sub>x, V\<^sub>x, p\<^sub>x)"
    using prod_cases3
    by blast
  obtain A\<^sub>x' :: "'a set" and V\<^sub>x' :: "'v set" and p\<^sub>x' :: "('a, 'v) Profile" where
    x'_eq: "x' = (A\<^sub>x', V\<^sub>x', p\<^sub>x')"
    using prod_cases3
    by blast
  have x_X: "x \<in> ?X" and x'_X: "x' \<in> ?X"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have x_alts: "A\<^sub>x = A" and x_fin: "finite V\<^sub>x"
    using x_X
    unfolding x_eq elections_\<A>.simps
    by auto
  have x'_alts: "A\<^sub>x' = A" and x'_fin: "finite V\<^sub>x'"
    using x'_X
    unfolding x'_eq elections_\<A>.simps
    by auto
  have x_A: "x = (A, V\<^sub>x, p\<^sub>x)" and x'_A: "x' = (A, V\<^sub>x', p\<^sub>x')"
    using x_eq x'_eq x_alts x'_alts
    by simp_all
  have rel_A: "((A, V\<^sub>x, p\<^sub>x), (A, V\<^sub>x', p\<^sub>x')) \<in> ?r"
    using rel
    by (simp only: x_A x'_A)
  show "Inf {?d x b | b. b \<in> BC} = Inf {?d x' b | b. b \<in> BC}"
  proof (cases "V\<^sub>x = {}")
    case True
    hence x_empty: "x = (A, {}, p\<^sub>x)"
      using x_A
      by simp
    have "V\<^sub>x' = {}"
      using anon_hom_empty_iff[OF rel_A] True
      by blast
    hence x'_empty: "x' = (A, {}, p\<^sub>x')"
      using x'_A
      by simp
    show ?thesis
      unfolding x_empty x'_empty inner_empty ..
  next
    case False
    hence x'_ne: "V\<^sub>x' \<noteq> {}"
      using anon_hom_empty_iff[OF rel_A]
      by blast
    have "Inf {?d x b | b. b \<in> BC} = ?d (A, V\<^sub>x, p\<^sub>x) (A, V\<^sub>x, \<lambda> v. R)"
      unfolding x_A
      by (rule inner[OF x_fin False])
    also have "\<dots> = ?d (A, V\<^sub>x', p\<^sub>x') (A, V\<^sub>x', \<lambda> v. R)"
      by (rule swap_dist_avg_invar_anon_hom[OF rel_A])
    also have "\<dots> = Inf {?d x' b | b. b \<in> BC}"
      unfolding x'_A
      by (rule inner[OF x'_fin x'_ne, symmetric])
    finally show ?thesis .
  qed
qed

subsection \<open>Invariance of the Distance-Rationalized Winners\<close>

text \<open>
  Score invariance, one-sided: whatever consensus election b the infimum for E
  ranges over, E' has a partner b' at exactly the same distance — the
  unanimity election with b's ballot on E''s own voter set. Members over
  other voter sets contribute \<infinity> and cannot lower the infimum.
\<close>

lemma swap_score_anon_hom_le:
  fixes
    A :: "'a set" and
    E E' :: "('a, 'v :: wellorder) Election" and
    w :: "'a"
  assumes rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "score (votewise_distance swap l_one_avg) (strong_unanimity_in A) E' w
          \<le> score (votewise_distance swap l_one_avg) (strong_unanimity_in A) E w"
proof -
  let ?d = "votewise_distance swap l_one_avg :: ('a, 'v) Election Distance"
  let ?K = "\<K>\<^sub>\<E> (strong_unanimity_in A) w"
  obtain A\<^sub>1 :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (A\<^sub>1, V, p)"
    using prod_cases3
    by blast
  obtain A\<^sub>2 :: "'a set" and V' :: "'v set" and p' :: "('a, 'v) Profile" where
    E'_eq: "E' = (A\<^sub>2, V', p')"
    using prod_cases3
    by blast
  have E_X: "E \<in> elections_\<A> A" and E'_X: "E' \<in> elections_\<A> A"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  have alts1: "A\<^sub>1 = A" and fin_V: "finite V"
    using E_X
    unfolding E_eq elections_\<A>.simps
    by auto
  have alts2: "A\<^sub>2 = A" and fin_V': "finite V'"
    using E'_X
    unfolding E'_eq elections_\<A>.simps
    by auto
  have E_A: "E = (A, V, p)" and E'_A: "E' = (A, V', p')"
    using E_eq E'_eq alts1 alts2
    by simp_all
  have rel_t: "((A, V, p), (A, V', p')) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    using rel
    by (simp only: E_A E'_A)
  have lb: "Inf (?d E' ` ?K) \<le> y" if y_in: "y \<in> ?d E ` ?K" for y :: "ereal"
  proof -
    from y_in obtain b where b_cons: "b \<in> ?K" and y_eq: "y = ?d E b"
      by blast
    obtain A\<^sub>b :: "'a set" and V\<^sub>b :: "'v set" and p\<^sub>b :: "('a, 'v) Profile" where
      b_eq: "b = (A\<^sub>b, V\<^sub>b, p\<^sub>b)"
      using prod_cases3
      by blast
    obtain R :: "'a Preference_Relation" where
      b_alts: "A\<^sub>b = A" and
      b_ne: "V\<^sub>b \<noteq> {}" and
      R_unan: "\<forall> v \<in> V\<^sub>b. p\<^sub>b v = R"
      using strong_unanimity_in_\<K>\<^sub>\<E>D[OF b_cons[unfolded b_eq]]
      by blast
    have b_A: "b = (A, V\<^sub>b, p\<^sub>b)"
      using b_eq b_alts
      by simp
    show ?thesis
    proof (cases "V\<^sub>b = V")
      case False
      \<comment> \<open>Partners on another voter set are at distance \<open>\<infinity>\<close>.\<close>
      have "y = \<infinity>"
        using False
        unfolding y_eq E_A b_A
        by simp
      thus ?thesis
        by simp
    next
      case True
      \<comment> \<open>b lives on E's own voter set; the matching partner for E' is the
          unanimity-R election on V'.\<close>
      let ?b' = "unanimity_election A V' R"
      have V'_ne: "V' \<noteq> {}"
        using anon_hom_empty_iff[OF rel_t] b_ne True
        by blast
            have "(A, V\<^sub>b, p\<^sub>b) \<in> elections_\<K> (strong_unanimity_in A)"
        using b_cons[unfolded b_A]
        unfolding elections_\<K>.simps
        by blast
      hence b_X: "(A, V\<^sub>b, p\<^sub>b) \<in> elections_\<A> A"
        by (rule subsetD[OF strong_unanimity_elections_subset])
      have "((A, V\<^sub>b, p\<^sub>b), ?b') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
        by (rule unanimity_election_anon_hom_related[OF b_X b_ne R_unan fin_V' V'_ne])
      hence b'_cons: "?b' \<in> ?K"
        by (rule strong_unanimity_in_anon_hom_transfer[OF _ b_cons[unfolded b_A]])
      \<comment> \<open>Both distances collapse to the distance to the constant-R profile,
          + they  agree by the engine lemma.\<close>
      have p\<^sub>b_R: "\<forall> v \<in> V. p\<^sub>b v = R"
        using R_unan True
        by simp
      have b_V: "b = (A, V, p\<^sub>b)"
        using b_A True
        by simp
      have dist_b: "?d E b = ?d (A, V, p) (A, V, \<lambda> v. R)"
        unfolding E_A b_V
        by (rule swap_dist_avg_to_unanimity[OF fin_V p\<^sub>b_R])
      have dist_b': "?d E' ?b' = ?d (A, V', p') (A, V', \<lambda> v. R)"
        unfolding E'_A
        by (rule swap_dist_avg_unanimity_election[OF fin_V'])
      have engine: "?d (A, V, p) (A, V, \<lambda> v. R) = ?d (A, V', p') (A, V', \<lambda> v. R)"
        by (rule swap_dist_avg_invar_anon_hom[OF rel_t])
      have "?d E' ?b' \<in> ?d E' ` ?K"
        using b'_cons
        by blast
      hence "Inf (?d E' ` ?K) \<le> ?d E' ?b'"
        by (rule Inf_lower)
      also have "?d E' ?b' = y"
        unfolding y_eq
        by (simp only: dist_b dist_b' engine)
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding score.simps
    using lb
    by (blast intro: Inf_greatest)
qed

text \<open>
  Score invariance: both inequalities via symmetry of the relation.
\<close>

lemma swap_score_invar_anon_hom:
  fixes
    A :: "'a set" and
    E E' :: "('a, 'v :: wellorder) Election" and
    w :: "'a"
  assumes rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  shows "score (votewise_distance swap l_one_avg) (strong_unanimity_in A) E w
           = score (votewise_distance swap l_one_avg) (strong_unanimity_in A) E' w"

proof -
  have "sym (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A))"
    using anon_hom_equiv
    unfolding equiv_def
    by blast
  hence rel': "(E', E) \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
    using rel
    unfolding sym_def
    by blast
    show ?thesis
    using swap_score_anon_hom_le[OF rel, where w = w]
          swap_score_anon_hom_le[OF rel', where w = w]
    by order
qed

text \<open>
  Bridge lemma (generic in d and C, so it can live in the result locale):
  invariant scores make the arg-min, hence the winners, invariant. Both
  related elections have alternative set A, so they share the candidate set
  limit A UNIV. Combined with swap_score_invar_anon_hom at instantiation
  time, this discharges the invar_dr assumption of
  invar_dr_simple_dist_imp_quotient_dr_winners.
\<close>

lemma (in result) anon_hom_score_invar_imp_invar_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    A :: "'a set"
 assumes score_invar:
    "\<And> E E' w. (E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)
        \<Longrightarrow> score d C E w = score d C E' w"
  shows "is_symmetry (fun\<^sub>\<E> (\<R>\<^sub>\<W> d C))
  (Invariance (anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)))"
proof (unfold is_symmetry.simps, intro allI impI)
  fix E E' :: "('a, 'v) Election"
  assume rel: "(E, E') \<in> anonymity_homogeneity\<^sub>\<R> (elections_\<A> A)"
  obtain A\<^sub>1 V p where E_eq: "E = (A\<^sub>1, V, p)"
    using prod_cases3 by blast
 obtain A\<^sub>2 V' p' where E'_eq: "E' = (A\<^sub>2, V', p')"
    using prod_cases3 by blast
  have "E \<in> elections_\<A> A" and "E' \<in> elections_\<A> A"
    using rel
    unfolding anonymity_homogeneity\<^sub>\<R>.simps
    by blast+
  hence alts: "A\<^sub>1 = A" and alts': "A\<^sub>2 = A"
    unfolding E_eq E'_eq elections_\<A>.simps
  by auto
  have "score d C (A\<^sub>1, V, p) = score d C (A\<^sub>2, V', p')"
  proof (rule ext)
    fix w
    show "score d C (A\<^sub>1, V, p) w = score d C (A\<^sub>2, V', p') w"
      using score_invar[OF rel]
      by (simp only: E_eq E'_eq)
  qed
 hence "arg_min_set (score d C (A\<^sub>1, V, p)) (limit A\<^sub>1 UNIV)
           = arg_min_set (score d C (A\<^sub>2, V', p')) (limit A\<^sub>2 UNIV)"
   using alts alts'
   by simp
  thus "fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E = fun\<^sub>\<E> (\<R>\<^sub>\<W> d C) E'"
    unfolding E_eq E'_eq
    by simp
qed


end