(*  File:       Profile.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Preference Profile\<close>

theory Profile
  imports Preference_Relation
          Auxiliary_Lemmas
          "HOL-Library.Extended_Nat"
begin

text \<open>
  Preference profiles denote the decisions made by the individual voters on
  the eligible alternatives. They are represented in the form of one preference
  relation (e.g., selected on a ballot) per voter, collectively captured in a
  mapping of voters onto their respective preference relations.
  If there are finitely many voters, they can be enumerated and the mapping can
  be interpreted as a list of preference relations.
  Unlike the common preference profiles in the social-choice sense, the
  profiles described here consider only the (sub-)set of alternatives that are
  received.
\<close>

subsection \<open>Definition\<close>

text \<open>
  A profile contains one ballot for each voter.
  An election consists of a set of participating voters,
  a set of eligible alternatives, and a corresponding profile.
\<close>

type_synonym ('a, 'v) Profile = "'v \<Rightarrow> ('a Preference_Relation)"

type_synonym ('a, 'v) Election = "'a set \<times> 'v set \<times> ('a, 'v) Profile"

fun alternatives_\<E> :: "('a, 'v) Election \<Rightarrow> 'a set" where
  "alternatives_\<E> E = fst E"

fun voters_\<E> :: "('a, 'v) Election \<Rightarrow> 'v set" where
  "voters_\<E> E = fst (snd E)"

fun profile_\<E> :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Profile" where
  "profile_\<E> E = snd (snd E)"

fun election_equality :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> bool" where
  "election_equality (A, V, p) (A', V', p') =
        (A = A' \<and> V = V' \<and> (\<forall> v \<in> V. p v = p' v))"

text \<open>
  A profile on a set of alternatives A and a voter set V consists of ballots
  that are linear orders on A for all voters in V.
  A finite profile is one with finitely many alternatives and voters.
\<close>

definition profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "profile V A p \<equiv> \<forall> v \<in> V. linear_order_on A (p v)"

abbreviation finite_profile :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> bool" where
  "finite_profile V A p \<equiv> finite A \<and> finite V \<and> profile V A p"

abbreviation finite_election :: "('a, 'v) Election \<Rightarrow> bool" where
  "finite_election E \<equiv> finite_profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

abbreviation finite_\<V>_election :: "('a, 'v) Election \<Rightarrow> bool" where
  "finite_\<V>_election E \<equiv> finite (voters_\<E> E)"

abbreviation well_formed_election :: "('a, 'v) Election \<Rightarrow> bool" where
  "well_formed_election E \<equiv> profile (voters_\<E> E) (alternatives_\<E> E) (profile_\<E> E)"

definition finite_\<V>_elections :: "('a, 'v) Election set" where
  "finite_\<V>_elections \<equiv> {E :: ('a, 'v) Election. finite_\<V>_election E}"

definition finite_elections :: "('a, 'v) Election set" where
  "finite_elections \<equiv> {E :: ('a, 'v) Election. finite_election E}"

definition well_formed_elections :: "('a, 'v) Election set" where
  "well_formed_elections \<equiv> {E :: ('a, 'v) Election. well_formed_election E}"

definition well_formed_finite_\<V>_elections :: "('a, 'v) Election set" where
  "well_formed_finite_\<V>_elections \<equiv>
      {E :: ('a, 'v) Election. finite_\<V>_election E \<and> well_formed_election E}"

lemma well_formed_and_finite_\<V>_elections:
  "well_formed_finite_\<V>_elections = well_formed_elections \<inter> finite_\<V>_elections"
  unfolding finite_\<V>_elections_def well_formed_elections_def
            well_formed_finite_\<V>_elections_def
  using Collect_conj_eq Int_commute
  by metis

\<comment> \<open>This function subsumes elections with fixed alternatives, finite voters, and
    a default value for the profile value on non-voters.\<close>
fun elections_\<A> :: "'a set \<Rightarrow> ('a, 'v) Election set" where
  "elections_\<A> A =
        well_formed_elections
      \<inter> {E. alternatives_\<E> E = A \<and> finite (voters_\<E> E)
            \<and> (\<forall> v. v \<notin> voters_\<E> E \<longrightarrow> profile_\<E> E v = {})}"

\<comment> \<open>Here, we count the occurrences of a ballot in an election,
    i.e., how many voters specifically chose that exact ballot.\<close>
fun vote_count :: "'a Preference_Relation \<Rightarrow> ('a, 'v) Election \<Rightarrow> nat" where
  "vote_count p E = card {v \<in> (voters_\<E> E). (profile_\<E> E) v = p}"

subsection \<open>Voter Permutations\<close>

text \<open>
  A common action of interest on elections is renaming the voters,
  e.g., when talking about anonymity.
\<close>

fun rename :: "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "rename \<pi> (A, V, p) = (A, \<pi> ` V, p \<circ> (the_inv \<pi>))"

lemma rename_sound:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    prof: "profile V A p" and
    renamed: "(A, V', q) = rename \<pi> (A, V, p)" and
    bij_perm: "bij \<pi>"
  shows "profile V' A q"
proof (unfold profile_def, safe)
  fix v' :: "'v"
  assume "v' \<in> V'"
  moreover have "V' = \<pi> ` V"
    using renamed
    by simp
  ultimately have "((the_inv \<pi>) v') \<in> V"
    using UNIV_I bij_perm bij_is_inj bij_is_surj
          f_the_inv_into_f inj_image_mem_iff
    by metis
  thus "linear_order_on A (q v')"
    using renamed bij_perm prof
    unfolding profile_def
    by simp
qed

lemma rename_prof:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "profile V A p" and
    "(A, V', q) = rename \<pi> (A, V, p)" and
    "bij \<pi>"
  shows "profile V' A q"
  using assms rename_sound
  by metis

lemma rename_finite:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "finite V" and
    "(A, V', q) = rename \<pi> (A, V, p)" and
    "bij \<pi>"
  shows "finite V'"
  using assms 
  by simp

lemma rename_inv:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v" and
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes "bij \<pi>"
  shows "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
proof -
  have "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) =
        (A, \<pi> ` (the_inv \<pi>) ` V, p \<circ> (the_inv (the_inv \<pi>)) \<circ> (the_inv \<pi>))"
    by simp
  moreover have "\<pi> ` (the_inv \<pi>) ` V = V"
    using assms
    by (simp add: f_the_inv_into_f_bij_betw image_comp)
  moreover have "(the_inv (the_inv \<pi>)) = \<pi>"
    using assms surj_def inj_on_the_inv_into surj_imp_inv_eq the_inv_f_f
    unfolding bij_betw_def
    by (metis (mono_tags, opaque_lifting))
  moreover have "\<pi> \<circ> (the_inv \<pi>) = id"
    using assms f_the_inv_into_f_bij_betw
    by fastforce
  ultimately show "rename \<pi> (rename (the_inv \<pi>) (A, V, p)) = (A, V, p)"
    by (simp add: rewriteR_comp_comp)
qed

lemma rename_inj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows "inj (rename \<pi>)"
proof (unfold inj_def split_paired_All rename.simps, safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    v :: "'v"
  assume
    "p \<circ> the_inv \<pi> = p' \<circ> the_inv \<pi>" and
    "\<pi> ` V = \<pi> ` V'"
  thus
    "v \<in> V \<Longrightarrow> v \<in> V'" and
    "v \<in> V' \<Longrightarrow> v \<in> V" and
    "p = p'"
    using assms
    by (metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_imp_inj_on inj_image_eq_iff,
        metis bij_betw_the_inv_into bij_is_surj surj_fun_eq)
qed

lemma rename_surj:
  fixes \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    "rename \<pi> ` well_formed_elections = well_formed_elections" and
    "rename \<pi> ` finite_elections = finite_elections"
proof (safe)
  fix
    A A' :: "'a set" and
    V V' :: "'v set" and
    p p' :: "('a, 'v) Profile"
  assume wf: "(A, V, p) \<in> well_formed_elections"
  hence "rename (the_inv \<pi>) (A, V, p) \<in> well_formed_elections"
    using assms bij_betw_the_inv_into rename_sound
    unfolding well_formed_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` well_formed_elections"
    using assms image_eqI rename_inv
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> well_formed_elections"
    using rename_sound wf assms
    unfolding well_formed_elections_def
    by fastforce
next
  fix
    A A' :: "'b set" and
    V V' :: "'v set" and
    p p' :: "('b, 'v) Profile"
  assume finite: "(A, V, p) \<in> finite_elections"
  hence "rename (the_inv \<pi>) (A, V, p) \<in> finite_elections"
    using assms bij_betw_the_inv_into rename_prof rename_finite
    unfolding finite_elections_def
    by fastforce
  thus "(A, V, p) \<in> rename \<pi> ` finite_elections"
    using assms image_eqI rename_inv
    by metis
  assume "(A', V', p') = rename \<pi> (A, V, p)"
  thus "(A', V', p') \<in> finite_elections"
    using rename_sound finite assms
    unfolding finite_elections_def
    by fastforce
qed

subsection \<open>List Representation\<close>

text \<open>
  A profile on a voter set that has a natural order can be viewed as a list of ballots.
\<close>

fun to_list :: "'v :: linorder set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        ('a Preference_Relation) list" where
  "to_list V p = (if finite V
                    then map p (sorted_list_of_set V)
                    else [])"

lemma map_helper:
  fixes
    f :: "'x \<Rightarrow> 'y \<Rightarrow> 'z" and
    g :: "'x \<Rightarrow> 'x" and
    h :: "'y \<Rightarrow> 'y" and
    l :: "'x list" and
    l' :: "'y list"
  shows "map2 f (map g l) (map h l') = map2 (\<lambda> x y. f (g x) (h y)) l l'"
proof -
  have "map2 f (map g l) (map h l') =
          map (\<lambda> (x, y). f x y) (map (\<lambda> (x, y). (g x, h y)) (zip l l'))"
    using zip_map_map
    by metis
  thus ?thesis
    by force
qed

lemma to_list_simp:
  fixes
    i :: "nat" and
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile"
  assumes "i < card V"
  shows "(to_list V p)!i = p ((sorted_list_of_set V)!i)"
  using assms
  by force

lemma to_list_comp:
  fixes
    V :: "'v :: linorder set" and
    p :: "('a, 'v) Profile" and
    f :: "'a rel \<Rightarrow> 'a rel"
  shows "to_list V (f \<circ> p) = map f (to_list V p)"
  by simp

lemma set_card_upper_bound:
  fixes
    i :: "nat" and
    V :: "nat set"
  assumes
    fin_V: "finite V" and
    bound_v: "\<forall> v \<in> V. v < i"
  shows "card V \<le> i"
proof (cases "V = {}")
  case True
  thus ?thesis
    by simp
next
  case False
  hence "Max V \<in> V"
    using fin_V
    by simp
  thus ?thesis
    using assms Suc_leI card_le_Suc_Max order_trans
    by metis
qed

subsection \<open>Preference Counts\<close>

text \<open>
  The win count for an alternative a with respect to a finite voter set V in a profile p is
  the amount of ballots from V in p that rank alternative a in first position.
  If the voter set is infinite, counting is not generally possible.
\<close>

fun win_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> enat" where
  "win_count V p a = (if finite V
    then card {v \<in> V. above (p v) a = {a}} else \<infinity>)"

fun prefer_count :: "'v set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> enat" where
  "prefer_count V p x y = (if finite V
      then card {v \<in> V. let r = (p v) in (y \<preceq>\<^sub>r x)} else \<infinity>)"

lemma pref_count_voter_set_card:
  fixes
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a b :: "'a"
  assumes "finite V"
  shows "prefer_count V p a b \<le> card V"
  using assms
  by (simp add: card_mono)

lemma set_compr:
  fixes
    A :: "'a set" and
    f :: "'a \<Rightarrow> 'a set"
  shows "{f x | x. x \<in> A} = f ` A"
  by blast

lemma pref_count_set_compr:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  shows "{prefer_count V p a a' | a'. a' \<in> A - {a}} =
            (prefer_count V p a) ` (A - {a})"
  by blast

lemma pref_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    a b :: "'a"
  assumes
    prof: "profile V A p" and
    fin: "finite V" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    neq: "a \<noteq> b"
  shows "prefer_count V p a b = card V - (prefer_count V p b a)"
proof -
  have "\<forall> v \<in> V. let r = (p v) in \<not> b \<preceq>\<^sub>r a \<longrightarrow> a \<preceq>\<^sub>r b"
    using a_in_A b_in_A prof lin_ord_imp_connex
    unfolding profile_def connex_def
    by metis
  moreover have "\<forall> v \<in> V. (b, a) \<in> (p v) \<longrightarrow> (a, b) \<notin> (p v)"
    using antisymD neq lin_imp_antisym prof
    unfolding profile_def
    by metis
  ultimately have
    "{v \<in> V. let r = p v in b \<preceq>\<^sub>r a} =
        V - {v \<in> V. let r = p v in a \<preceq>\<^sub>r b}"
    by auto
  thus ?thesis
    using fin
    by (simp add: card_Diff_subset)
qed

lemma pref_count_sym:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a b c :: "'a"
  assumes
    pref_count_ineq: "prefer_count V p a c \<ge> prefer_count V p c b" and
    prof: "profile V A p" and
    a_in_A: "a \<in> A" and
    b_in_A: "b \<in> A" and
    c_in_A: "c \<in> A" and
    a_neq_c: "a \<noteq> c" and
    c_neq_b: "c \<noteq> b"
  shows "prefer_count V p b c \<ge> prefer_count V p c a"
proof (cases "finite V")
  case True
  moreover have
    "prefer_count V p c a \<in> \<nat>" and
    "prefer_count V p b c \<in> \<nat>"
    unfolding Nats_def
    using True of_nat_eq_enat
    by (simp, simp)
  moreover have "prefer_count V p c a \<le> card V"
    using True prof pref_count_voter_set_card
    by metis
  moreover have
    "prefer_count V p a c = card V - (prefer_count V p c a)" and
    "prefer_count V p c b = card V - (prefer_count V p b c)"
    using True pref_count prof c_in_A
    by (metis (no_types, opaque_lifting) a_in_A a_neq_c,
        metis (no_types, opaque_lifting) b_in_A c_neq_b)
  ultimately show ?thesis
    using pref_count_ineq
    by simp
next
  case False
  thus ?thesis
    by simp
qed

lemma empty_prof_imp_zero_pref_count:
  fixes
    p :: "('a, 'v) Profile" and
    V :: "'v set" and
    a b :: "'a"
  assumes "V = {}"
  shows "prefer_count V p a b = 0"
  unfolding zero_enat_def
  using assms
  by simp

fun wins :: "'v set \<Rightarrow> 'a \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins V a p b =
    (prefer_count V p a b > prefer_count V p b a)"

lemma wins_inf_voters:
  fixes
    p :: "('a, 'v) Profile" and
    a b :: "'a" and
    V :: "'v set"
  assumes "infinite V"
  shows "\<not> wins V b p a"
  using assms
  by simp

text \<open>
  Having alternative \<open>a\<close> win against \<open>b\<close> implies that \<open>b\<close> does not win against \<open>a\<close>.
\<close>

lemma wins_antisym:
  fixes
    p :: "('a, 'v) Profile" and
    a b :: "'a" and
    V :: "'v set"
  assumes "wins V a p b" \<comment> \<open>This already implies that \<open>V\<close> is finite.\<close>
  shows "\<not> wins V b p a"
  using assms
  by simp

lemma wins_irreflex:
  fixes
    p :: "('a, 'v) Profile" and
    a :: "'a" and
    V :: "'v set"
  shows "\<not> wins V a p a"
  using wins_antisym
  by metis

subsection \<open>Condorcet Winner\<close>

fun condorcet_winner :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "condorcet_winner V A p a =
      (finite_profile V A p \<and> a \<in> A \<and> (\<forall> x \<in> A - {a}. wins V a p x))"
(*
Could this be defined via
  "for all b \<noteq> a there is an injective map
    from ballots where b wins to ballots where a wins"
instead of prefer_count for infinite voter sets?
*)

lemma cond_winner_unique_eq:
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "condorcet_winner V A p b"
  shows "b = a"
proof (rule ccontr)
  assume b_neq_a: "b \<noteq> a"
  hence "wins V b p a"
    using insert_Diff insert_iff assms
    by simp
  hence "\<not> wins V a p b"
    by (simp add: wins_antisym)
  moreover have "wins V a p b"
    using Diff_iff b_neq_a singletonD assms
    by auto
  ultimately show False
    by simp
qed

lemma cond_winner_unique:
  fixes
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "condorcet_winner V A p a"
  shows "{a' \<in> A. condorcet_winner V A p a'} = {a}"
proof (safe)
  fix a' :: "'a"
  assume "condorcet_winner V A p a'"
  thus "a' = a"
    using assms cond_winner_unique_eq
    by metis
next
  show "a \<in> A"
    using assms
    unfolding condorcet_winner.simps
    by (metis (no_types))
next
  show "condorcet_winner V A p a"
    using assms
    by presburger
qed

lemma cond_winner_unique':
  fixes
    V :: "'v set" and
    A :: "'a set" and
    p :: "('a, 'v) Profile" and
    a b :: "'a"
  assumes
    "condorcet_winner V A p a" and
    "b \<noteq> a"
  shows "\<not> condorcet_winner V A p b"
  using cond_winner_unique_eq assms
  by metis

subsection \<open>Limited Profile\<close>

text \<open>
  This function restricts a profile p to a set A of alternatives and
  a set V of voters s.t. voters outside of V do not have any preferences or
  do not cast a vote.
  This keeps all of A's preferences.
\<close>

fun limit_profile :: "'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow> ('a, 'v) Profile" where
  "limit_profile A p = (\<lambda> v. limit A (p v))"

lemma limit_prof_trans:
  fixes
    A B C :: "'a set" and
    p :: "('a, 'v) Profile"
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B"
  shows "limit_profile C p = limit_profile C (limit_profile B p)"
  using assms
  by auto

lemma limit_profile_sound:
  fixes
    A B :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile"
  assumes
    "profile V B p" and
    "A \<subseteq> B"
  shows "profile V A (limit_profile A p)"
proof (unfold profile_def)
  have "\<forall> v \<in> V. linear_order_on A (limit A (p v))"
    using assms limit_presv_lin_ord
    unfolding profile_def
    by metis
  thus "\<forall> v \<in> V. linear_order_on A ((limit_profile A p) v)"
    by simp
qed

subsection \<open>Lifting Property\<close>

definition equiv_prof_except_a :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv_prof_except_a V A p p' a \<equiv>
    profile V A p \<and> profile V A p' \<and> a \<in> A \<and>
      (\<forall> v \<in> V. equiv_rel_except_a A (p v) (p' v) a)"

text \<open>
  An alternative gets lifted from one profile to another iff
  its ranking increases in at least one ballot, and nothing else changes.
\<close>

definition lifted :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('a, 'v) Profile \<Rightarrow>
        ('a, 'v) Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted V A p p' a \<equiv>
    finite_profile V A p \<and> finite_profile V A p' \<and> a \<in> A
      \<and> (\<forall> v \<in> V. \<not> Preference_Relation.lifted A (p v) (p' v) a \<longrightarrow> (p v) = (p' v))
      \<and> (\<exists> v \<in> V. Preference_Relation.lifted A (p v) (p' v) a)"

lemma lifted_imp_equiv_prof_except_a:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes "lifted V A p p' a"
  shows "equiv_prof_except_a V A p p' a"
proof (unfold equiv_prof_except_a_def, safe)
  show
    "profile V A p" and
    "profile V A p'" and
    "a \<in> A"
    using assms
    unfolding lifted_def
    by (metis, metis, metis)
next
  fix v :: "'v"
  assume "v \<in> V"
  thus "equiv_rel_except_a A (p v) (p' v) a"
    using assms lifted_imp_equiv_rel_except_a trivial_equiv_rel
    unfolding lifted_def profile_def
    by (metis (no_types))
qed

lemma negl_diff_imp_eq_limit_prof:
  fixes
    A A' :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    change: "equiv_prof_except_a V A' p q a" and
    subset: "A \<subseteq> A'" and
    not_in_A: "a \<notin> A"
  shows "\<forall> v \<in> V. (limit_profile A p) v = (limit_profile A q) v"
  \<comment> \<open>With the current definitions of \<open>equiv_prof_except_a\<close> and \<open>limit_prof\<close>, we can
      only conclude that the limited profiles coincide on the given voter set, since
      \<open>limit_prof\<close> may change the profiles everywhere, while \<open>equiv_prof_except_a\<close>
      only makes statements about the voter set.\<close>
proof (clarify)
  fix v :: 'v
  assume "v \<in> V"
  hence "equiv_rel_except_a A' (p v) (q v) a"
    using change equiv_prof_except_a_def
    by metis
  thus "limit_profile A p v = limit_profile A q v"
    using subset not_in_A negl_diff_imp_eq_limit
    by simp
qed

lemma limit_prof_eq_or_lifted:
  fixes
    A A' :: "'a set" and
    V :: "'v set" and
    p p' :: "('a, 'v) Profile" and
    a :: "'a"
  assumes
    lifted_a: "lifted V A' p p' a" and
    subset: "A \<subseteq> A'"
  shows "(\<forall> v \<in> V. limit_profile A p v = limit_profile A p' v)
        \<or> lifted V A (limit_profile A p) (limit_profile A p') a"
proof (cases "a \<in> A")
  case True
  have "\<forall> v \<in> V. Preference_Relation.lifted A' (p v) (p' v) a \<or> (p v) = (p' v)"
    using lifted_a
    unfolding lifted_def
    by metis
  hence one:
    "\<forall> v \<in> V.
         Preference_Relation.lifted A (limit A (p v)) (limit A (p' v)) a \<or>
           (limit A (p v)) = (limit A (p' v))"
    using limit_lifted_imp_eq_or_lifted subset
    by metis
  thus ?thesis
  proof (cases "\<forall> v \<in> V. limit A (p v) = limit A (p' v)")
    case True
    thus ?thesis
      by simp
  next
    case False
    let ?p = "limit_profile A p"
    let ?q = "limit_profile A p'"
    have
      "profile V A ?p" and
      "profile V A ?q"
      using lifted_a subset limit_profile_sound
      unfolding lifted_def
      by (safe, safe)
    moreover have
      "\<exists> v \<in> V. Preference_Relation.lifted A (?p v) (?q v) a"
      using False one
      unfolding limit_profile.simps
      by (metis (no_types, lifting))
    ultimately have "lifted V A ?p ?q a"
      using True lifted_a one rev_finite_subset subset
      unfolding lifted_def limit_profile.simps
      by (metis (no_types, lifting))
    thus ?thesis
      by simp
  qed
next
  case False
  thus ?thesis
    using lifted_a negl_diff_imp_eq_limit_prof subset lifted_imp_equiv_prof_except_a
    by metis
qed

end