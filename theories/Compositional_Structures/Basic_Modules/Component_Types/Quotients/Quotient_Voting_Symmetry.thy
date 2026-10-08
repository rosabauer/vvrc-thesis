(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotients/Quotient_Voting_Symmetry.thy
*)
\<^marker>‹creator "Rosa Bauer, LMU Munich"›

section ‹Symmetry of Quotient Voting Rules›

theory Quotient_Voting_Symmetry
  imports Election_Quotients
          "../Electoral_Module"
begin

text ‹
  This theory transfers the symmetry properties of electoral modules from
  well-formed elections to the quotient of the elections over a fixed
  alternative set ‹A› under the anonymity-homogeneity relation. For
  neutrality and reversal symmetry it establishes the premises of
  ‹pass_to_quotient_equivar'›: the transformations are compatible with the
  relation, they are invertible on ‹elections_𝒜 A›, and the property on
  well-formed elections restricts to an equivariance on ‹elections_𝒜 A›.
  For neutrality, the transformations have to be restricted to the
  stabilizer of ‹A›, since only those keep the alternative set fixed; the
  main result is ‹neutrality_lifts_to_anon_hom_quotient›. Voter renamings
  act trivially on the quotient (‹anon_acts_trivially_on_quotient›), so
  anonymity is built into the quotient rather than being a symmetry of it.
›

subsection ‹The Alternative-Set Stabilizer›

text ‹
  In group theory, stabilizers are restrictions on a set 
  that state that an operation never maps the elements of a set, 
  in this case the election alternatives, outside of the set,
  but only switches them bijectively within the set.
  They are  the neutrality symmetries that descend to
  the anon-hom quotient over A (and thus to the simplex).
›

definition alt_stabilizer :: "'a set ⇒ ('a ⇒ 'a) set" where
  "alt_stabilizer A = {π ∈ carrier bijection⇩𝒜⇩𝒢. π ` A = A}"

lemma alt_stabilizer_rewrite:
  fixes A :: "'a set"
  shows "alt_stabilizer A = {π. bij π ∧ π ` A = A}"
  unfolding alt_stabilizer_def bijection⇩𝒜⇩𝒢_def
  using rewrite_carrier
  by blast

lemma φ_neutral_apply:
  fixes
    𝒳 :: "('a, 'v) Election set" and
    π :: "'a ⇒ 'a" and
    E :: "('a, 'v) Election"
  assumes "E ∈ 𝒳"
  shows "φ_neutral 𝒳 π E = alts_rename π E"
  by (simp only: φ_neutral.simps extensional_continuation.simps if_P[OF assms])
  
subsection ‹Auxiliary Lemmas on Renaming›

lemma rel_rename_id: "rel_rename id = id"
proof
  fix r :: "'a rel"
  show "rel_rename id r = id r"
    unfolding rel_rename.simps
    by force
qed

lemma rel_rename_empty: "rel_rename π {} = {}"
  unfolding rel_rename.simps
  by blast

lemma alts_rename_id:
  fixes E :: "('a, 'v) Election"
  shows "alts_rename id E = E"
  by (cases E) (simp add: rel_rename_id)

lemma bij_the_inv_comp:
  fixes π :: "'a ⇒ 'a"
  assumes bij_π: "bij π"
  shows
    "the_inv π ∘ π = id" and
    "π ∘ the_inv π = id"
proof -
  show "the_inv π ∘ π = id"
    using bij_π
    by (simp add: fun_eq_iff bij_is_inj the_inv_f_f)
  show "π ∘ the_inv π = id"
  proof
    fix x :: "'a"
    show "(π ∘ the_inv π) x = id x"
      using bij_π f_the_inv_into_f_bij_betw
      by fastforce 
  qed
qed

lemma alt_stabilizer_the_inv_closed:
  fixes
    A :: "'a set" and
    π :: "'a ⇒ 'a"
  assumes "π ∈ alt_stabilizer A"
  shows "the_inv π ∈ alt_stabilizer A"
proof -
  have bij_π: "bij π" and img_A: "π ` A = A"
    using assms
    unfolding alt_stabilizer_rewrite
    by simp_all
  have "bij (the_inv π)"
    using bij_π bij_betw_the_inv_into
    by blast
  moreover have "the_inv π ` A = A"
  proof -
    have "the_inv π ` A = the_inv π ` (π ` A)"
      using img_A
      by simp
    also have "… = (the_inv π ∘ π) ` A"
      by (simp add: image_comp)
    also have "… = A"
      using bij_the_inv_comp[OF bij_π]
      by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis
    using alt_stabilizer_rewrite
    by blast
qed

subsection ‹Stabilizer Renaming Preserves Fixed-Alternative Elections›

lemma stabilizer_preserves_elections_𝒜:
  fixes
    A :: "'a set" and
    π :: "'a ⇒ 'a" and
    E :: "('a, 'v) Election"
  assumes
    stab: "π ∈ alt_stabilizer A" and
    elect: "E ∈ elections_𝒜 A"
  shows "alts_rename π E ∈ elections_𝒜 A"
proof -
  have bij_π: "bij π" and img_A: "π ` A = A"
    using assms
    unfolding alt_stabilizer_rewrite
    by simp_all
  obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (B, V, p)"
    using prod_cases3
    by blast
  have B_eq_A: "B = A" and
       fin_V: "finite V" and
       def_prof: "∀ v. v ∉ V ⟶ p v = {}" and
       wf: "(B, V, p) ∈ well_formed_elections"
    using elect E_eq
    unfolding elections_𝒜.simps
    by auto
  have ren_eq: "(π ` B, V, rel_rename π ∘ p) = alts_rename π (B, V, p)"
    by simp
  have wf': "(π ` B, V, rel_rename π ∘ p) ∈ well_formed_elections"
    using alternatives_rename_sound[OF bij_π wf ren_eq] .
   have img_B: "π ` B = A"
    using B_eq_A img_A
    by simp
  have def_prof': "∀ v. v ∉ V ⟶ (rel_rename π ∘ p) v = {}"
    using def_prof rel_rename_empty
    by simp
  have ren_E: "alts_rename π E = (π ` B, V, rel_rename π ∘ p)"
    unfolding E_eq
    by simp
  show ?thesis
    unfolding ren_E elections_𝒜.simps
    using wf' img_B fin_V def_prof'
    by simp
qed

subsection ‹Ballot Maps and Vote Fractions›

text ‹
  All transformations considered below leave the voters untouched and act on
  the ballots by a map ‹τ› with a two-sided inverse ‹σ›. Such a map only
  permutes which ballot has which vote count, so vote counts and vote fractions
  are carried along, and related elections stay related.
›

lemma vote_count_profile_map:
  fixes
    τ σ :: "'a Preference_Relation ⇒ 'a Preference_Relation" and
    q :: "'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_στ: "⋀ s. σ (τ s) = s" and
    inv_τσ: "⋀ s. τ (σ s) = s" and
    voters: "voters_ℰ E' = voters_ℰ E" and
    prof: "profile_ℰ E' = τ ∘ profile_ℰ E"
  shows "vote_count q E' = vote_count (σ q) E"
proof -
  have set_eq: "{v ∈ voters_ℰ E. τ (profile_ℰ E v) = q} = {v ∈ voters_ℰ E. profile_ℰ E v = σ q}"
  proof (rule Collect_cong)
    fix v :: "'v"
    show "(v ∈ voters_ℰ E ∧ τ (profile_ℰ E v) = q) = (v ∈ voters_ℰ E ∧ profile_ℰ E v = σ q)"
      using inv_στ inv_τσ
      by metis
  qed
  have "vote_count q E' = card {v ∈ voters_ℰ E. τ (profile_ℰ E v) = q}"
    unfolding vote_count.simps voters prof
    by (simp add: comp_def)
  also have "… = card {v ∈ voters_ℰ E. profile_ℰ E v = σ q}"
    by (simp only: set_eq)
  also have "… = vote_count (σ q) E"
    by (simp only: vote_count.simps)
  finally show ?thesis .
qed

lemma vote_fraction_profile_map:
  fixes
    τ σ :: "'a Preference_Relation ⇒ 'a Preference_Relation" and
    q :: "'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_στ: "⋀ s. σ (τ s) = s" and
    inv_τσ: "⋀ s. τ (σ s) = s" and
    voters: "voters_ℰ E' = voters_ℰ E" and
    prof: "profile_ℰ E' = τ ∘ profile_ℰ E"
  shows "vote_fraction q E' = vote_fraction (σ q) E"
  by (simp only: vote_fraction.simps voters vote_count_profile_map[OF inv_στ inv_τσ voters prof])

lemma profile_map_compat:
  fixes
    A :: "'a set" and
    F :: "('a, 'v) Election ⇒ ('a, 'v) Election" and
    τ σ :: "'a Preference_Relation ⇒ 'a Preference_Relation" and
    E E' :: "('a, 'v) Election"
  assumes
    inv_στ: "⋀ s. σ (τ s) = s" and
    inv_τσ: "⋀ s. τ (σ s) = s" and
    voters: "⋀ E. voters_ℰ (F E) = voters_ℰ E" and
    prof: "⋀ E. profile_ℰ (F E) = τ ∘ profile_ℰ E" and
    closed: "⋀ E. E ∈ elections_𝒜 A ⟹ F E ∈ elections_𝒜 A" and
    rel: "(E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  shows "(F E, F E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
proof -
  have E_in: "E ∈ elections_𝒜 A" and
       E'_in: "E' ∈ elections_𝒜 A" and
       fin_eq: "finite (voters_ℰ E) = finite (voters_ℰ E')" and
       frac_eq: "∀ q. vote_fraction q E = vote_fraction q E'"
    using rel
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast+
  have "∀ q. vote_fraction q (F E) = vote_fraction q (F E')"
    using vote_fraction_profile_map[OF inv_στ inv_τσ voters prof] frac_eq
    by metis
  moreover have "finite (voters_ℰ (F E)) = finite (voters_ℰ (F E'))"
    using fin_eq
    unfolding voters .
  ultimately show ?thesis
    using closed[OF E_in] closed[OF E'_in]
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast
qed

subsection ‹Vote Counts and Fractions under Renaming›

text ‹
  Renaming the alternatives with a bijection π permutes the ballots:
  the voters casting ballot r after renaming are exactly the voters casting
  the preimage ballot before renaming. Voters are untouched.
›

lemma rel_rename_the_inv_left:
  fixes
    π :: "'a ⇒ 'a" and
    q :: "'a Preference_Relation"
  assumes bij_π: "bij π"
  shows "rel_rename (the_inv π) (rel_rename π q) = q"
proof -
  have "rel_rename (the_inv π) ∘ rel_rename π = id"
    using rel_rename_compositional[of "the_inv π" π]
          bij_the_inv_comp(1)[OF bij_π] rel_rename_id
    by metis
  thus ?thesis
    by (metis comp_apply id_apply)
qed

lemma rel_rename_the_inv_right:
  fixes
    π :: "'a ⇒ 'a" and
    q :: "'a Preference_Relation"
  assumes bij_π: "bij π"
  shows "rel_rename π (rel_rename (the_inv π) q) = q"
proof -
  have "rel_rename π ∘ rel_rename (the_inv π) = id"
    using rel_rename_compositional[of π "the_inv π"]
          bij_the_inv_comp(2)[OF bij_π] rel_rename_id
    by metis
  thus ?thesis
    by (metis comp_apply id_apply)
qed

lemma alts_rename_voters:
  fixes
    π :: "'a ⇒ 'a" and
    E :: "('a, 'v) Election"
  shows "voters_ℰ (alts_rename π E) = voters_ℰ E"
  by simp

lemma alts_rename_profile:
  fixes
    π :: "'a ⇒ 'a" and
    E :: "('a, 'v) Election"
  shows "profile_ℰ (alts_rename π E) = rel_rename π ∘ profile_ℰ E"
  by simp

lemma vote_count_alts_rename:
  fixes
    π :: "'a ⇒ 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_π: "bij π"
  shows "vote_count r (alts_rename π E) = vote_count (rel_rename (the_inv π) r) E"
  by (rule vote_count_profile_map[OF rel_rename_the_inv_left[OF bij_π]
        rel_rename_the_inv_right[OF bij_π] alts_rename_voters alts_rename_profile])

lemma vote_fraction_alts_rename:
  fixes
    π :: "'a ⇒ 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_π: "bij π"
  shows "vote_fraction r (alts_rename π E) = vote_fraction (rel_rename (the_inv π) r) E"
  by (rule vote_fraction_profile_map[OF rel_rename_the_inv_left[OF bij_π]
        rel_rename_the_inv_right[OF bij_π] alts_rename_voters alts_rename_profile])

subsection ‹Neutrality Action Descends to Anon-Hom Classes›


text ‹
  Compatibility: stabilizer renamings map anonhom-related
  elections to related elections, since they permute vote fractions over
  ballots and leave the voters unchanged.
›

lemma φ_neutral_elections_𝒜_compat:
  fixes A :: "'a set"
  shows "∀ π ∈ alt_stabilizer A. ∀ E E'.
      (E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A) ⟶
        (φ_neutral (elections_𝒜 A) π E, φ_neutral (elections_𝒜 A) π E')
          ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
proof (intro ballI allI impI)
  fix
    π :: "'a ⇒ 'a" and
    E E' :: "('a, 'v) Election"
  assume
    stab: "π ∈ alt_stabilizer A" and
    rel: "(E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  have bij_π: "bij π"
    using stab
    unfolding alt_stabilizer_rewrite
    by simp
  have E_in: "E ∈ elections_𝒜 A" and E'_in: "E' ∈ elections_𝒜 A"
    using rel
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast+
  have "(alts_rename π E, alts_rename π E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
    by (rule profile_map_compat[OF rel_rename_the_inv_left[OF bij_π]
          rel_rename_the_inv_right[OF bij_π] alts_rename_voters alts_rename_profile
          stabilizer_preserves_elections_𝒜[OF stab] rel])
  thus "(φ_neutral (elections_𝒜 A) π E, φ_neutral (elections_𝒜 A) π E')
          ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
    unfolding φ_neutral_apply[OF E_in] φ_neutral_apply[OF E'_in] .
qed

text ‹
  Invertibility in the stabilizer: on elections over A, the renaming by
  \<open>the_inv π\<close> undoes the renaming by π and vice versa.
›

lemma φ_neutral_elections_𝒜_invertible:
  fixes A :: "'a set"
  shows "∀ π ∈ alt_stabilizer A. ∃ σ ∈ alt_stabilizer A. ∀ E ∈ elections_𝒜 A.
      φ_neutral (elections_𝒜 A) σ (φ_neutral (elections_𝒜 A) π E) = E
    ∧ φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) σ E) = E"
proof (intro ballI)
  fix π :: "'a ⇒ 'a"
  assume stab_π: "π ∈ alt_stabilizer A"
  hence stab_σ: "the_inv π ∈ alt_stabilizer A"
    using alt_stabilizer_the_inv_closed
    by blast
   have bij_π: "bij π"
    using stab_π
    unfolding alt_stabilizer_rewrite
    by simp
  have "∀ E ∈ elections_𝒜 A.
      φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E) = E
    ∧ φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E) = E"
  proof (intro ballI)
    fix E :: "('a, 'v) Election"
    assume E_in: "E ∈ elections_𝒜 A"
    have img_π: "alts_rename π E ∈ elections_𝒜 A"
      using stabilizer_preserves_elections_𝒜 stab_π E_in
      by blast
    have img_σ: "alts_rename (the_inv π) E ∈ elections_𝒜 A"
      using stabilizer_preserves_elections_𝒜 stab_σ E_in
      by blast
        have eq_1:
      "φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E) = E"
    proof -
      have "φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E)
          = alts_rename (the_inv π) (alts_rename π E)"
        by (simp only: φ_neutral_apply[OF E_in] φ_neutral_apply[OF img_π])
      also have "… = alts_rename (the_inv π ∘ π) E"
        by (metis alts_rename_compositional comp_apply)
      also have "… = E"
        unfolding bij_the_inv_comp(1)[OF bij_π]
        by (rule alts_rename_id)
      finally show ?thesis .
    qed
    have eq_2:
      "φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E) = E"
    proof -
      have "φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E)
          = alts_rename π (alts_rename (the_inv π) E)"
        by (simp only: φ_neutral_apply[OF E_in] φ_neutral_apply[OF img_σ])
      also have "… = alts_rename (π ∘ the_inv π) E"
        by (metis alts_rename_compositional comp_apply)
      also have "… = E"
        unfolding bij_the_inv_comp(2)[OF bij_π]
        by (rule alts_rename_id)
      finally show ?thesis .
    qed
    show
      "φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E) = E
      ∧ φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E) = E"
      using eq_1 eq_2
      by blast
qed
  thus "∃ σ ∈ alt_stabilizer A. ∀ E ∈ elections_𝒜 A.
      φ_neutral (elections_𝒜 A) σ (φ_neutral (elections_𝒜 A) π E) = E
    ∧ φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) σ E) = E"
    using stab_σ
    by blast
qed

subsection ‹Transfer of Neutrality to the Stabilizer Action›

text ‹
  A rule that is neutral on all well-formed elections is in particular
  equivariant on \<open>elections_𝒜 A\<close> under the stabilizer of A, with the action
  parameterized by \<open>elections_𝒜 A\<close> (the two continuations of
  \<open>alts_rename\<close> match up on \<open>elections_𝒜 A\<close>).
›

lemma (in result_properties) neutrality_in_stabilizer:
  fixes
    m :: "('a, 'v, 'b Result) Electoral_Module" and
    A :: "'a set"
  assumes "neutrality_in well_formed_elections m"
  shows "is_symmetry (fun⇩ℰ m)
      (action_induced_equivariance (alt_stabilizer A) (elections_𝒜 A)
          (φ_neutral (elections_𝒜 A)) (result_action ψ))"
proof -
  have pairs_sub:
    "{(φ_neutral well_formed_elections z, result_action ψ z) | z.
          z ∈ alt_stabilizer A}
      ⊆ {(φ_neutral well_formed_elections z, result_action ψ z) | z.
          z ∈ carrier bijection⇩𝒜⇩𝒢}"
    unfolding alt_stabilizer_def
    by blast
  have sub_dom: "elections_𝒜 A ⊆ well_formed_elections"
    unfolding elections_𝒜.simps
    by blast
  from assms have
    "is_symmetry (fun⇩ℰ m) (Equivariance well_formed_elections
        {(φ_neutral well_formed_elections z, result_action ψ z) | z.
            z ∈ carrier bijection⇩𝒜⇩𝒢})"
    unfolding neutrality_in.simps action_induced_equivariance_def
    by simp
  hence "is_symmetry (fun⇩ℰ m) (Equivariance well_formed_elections
      {(φ_neutral well_formed_elections z, result_action ψ z) | z.
          z ∈ alt_stabilizer A})"
    using equivar_under_subset' pairs_sub
    by blast
  hence "is_symmetry (fun⇩ℰ m) (Equivariance (elections_𝒜 A)
      {(φ_neutral well_formed_elections z, result_action ψ z) | z.
          z ∈ alt_stabilizer A})"
    using equivar_under_subset sub_dom
    by blast
  hence wfe_act: "is_symmetry (fun⇩ℰ m)
      (action_induced_equivariance (alt_stabilizer A) (elections_𝒜 A)
          (φ_neutral well_formed_elections) (result_action ψ))"
    unfolding action_induced_equivariance_def
    by simp
  moreover have "∀ π ∈ alt_stabilizer A. ∀ E ∈ elections_𝒜 A.
      φ_neutral well_formed_elections π E = φ_neutral (elections_𝒜 A) π E"
    using sub_dom
    by auto
  ultimately show ?thesis
    using equivar_ind_by_act_coincide
    by blast
qed

subsection ‹Theorem: Neutrality Lifts to the Quotient›

text ‹
  If an electoral module is invariant under the
  anon-hom relation on elections over A (so it induces a
  well-defined quotient rule via π𝒬) and neutral on well-formed elections,
  then the quotient rule is equivariant on the anon-hom classes
  with the stabilizer of A, ie neutral as a rule on the quotient
  (so also on the simplex).
›

theorem (in result_properties) neutrality_lifts_to_anon_hom_quotient:
  fixes
    m :: "('a, 'v, 'b Result) Electoral_Module" and
    A :: "'a set"
  assumes
    invar_m: "is_symmetry (fun⇩ℰ m)
        (Invariance (anonymity_homogeneity⇩ℛ (elections_𝒜 A)))" and
    neutral_m: "neutrality_in well_formed_elections m"
  shows "is_symmetry (π⇩𝒬 (fun⇩ℰ m))
      (action_induced_equivariance (alt_stabilizer A)
          (elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A))
          (set_action (φ_neutral (elections_𝒜 A))) (result_action ψ))"
  using pass_to_quotient_equivar'[OF
          anon_hom_equiv
          invar_m
          neutrality_in_stabilizer[OF neutral_m]
          φ_neutral_elections_𝒜_compat
          φ_neutral_elections_𝒜_invertible] .

subsection ‹Auxiliary Lemmas on Ballot Reversal›

text ‹
  Reversing all ballots is the map \<open>rel_app g\<close> for g in the two-element
  group \<open>reversal⇩𝒢\<close> = {reverse ballots, do nothing}. The lemmas below
  record the obvious computation rules: doing nothing changes nothing,
  two applications compose, and an election
  (alternatives, voters, ballots) transforms as expected.
›

lemma rel_app_id:
  fixes E :: "('a, 'v) Election"
  shows "rel_app id E = E"
  by (cases E) simp

lemma rel_app_comp:
  fixes
    f f' :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  shows "rel_app f (rel_app f' E) = rel_app (f ∘ f') E"
  by (cases E) (simp add: comp_assoc)

lemma rel_app_alts:
  fixes
    f :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  shows "alternatives_ℰ (rel_app f E) = alternatives_ℰ E"
  by (cases E) simp

lemma rel_app_voters:
  fixes
    f :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  shows "voters_ℰ (rel_app f E) = voters_ℰ E"
  by (cases E) simp

lemma rel_app_profile:
  fixes
    f :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  shows "profile_ℰ (rel_app f E) = f ∘ profile_ℰ E"
  by (cases E) simp

lemma reverse_rel_empty: "reverse_rel {} = {}"
  unfolding reverse_rel.simps
  by blast

lemma φ_reverse_apply:
  fixes
    𝒳 :: "('a, 'v) Election set" and
    g :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  assumes "E ∈ 𝒳"
  shows "φ_reverse 𝒳 g E = rel_app g E"
  by (simp only: φ_reverse.simps extensional_continuation.simps if_P[OF assms])

lemma reversal_carrier_elems:
  fixes g :: "'a rel ⇒ 'a rel"
  assumes "g ∈ carrier reversal⇩𝒢"
  shows "g = reverse_rel ∨ g = id"
  using assms
  unfolding reversal⇩𝒢_def
  by auto 

lemma reversal_carrier_invol:
  fixes g :: "'a rel ⇒ 'a rel"
  assumes "g ∈ carrier reversal⇩𝒢"
  shows "g ∘ g = id"
  using reversal_carrier_elems[OF assms] reverse_reverse_id
  by fastforce 

lemma reversal_carrier_invol_pointwise:
  fixes
    g :: "'a rel ⇒ 'a rel" and
    s :: "'a rel"
  assumes "g ∈ carrier reversal⇩𝒢"
  shows "g (g s) = s"
  using reversal_carrier_invol[OF assms] comp_apply id_apply
  by metis

lemma reversal_carrier_empty:
  fixes g :: "'a rel ⇒ 'a rel"
  assumes "g ∈ carrier reversal⇩𝒢"
  shows "g {} = {}"
  using reversal_carrier_elems[OF assms] reverse_rel_empty
  by fastforce 

subsection ‹Reversal Action on Anon-Hom Classes›

text ‹
  Reversing ballots keeps an election over A inside the elections over A:
  the alternatives and voters are untouched, a reversed linear order over A
  is again a linear order over A, and empty ballots stay empty.
  The well-formedness part is inherited from the existing group action
  of \<open>reversal⇩𝒢\<close> on all well-formed elections.
›

lemma reversal_preserves_elections_𝒜:
  fixes
    A :: "'a set" and
    g :: "'a rel ⇒ 'a rel" and
    E :: "('a, 'v) Election"
  assumes
    g_in: "g ∈ carrier reversal⇩𝒢" and
    elect: "E ∈ elections_𝒜 A"
  shows "rel_app g E ∈ elections_𝒜 A"
proof -
  have wfe_E: "E ∈ well_formed_elections" and
       alt_E: "alternatives_ℰ E = A" and
       fin_E: "finite (voters_ℰ E)" and
       def_E: "∀ v. v ∉ voters_ℰ E ⟶ profile_ℰ E v = {}"
    using elect
    unfolding elections_𝒜.simps
    by auto
  have "φ_reverse well_formed_elections g E ∈ well_formed_elections"
    using φ_reverse_action.element_image g_in wfe_E
    by metis
  moreover have "φ_reverse well_formed_elections g E = rel_app g E"
    by (rule φ_reverse_apply[OF wfe_E])
  ultimately have wf': "rel_app g E ∈ well_formed_elections"
    by simp
  have alts': "alternatives_ℰ (rel_app g E) = A"
    by (simp only: rel_app_alts alt_E)
  have fin': "finite (voters_ℰ (rel_app g E))"
    using fin_E
    by (cases E) simp
  have def': "∀ v. v ∉ voters_ℰ (rel_app g E) ⟶ profile_ℰ (rel_app g E) v = {}"
  proof (intro allI impI)
    fix v :: "'v"
    assume "v ∉ voters_ℰ (rel_app g E)"
    hence "profile_ℰ E v = {}"
      using def_E
      by (cases E) simp
    thus "profile_ℰ (rel_app g E) v = {}"
      using reversal_carrier_empty[OF g_in]
      by (cases E) simp
  qed
  show ?thesis
    unfolding elections_𝒜.simps
    using wf' alts' fin' def'
    by blast
qed

text ‹
  Counting: the voters who cast ballot q after all ballots are reversed
  are exactly the voters who cast the reversed ballot before, since
  reversing twice is doing nothing. The voter set itself stays the same,
  so the same holds for vote fractions.
›

lemma vote_count_rel_app:
  fixes
    g :: "'a rel ⇒ 'a rel" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes g_in: "g ∈ carrier reversal⇩𝒢"
  shows "vote_count q (rel_app g E) = vote_count (g q) E"
  by (rule vote_count_profile_map[OF reversal_carrier_invol_pointwise[OF g_in]
        reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile])

lemma vote_fraction_rel_app:
  fixes
    g :: "'a rel ⇒ 'a rel" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes g_in: "g ∈ carrier reversal⇩𝒢"
  shows "vote_fraction q (rel_app g E) = vote_fraction (g q) E"
  by (rule vote_fraction_profile_map[OF reversal_carrier_invol_pointwise[OF g_in]
        reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile])

text ‹
  Compatibility: if two elections have the same vote fractions, then so do
  their reversed versions, since reversal only permutes which ballot has
  which fraction. So reversal maps related elections to related elections.
›

lemma φ_reverse_elections_𝒜_compat:
  fixes A :: "'a set"
  shows "∀ g ∈ carrier reversal⇩𝒢. ∀ E E'.
      (E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A) ⟶
        (φ_reverse (elections_𝒜 A) g E, φ_reverse (elections_𝒜 A) g E')
          ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
proof (intro ballI allI impI)
  fix
    g :: "'a rel ⇒ 'a rel" and
    E E' :: "('a, 'v) Election"
  assume
    g_in: "g ∈ carrier reversal⇩𝒢" and
    rel: "(E, E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  have E_in: "E ∈ elections_𝒜 A" and E'_in: "E' ∈ elections_𝒜 A"
    using rel
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast+
  have "(rel_app g E, rel_app g E') ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
    by (rule profile_map_compat[OF reversal_carrier_invol_pointwise[OF g_in]
          reversal_carrier_invol_pointwise[OF g_in] rel_app_voters rel_app_profile
          reversal_preserves_elections_𝒜[OF g_in] rel])
  thus "(φ_reverse (elections_𝒜 A) g E, φ_reverse (elections_𝒜 A) g E')
          ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
    unfolding φ_reverse_apply[OF E_in] φ_reverse_apply[OF E'_in] .
qed

text ‹
  Invertibility: reversal undoes itself, so every carrier element is its
  own inverse on the elections over A.
›

lemma φ_reverse_elections_𝒜_invertible:
  fixes A :: "'a set"
  shows "∀ g ∈ carrier reversal⇩𝒢. ∃ h ∈ carrier reversal⇩𝒢.
      ∀ E ∈ elections_𝒜 A.
        φ_reverse (elections_𝒜 A) h (φ_reverse (elections_𝒜 A) g E) = E
      ∧ φ_reverse (elections_𝒜 A) g (φ_reverse (elections_𝒜 A) h E) = E"
proof (intro ballI)
  fix g :: "'a rel ⇒ 'a rel"
  assume g_in: "g ∈ carrier reversal⇩𝒢"
  have "∀ E ∈ elections_𝒜 A.
      φ_reverse (elections_𝒜 A) g (φ_reverse (elections_𝒜 A) g E) = E"
  proof (intro ballI)
    fix E :: "('a, 'v) Election"
    assume E_in: "E ∈ elections_𝒜 A"
    have img: "rel_app g E ∈ elections_𝒜 A"
      by (rule reversal_preserves_elections_𝒜[OF g_in E_in])
    have "φ_reverse (elections_𝒜 A) g (φ_reverse (elections_𝒜 A) g E)
        = rel_app g (rel_app g E)"
      by (simp only: φ_reverse_apply[OF E_in] φ_reverse_apply[OF img])
    also have "… = rel_app (g ∘ g) E"
      by (rule rel_app_comp)
    also have "… = rel_app id E"
      by (simp only: reversal_carrier_invol[OF g_in])
    also have "… = E"
      by (rule rel_app_id)
    finally show
      "φ_reverse (elections_𝒜 A) g (φ_reverse (elections_𝒜 A) g E) = E" .
  qed
  thus "∃ h ∈ carrier reversal⇩𝒢. ∀ E ∈ elections_𝒜 A.
      φ_reverse (elections_𝒜 A) h (φ_reverse (elections_𝒜 A) g E) = E
    ∧ φ_reverse (elections_𝒜 A) g (φ_reverse (elections_𝒜 A) h E) = E"
    using g_in
    by blast
qed

text ‹
  Transfer: a rule with reversal symmetry on all well-formed elections is
  in particular reversal-equivariant on the elections over A, with the
  action parameterized by \<open>elections_𝒜 A\<close>. Unlike neutrality, no
  restriction of the transformation set is needed, since reversal never
  moves the alternative set.
›

lemma reversal_symmetry_in_elections_𝒜:
  fixes
    m :: "('a, 'v, 'a rel Result) Electoral_Module" and
    A :: "'a set"
  assumes "reversal_symmetry_in well_formed_elections m"
  shows "is_symmetry (fun⇩ℰ m)
      (action_induced_equivariance (carrier reversal⇩𝒢) (elections_𝒜 A)
          (φ_reverse (elections_𝒜 A)) (result_action ψ_reverse))"
proof -
  have sub_dom: "elections_𝒜 A ⊆ well_formed_elections"
    unfolding elections_𝒜.simps
    by blast
  from assms have
    "is_symmetry (fun⇩ℰ m) (Equivariance well_formed_elections
        {(φ_reverse well_formed_elections z, result_action ψ_reverse z) | z.
            z ∈ carrier reversal⇩𝒢})"
    unfolding reversal_symmetry_in_def action_induced_equivariance_def
    by simp
  hence "is_symmetry (fun⇩ℰ m) (Equivariance (elections_𝒜 A)
      {(φ_reverse well_formed_elections z, result_action ψ_reverse z) | z.
          z ∈ carrier reversal⇩𝒢})"
    using equivar_under_subset sub_dom
    by blast
  hence wfe_act: "is_symmetry (fun⇩ℰ m)
      (action_induced_equivariance (carrier reversal⇩𝒢) (elections_𝒜 A)
          (φ_reverse well_formed_elections) (result_action ψ_reverse))"
    unfolding action_induced_equivariance_def
    by simp
  moreover have "∀ g ∈ carrier reversal⇩𝒢. ∀ E ∈ elections_𝒜 A.
      φ_reverse well_formed_elections g E = φ_reverse (elections_𝒜 A) g E"
    using sub_dom
    by auto
  ultimately show ?thesis
    using equivar_ind_by_act_coincide
    by blast
qed

subsection ‹Anonymity Acts Trivially on the Quotient›

text ‹
  Renaming voters with a bijection changes who casts which ballot, but not
  how many voters cast each ballot: counting is blind to voter names.
  So a renamed election has exactly the same vote fractions as the
  original and therefore lands in the same anon-hom class. Consequently,
  voter renaming does not move the classes at all: it acts as the
  identity on the quotient. Anonymity does not survive as a symmetry of
  the quotient; it is built into the quotient itself.
›

lemma anon_preserves_elections_𝒜:
  fixes
    A :: "'a set" and
    π :: "'v ⇒ 'v" and
    E :: "('a, 'v) Election"
  assumes
    bij_π: "bij π" and
    elect: "E ∈ elections_𝒜 A"
  shows "rename π E ∈ elections_𝒜 A"
proof -
  obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
    E_eq: "E = (B, V, p)"
    using prod_cases3
    by blast
  have B_eq_A: "B = A" and
       fin_V: "finite V" and
       def_prof: "∀ v. v ∉ V ⟶ p v = {}" and
       wf: "(B, V, p) ∈ well_formed_elections"
    using elect E_eq
    unfolding elections_𝒜.simps
    by auto
  have prof: "profile V B p"
    using wf
    unfolding well_formed_elections_def
    by simp
  have ren_eq: "(B, π ` V, p ∘ the_inv π) = rename π (B, V, p)"
    by simp
  have "profile (π ` V) B (p ∘ the_inv π)"
    using rename_prof[OF prof ren_eq bij_π] .
  hence wf': "(B, π ` V, p ∘ the_inv π) ∈ well_formed_elections"
    unfolding well_formed_elections_def
    by simp
  have fin': "finite (π ` V)"
    using fin_V
    by blast
  have def': "∀ v'. v' ∉ π ` V ⟶ (p ∘ the_inv π) v' = {}"
  proof (intro allI impI)
    fix v' :: "'v"
    assume nin: "v' ∉ π ` V"
    have "the_inv π v' ∉ V"
    proof
      assume "the_inv π v' ∈ V"
      hence "π (the_inv π v') ∈ π ` V"
        by blast
      moreover have "π (the_inv π v') = v'"
        using bij_π f_the_inv_into_f_bij_betw
        by fastforce
      ultimately show "False"
        using nin
        by simp
    qed
    thus "(p ∘ the_inv π) v' = {}"
      using def_prof
      by simp
  qed
  have ren_E: "rename π E = (B, π ` V, p ∘ the_inv π)"
    unfolding E_eq
    by simp
  show ?thesis
    unfolding ren_E elections_𝒜.simps
    using wf' B_eq_A fin' def'
    by auto
qed

lemma φ_anon_apply:
  fixes
    𝒳 :: "('a, 'v) Election set" and
    π :: "'v ⇒ 'v" and
    E :: "('a, 'v) Election"
  assumes "E ∈ 𝒳"
  shows "φ_anon 𝒳 π E = rename π E"
  by (simp only: φ_anon.simps extensional_continuation.simps if_P[OF assms])

lemma vote_count_rename:
  fixes
    π :: "'v ⇒ 'v" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes
    bij_π: "bij π" and
    fin: "finite (voters_ℰ E)"
  shows "vote_count q (rename π E) = vote_count q E"
proof -
  have "(E, rename π E) ∈ anonymity⇩ℛ UNIV"
    unfolding anonymity⇩ℛ.simps action_induced_rel.simps φ_anon.simps
              simp_extensional_univ bijection⇩𝒱⇩𝒢_def
    using bij_π case_prodI rewrite_carrier
    by auto
  hence "∀ p. vote_count p E = vote_count p (rename π E)"
    using anon_rel_vote_count[OF fin]
    by blast
  thus ?thesis
    by metis
qed

lemma vote_fraction_rename:
  fixes
    π :: "'v ⇒ 'v" and
    q :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_π: "bij π"
  shows "vote_fraction q (rename π E) = vote_fraction q E"
proof -
  have inj_V: "inj_on π (voters_ℰ E)"
    by (rule inj_on_subset[OF bij_is_inj[OF bij_π] subset_UNIV])
  have vtrs: "voters_ℰ (rename π E) = π ` voters_ℰ E"
    by (cases E) simp
  have fin_eq: "finite (voters_ℰ (rename π E)) = finite (voters_ℰ E)"
    unfolding vtrs
    by (rule finite_image_iff[OF inj_V])
  have emp_eq: "(voters_ℰ (rename π E) = {}) = (voters_ℰ E = {})"
    unfolding vtrs
    by (rule image_is_empty)
  have card_eq: "card (voters_ℰ (rename π E)) = card (voters_ℰ E)"
    unfolding vtrs
    by (rule card_image[OF inj_V])
  show ?thesis
  proof (cases "finite (voters_ℰ E)")
    case True
    thus ?thesis
      by (simp only: vote_fraction.simps fin_eq emp_eq card_eq vote_count_rename[OF bij_π True])
  next
    case False
    thus ?thesis
      using fin_eq
      by simp
  qed
qed

text ‹
  The key step: an election and its voter-renamed version have the same
  fractions and both lie over A, so they are in the same anon-hom class.
›

lemma anon_rename_in_own_class:
  fixes
    A :: "'a set" and
    π :: "'v ⇒ 'v" and
    E :: "('a, 'v) Election"
  assumes
    bij_π: "bij π" and
    E_in: "E ∈ elections_𝒜 A"
  shows "(E, rename π E) ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
proof -
  have img: "rename π E ∈ elections_𝒜 A"
    by (rule anon_preserves_elections_𝒜[OF bij_π E_in])
  have fracs: "∀ q. vote_fraction q E = vote_fraction q (rename π E)"
    using vote_fraction_rename[OF bij_π]
    by metis
  have inj_V: "inj_on π (voters_ℰ E)"
    using bij_π bij_is_inj subset_UNIV inj_on_subset
    by metis
  have "voters_ℰ (rename π E) = π ` voters_ℰ E"
    by (cases E) simp
  hence "finite (voters_ℰ E) = finite (voters_ℰ (rename π E))"
    using finite_image_iff[OF inj_V]
    by simp
  thus ?thesis
    using E_in img fracs
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast
qed

text ‹
  Voter renaming maps every anon-hom class to itself: each renamed member
  stays in the class, and each member w of the class is hit, namely as
  the renaming of its own inverse-renaming, which also lies in the class.
›

lemma anon_acts_trivially_on_quotient:
  fixes
    A :: "'a set" and
    π :: "'v ⇒ 'v" and
    CLS :: "('a, 'v) Election set"
  assumes
    bij_π: "bij π" and
    cls: "CLS ∈ elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  shows "φ_anon (elections_𝒜 A) π ` CLS = CLS"
proof -
  let ?X = "elections_𝒜 A"
  let ?r = "anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  have equiv_r: "equiv ?X ?r"
    by (rule anon_hom_equiv)
  have trans_r: "Relation.trans ?r"
    using equiv_r
    unfolding equiv_def
    by blast
  obtain x :: "('a, 'v) Election" where
    CLS_eq: "CLS = ?r `` {x}" and
    x_in: "x ∈ ?X"
    using cls quotientE
    by blast
  have sub_X: "CLS ⊆ ?X"
    using CLS_eq equiv_type[OF equiv_r]
    by blast
  show ?thesis
  proof (intro equalityI subsetI)
    fix w :: "('a, 'v) Election"
    assume "w ∈ φ_anon ?X π ` CLS"
    then obtain E :: "('a, 'v) Election" where
      E_in_CLS: "E ∈ CLS" and
      w_eq: "w = φ_anon ?X π E"
      by blast
    have E_in_X: "E ∈ ?X"
      using E_in_CLS sub_X
      by blast
    have w_ren: "w = rename π E"
      unfolding w_eq
      by (rule φ_anon_apply[OF E_in_X])
    have "(x, E) ∈ ?r"
      using E_in_CLS CLS_eq
      by blast
    moreover have "(E, w) ∈ ?r"
      unfolding w_ren
      by (rule anon_rename_in_own_class[OF bij_π E_in_X])
    ultimately have "(x, w) ∈ ?r"
       by (rule transD[OF trans_r])
    thus "w ∈ CLS"
      unfolding CLS_eq
      by (simp only: Image_singleton_iff)
  next
    fix w :: "('a, 'v) Election"
    assume w_CLS: "w ∈ CLS"
    have x_w: "(x, w) ∈ ?r"
      using w_CLS CLS_eq
      by blast
    have w_X: "w ∈ ?X"
      using w_CLS sub_X
      by blast
    have bij_σ: "bij (the_inv π)"
      using bij_π bij_betw_the_inv_into
      by blast
    have u_X: "rename (the_inv π) w ∈ ?X"
      by (rule anon_preserves_elections_𝒜[OF bij_σ w_X])
    have "(w, rename (the_inv π) w) ∈ ?r"
      by (rule anon_rename_in_own_class[OF bij_σ w_X])
    hence "(x, rename (the_inv π) w) ∈ ?r"
      by (rule transD[OF trans_r x_w])
    hence u_CLS: "rename (the_inv π) w ∈ CLS"
      unfolding CLS_eq
      by blast
    obtain B :: "'a set" and V :: "'v set" and p :: "('a, 'v) Profile" where
      w_eq: "w = (B, V, p)"
      using prod_cases3
      by blast
    have "rename π (rename (the_inv π) w) = w"
      unfolding w_eq
      by (rule rename_inv[OF bij_π])
    moreover have "φ_anon ?X π (rename (the_inv π) w)
        = rename π (rename (the_inv π) w)"
      by (rule φ_anon_apply[OF u_X])
    ultimately have "w = φ_anon ?X π (rename (the_inv π) w)"
      by simp
    thus "w ∈ φ_anon ?X π ` CLS"
      by (rule image_eqI[OF _ u_CLS])
  qed
qed


end