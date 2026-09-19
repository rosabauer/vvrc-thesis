(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotients/Quotient_Voting_Symmetry.thy

    NOTE: anon_hom_equiv_elections_𝒜 duplicates anon_hom_equiv from
    Quotient_Swapwise_Rules_Helpers.thy; WIP to refactor where this fact could 
    be best placed in the VMCF.
*)

section ‹Symmetry of Quotient Voting Rules›

theory Quotient_Voting_Symmetry
  imports Election_Quotients
          "../Social_Choice_Types/Property_Interpretations"
begin

subsection ‹The Alternative-Set Stabilizer›

text ‹
  In group theory, stabilizers are restrictions on a set 
  that state that an operation never maps the elements of a set, 
  in this case the election alternatives, outside of the set.
  They are  the neutrality symmetries
  that descend to the anon-hom quotient over A (and thus to the simplex).
›

definition alt_stabilizer :: "'a set ⇒ ('a ⇒ 'a) set" where
  "alt_stabilizer A = {π ∈ carrier bijection⇩𝒜⇩𝒢. π ` A = A}"

lemma alt_stabilizer_rewrite:
  fixes A :: "'a set"
  shows "alt_stabilizer A = {π. bij π ∧ π ` A = A}"
  unfolding alt_stabilizer_def bijection⇩𝒜⇩𝒢_def
  using rewrite_carrier
  by blast

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
      by fastforce (* alt: by (metis UNIV_I comp_apply id_apply) *)
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
    using assms alt_stabilizer_rewrite
    by blast+
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
    using stab alt_stabilizer_rewrite
    by blast+
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
  have "π ` B = A"
    using B_eq_A img_A
    by simp
  moreover have "∀ v. v ∉ V ⟶ (rel_rename π ∘ p) v = {}"
    using def_prof rel_rename_empty
    by simp
  ultimately show ?thesis
    using wf' fin_V ren_eq E_eq
    unfolding elections_𝒜.simps
    by (metis (mono_tags, lifting) IntI alternatives_ℰ.simps
          mem_Collect_eq profile_ℰ.simps voters_ℰ.simps)
    (* WIP---- : maybe unfold and finish with auto after rewriting with ren_eq[symmetric] *)
qed

subsection ‹Vote Counts and Fractions under Renaming›

text ‹
  Renaming the alternatives with a bijection π permutes the ballots:
  the voters casting ballot r after renaming are exactly the voters casting
  the preimage ballot before renaming. Voters are untouched, so vote counts
  and vote fractions transform accordingly.
›

lemma vote_count_alts_rename:
  fixes
    π :: "'a ⇒ 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_π: "bij π"
  shows "vote_count r (alts_rename π E) = vote_count (rel_rename (the_inv π) r) E"
proof -
  have rr_inv: "rel_rename (the_inv π) ∘ rel_rename π = id"
    using rel_rename_compositional[of "the_inv π" π]
          bij_the_inv_comp(1)[OF bij_π] rel_rename_id
    by metis
  have rr_inv': "rel_rename π ∘ rel_rename (the_inv π) = id"
    using rel_rename_compositional[of π "the_inv π"]
          bij_the_inv_comp(2)[OF bij_π] rel_rename_id
    by metis
  have set_eq: "{v ∈ voters_ℰ E. rel_rename π (profile_ℰ E v) = r}
      = {v ∈ voters_ℰ E. profile_ℰ E v = rel_rename (the_inv π) r}"
  proof (safe)
    fix v :: "'v"
    assume "r = rel_rename π (profile_ℰ E v)"
    thus "profile_ℰ E v = rel_rename (the_inv π) (rel_rename π (profile_ℰ E v))"
      using rr_inv
      by (metis comp_apply id_apply)
  next
    fix v :: "'v"
    assume "profile_ℰ E v = rel_rename (the_inv π) r"
    thus "rel_rename π (profile_ℰ E v) = r"
      using rr_inv'
      by (metis comp_apply id_apply)
  qed
  have "vote_count r (alts_rename π E)
      = card {v ∈ voters_ℰ E. rel_rename π (profile_ℰ E v) = r}"
    unfolding vote_count.simps alts_rename.simps
    by (simp add: comp_def)
  also have "… = card {v ∈ voters_ℰ E. profile_ℰ E v = rel_rename (the_inv π) r}"
    by (rule arg_cong[of _ _ card, OF set_eq])
  also have "… = vote_count (rel_rename (the_inv π) r) E"
    unfolding vote_count.simps
    by simp
  finally show ?thesis .
qed

lemma vote_fraction_alts_rename:
  fixes
    π :: "'a ⇒ 'a" and
    r :: "'a Preference_Relation" and
    E :: "('a, 'v) Election"
  assumes bij_π: "bij π"
  shows "vote_fraction r (alts_rename π E)
       = vote_fraction (rel_rename (the_inv π) r) E"
proof -
  have "voters_ℰ (alts_rename π E) = voters_ℰ E"
    by simp
  thus ?thesis
    using vote_count_alts_rename[OF bij_π]
    unfolding vote_fraction.simps
    by presburger (* alt: by simp *)
qed

subsection ‹Neutrality Action Descends to Anon-Hom Classes›

lemma anon_hom_equiv_elections_𝒜:
  fixes A :: "'a set"
  shows "equiv (elections_𝒜 A) (anonymity_homogeneity⇩ℛ (elections_𝒜 A))"
proof -
  have "∀ E ∈ elections_𝒜 A. finite (voters_ℰ E)"
    unfolding elections_𝒜.simps
    by blast
  thus ?thesis
    by (rule anonymity_homogeneity_is_equivalence)
qed

text ‹
  Compatibility: stabilizer renamings map anonhom-related
  elections to related elections, since they permute vote fractions over
  ballots and leave the alternatives untouched.
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
    using stab alt_stabilizer_rewrite
    by blast
  have E_in: "E ∈ elections_𝒜 A" and
       E'_in: "E' ∈ elections_𝒜 A" and
       fin_eq: "finite (voters_ℰ E) = finite (voters_ℰ E')" and
       frac_eq: "∀ q. vote_fraction q E = vote_fraction q E'"
    using rel
    unfolding anonymity_homogeneity⇩ℛ.simps
    by blast+
  have φ_E: "φ_neutral (elections_𝒜 A) π E = alts_rename π E"
    using E_in
    by simp
  have φ_E': "φ_neutral (elections_𝒜 A) π E' = alts_rename π E'"
    using E'_in
    by simp
  have img_E: "alts_rename π E ∈ elections_𝒜 A"
    using stabilizer_preserves_elections_𝒜 stab E_in
    by blast
  have img_E': "alts_rename π E' ∈ elections_𝒜 A"
    using stabilizer_preserves_elections_𝒜 stab E'_in
    by blast
  have "∀ q. vote_fraction q (alts_rename π E) = vote_fraction q (alts_rename π E')"
    using vote_fraction_alts_rename[OF bij_π] frac_eq
    by metis
  moreover have
    "finite (voters_ℰ (alts_rename π E)) = finite (voters_ℰ (alts_rename π E'))"
    using fin_eq
    by simp
  ultimately show
    "(φ_neutral (elections_𝒜 A) π E, φ_neutral (elections_𝒜 A) π E')
        ∈ anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
    using img_E img_E'
    unfolding φ_E φ_E' anonymity_homogeneity⇩ℛ.simps
    by blast
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
    using stab_π alt_stabilizer_rewrite
    by blast
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
    have fst_dir:
      "φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E)
        = alts_rename (the_inv π) (alts_rename π E)"
      using E_in img_π
      by simp
    have "alts_rename (the_inv π) (alts_rename π E)
        = alts_rename (the_inv π ∘ π) E"
      using alts_rename_compositional comp_apply
      by metis
    hence eq_1:
      "φ_neutral (elections_𝒜 A) (the_inv π) (φ_neutral (elections_𝒜 A) π E) = E"
      using fst_dir bij_the_inv_comp(1)[OF bij_π] alts_rename_id
      by metis
    have snd_dir:
      "φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E)
        = alts_rename π (alts_rename (the_inv π) E)"
      using E_in img_σ
      by simp
    have "alts_rename π (alts_rename (the_inv π) E)
        = alts_rename (π ∘ the_inv π) E"
      using alts_rename_compositional comp_apply
      by metis
    hence eq_2:
      "φ_neutral (elections_𝒜 A) π (φ_neutral (elections_𝒜 A) (the_inv π) E) = E"
      using snd_dir bij_the_inv_comp(2)[OF bij_π] alts_rename_id
      by metis
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
    by blast (* alt: by metis *)
qed

subsection ‹Theorem: Neutrality Lifts to the Quotient›

text ‹
  If an electoral module is invariant under the
  anon-hom relation on elections over A (so it induces a
  well-defined quotient rule via π⇩𝒬) and neutral on well-formed elections,
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
          anon_hom_equiv_elections_𝒜
          invar_m
          neutrality_in_stabilizer[OF neutral_m]
          φ_neutral_elections_𝒜_compat
          φ_neutral_elections_𝒜_invertible] .

end