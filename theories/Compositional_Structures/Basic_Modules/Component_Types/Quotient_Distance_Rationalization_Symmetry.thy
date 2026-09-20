(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotient_Distance_Rationalization_Symmetry.thy
*)

section ‹Symmetry Properties of Quotient Distance-Rationalized Rules›

theory Quotient_Distance_Rationalization_Symmetry
  imports  Quotient_Distance_Rationalization
  "Quotients/Quotient_Voting_Symmetry"
begin

text ‹
  This theory lifts symmetry properties of distance-rationalized rules to
  their quotient counterparts, generically in the property: any symmetry of
  the base rule that is expressed as an equivariance under a family of
  transformations (T, φ, ψ) and that is compatible with the quotient
  relation descends to the natively-constructed quotient rule
  \<open>distance_ℛ⇩𝒬\<close>. Invariance properties are the special case
  ψ g = id. Concrete properties (neutrality under the alternative-set
  stabilizer, reversal symmetry, ...) are obtained downstream by assuming equivariance, 
  compatibility, and invertibility for the respective action.
›

subsection ‹Auxiliary Lemma›

text ‹
  Invariance of the winner set and of the result limit under a relation
  yields invariance of the full DR rule, since the
  latter is assembled componentwise from the two. This makes winner-level
  invariance facts usable where full-rule invariance is required.
›

lemma (in result) distance_ℛ_invar_of_winners_invar:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel"
  assumes
    invar_winners: "is_symmetry (fun⇩ℰ (ℛ⇩𝒲 d C)) (Invariance r)" and
    invar_res: "is_symmetry (λ E :: ('a, 'v) Election.
        limit (alternatives_ℰ E) UNIV) (Invariance r)"
  shows "is_symmetry (fun⇩ℰ (distance_ℛ d C)) (Invariance r)"
proof -
  have win: "∀ E E'. (E, E') ∈ r ⟶ fun⇩ℰ (ℛ⇩𝒲 d C) E = fun⇩ℰ (ℛ⇩𝒲 d C) E'"
    using invar_winners
    unfolding is_symmetry.simps
    by blast (* alt: by fastforce *)
  have res: "∀ E E'. (E, E') ∈ r ⟶
      limit (alternatives_ℰ E) UNIV = limit (alternatives_ℰ E') UNIV"
    using invar_res
    unfolding is_symmetry.simps
    by blast (* alt: by fastforce *)
  have "∀ E E'. (E, E') ∈ r ⟶
      fun⇩ℰ (distance_ℛ d C) E = fun⇩ℰ (distance_ℛ d C) E'"
  proof (intro allI impI)
    fix E E' :: "('a, 'v) Election"
    assume rel: "(E, E') ∈ r"
    have "fun⇩ℰ (distance_ℛ d C) E =
        (fun⇩ℰ (ℛ⇩𝒲 d C) E,
          limit (alternatives_ℰ E) UNIV - fun⇩ℰ (ℛ⇩𝒲 d C) E, {})"
      by simp
    also have "… =
        (fun⇩ℰ (ℛ⇩𝒲 d C) E',
          limit (alternatives_ℰ E') UNIV - fun⇩ℰ (ℛ⇩𝒲 d C) E', {})"
      using win res rel
      by metis
    also have "… = fun⇩ℰ (distance_ℛ d C) E'"
      by simp
    finally show "fun⇩ℰ (distance_ℛ d C) E = fun⇩ℰ (distance_ℛ d C) E'" .
  qed
  thus ?thesis
    unfolding is_symmetry.simps
    by blast
qed

subsection ‹Theorem: Equivariance Lifts to the Quotient Rule›

text ‹
  Under the premises of \<open>invar_dr_simple_dist_imp_quotient_dr\<close>, any
  equivariance of the full distance-rationalized rule on X whose
  transformations respect the relation r and are invertible in the
  family descends to the quotient rule \<open>distance_ℛ⇩𝒬\<close> on X // r,
  under the elementwise action of the same transformations.
  The proof puts together 3 facts per transformation g and class B:
  the quotient-DR bridge identifies \<open>distance_ℛ⇩𝒬\<close> with the induced
  quotient function \<open>π⇩𝒬 (fun⇩ℰ (distance_ℛ d C))\<close>, both at B and at
  the transformed class φ g ` B (a class again by
  \<open>act_maps_classes_into_quotient\<close>), and the generic equivariance
  lifting \<open>pass_to_quotient_equivar'\<close> provides the equivariance of the
  induced quotient function in between.
›

theorem (in result) equivar_dr_simple_dist_imp_equivar_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    r :: "('a, 'v) Election rel" and
    X :: "('a, 'v) Election set" and
    T :: "'z set" and
    φ :: "('z, ('a, 'v) Election) binary_fun" and
    ψ :: "('z, 'r Result) binary_fun"
  assumes
    simple: "simple_on (elections_𝒦 C) r X d" and
    closed_domain: "closed_restricted_rel r X (elections_𝒦 C)" and
    invar_res: "is_symmetry (λ E :: ('a, 'v) Election.
        limit (alternatives_ℰ E) UNIV) (Invariance r)" and
    invar_C: "is_symmetry (elect_r ∘ fun⇩ℰ (rule_𝒦 C))
        (Invariance (Restr r (elections_𝒦 C)))" and
    invar_dr: "is_symmetry (fun⇩ℰ (ℛ⇩𝒲 d C)) (Invariance r)" and
    equiv_rel: "equiv X r" and
    cons_subset: "elections_𝒦 C ⊆ X" and
    equivar_dr: "is_symmetry (fun⇩ℰ (distance_ℛ d C))
        (action_induced_equivariance T X φ ψ)" and
    compat: "∀ g ∈ T. ∀ E E'. (E, E') ∈ r ⟶ (φ g E, φ g E') ∈ r" and
    invs: "∀ g ∈ T. ∃ h ∈ T. ∀ E ∈ X. φ h (φ g E) = E ∧ φ g (φ h E) = E"
  shows "is_symmetry (distance_ℛ⇩𝒬 r d C)
      (action_induced_equivariance T (X // r) (set_action φ) ψ)"
proof -
  have invar_full: "is_symmetry (fun⇩ℰ (distance_ℛ d C)) (Invariance r)"
    by (rule distance_ℛ_invar_of_winners_invar[OF invar_dr invar_res])
  have lifted: "is_symmetry (π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)))
      (action_induced_equivariance T (X // r) (set_action φ) ψ)"
    by (rule pass_to_quotient_equivar'[OF equiv_rel invar_full
          equivar_dr compat invs])
  have bridge: "∀ B ∈ X // r.
      π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) B = distance_ℛ⇩𝒬 r d C B"
  proof (intro ballI)
    fix B :: "('a, 'v) Election set"
    assume "B ∈ X // r"
    thus "π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) B = distance_ℛ⇩𝒬 r d C B"
      by (rule invar_dr_simple_dist_imp_quotient_dr[OF simple closed_domain
            invar_res invar_C invar_dr _ equiv_rel cons_subset])
  qed
  have "∀ g ∈ T. ∀ B ∈ X // r.
      distance_ℛ⇩𝒬 r d C (φ g ` B) = ψ g (distance_ℛ⇩𝒬 r d C B)"
  proof (intro ballI)
    fix
      g :: "'z" and
      B :: "('a, 'v) Election set"
    assume
      g_in_T: "g ∈ T" and
      cls_B: "B ∈ X // r"
    have img_cls: "φ g ` B ∈ X // r"
      by (rule act_maps_classes_into_quotient[OF equiv_rel compat invs
            g_in_T cls_B])
    have lifted_eq: "π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) (φ g ` B)
        = ψ g (π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) B)"
      using lifted g_in_T cls_B
      unfolding rewrite_equivariance set_action.simps
      by blast (* WIP *)
    have bridge_img: "π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) (φ g ` B)
        = distance_ℛ⇩𝒬 r d C (φ g ` B)"
      by (rule bspec[OF bridge img_cls])
    have bridge_B: "π⇩𝒬 (fun⇩ℰ (distance_ℛ d C)) B = distance_ℛ⇩𝒬 r d C B"
      by (rule bspec[OF bridge cls_B])
    show "distance_ℛ⇩𝒬 r d C (φ g ` B) = ψ g (distance_ℛ⇩𝒬 r d C B)"
      unfolding bridge_img[symmetric] bridge_B[symmetric]
      by (rule lifted_eq)
  qed
  thus ?thesis
    unfolding action_induced_equivariance_def is_symmetry.simps
              set_action.simps
    by blast
qed

(*  INSERT into: Quotient_Distance_Rationalization_Symmetry.thy

    EDIT 1 (header): change the imports line to

      imports Quotient_Distance_Rationalization
              "Quotients/Quotient_Voting_Symmetry"

    EDIT 2: paste everything below directly before the final `end`.

    NOTE (unverified): written without a running Isabelle; fallback
    methods are marked (* alt: ... *).
*)

subsection ‹Neutrality Lifts to the Quotient Rule›

text ‹
  [NEUTR_Q]: If the winner set of a distance-rationalized rule does not
  distinguish elections with the same vote fractions, and the rule is
  neutral on all well-formed elections, then the quotient rule over A is
  neutral in the quotient sense: renaming the alternatives within A moves
  each class to another class, and the winners of the moved class are the
  renamed winners of the original class. The proof only plugs the already
  proven stabilizer facts into the generic lifting theorem.
›

theorem (in result_properties) neutr_dr_imp_neutr_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'b Result) Consensus_Class" and
    A :: "'a set"
  assumes
    simple: "simple_on (elections_𝒦 C)
        (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) (elections_𝒜 A) d" and
    closed_domain: "closed_restricted_rel
        (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) (elections_𝒜 A)
        (elections_𝒦 C)" and
    invar_res: "is_symmetry (λ E :: ('a, 'v) Election.
        limit (alternatives_ℰ E) UNIV)
        (Invariance (anonymity_homogeneity⇩ℛ (elections_𝒜 A)))" and
    invar_C: "is_symmetry (elect_r ∘ fun⇩ℰ (rule_𝒦 C))
        (Invariance (Restr (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
            (elections_𝒦 C)))" and
    invar_dr: "is_symmetry (fun⇩ℰ (ℛ⇩𝒲 d C))
        (Invariance (anonymity_homogeneity⇩ℛ (elections_𝒜 A)))" and
    cons_subset: "elections_𝒦 C ⊆ elections_𝒜 A" and
    neutral: "neutrality_in well_formed_elections (distance_ℛ d C)"
  shows "is_symmetry (distance_ℛ⇩𝒬 (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) d C)
      (action_induced_equivariance (alt_stabilizer A)
          (elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A))
          (set_action (φ_neutral (elections_𝒜 A))) (result_action ψ))"
  by (rule equivar_dr_simple_dist_imp_equivar_quotient_dr[OF simple
        closed_domain invar_res invar_C invar_dr anon_hom_equiv cons_subset
        neutrality_in_stabilizer[OF neutral]
        φ_neutral_elections_𝒜_compat φ_neutral_elections_𝒜_invertible])

subsection ‹Reversal Symmetry Lifts to the Quotient Rule›

text ‹
  [REV_Q]: The same statement for reversal symmetry of SCFs. Here the full two-element reversal group acts, since flipping
  all ballots never moves the alternative set.
›

theorem rev_dr_imp_rev_quotient_dr:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'a rel Result) Consensus_Class" and
    A :: "'a set"
  assumes
    simple: "simple_on (elections_𝒦 C)
        (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) (elections_𝒜 A) d" and
    closed_domain: "closed_restricted_rel
        (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) (elections_𝒜 A)
        (elections_𝒦 C)" and
    invar_res: "is_symmetry (λ E :: ('a, 'v) Election.
        limit_𝒮𝒲ℱ (alternatives_ℰ E) UNIV)
        (Invariance (anonymity_homogeneity⇩ℛ (elections_𝒜 A)))" and
    invar_C: "is_symmetry (elect_r ∘ fun⇩ℰ (rule_𝒦 C))
        (Invariance (Restr (anonymity_homogeneity⇩ℛ (elections_𝒜 A))
            (elections_𝒦 C)))" and
    invar_dr: "is_symmetry (fun⇩ℰ (𝒮𝒲ℱ_result.ℛ⇩𝒲 d C))
        (Invariance (anonymity_homogeneity⇩ℛ (elections_𝒜 A)))" and
    cons_subset: "elections_𝒦 C ⊆ elections_𝒜 A" and
    rev_sym: "reversal_symmetry_in well_formed_elections
        (𝒮𝒲ℱ_result.distance_ℛ d C)"
  shows "is_symmetry
      (𝒮𝒲ℱ_result.distance_ℛ⇩𝒬 (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) d C)
      (action_induced_equivariance (carrier reversal⇩𝒢)
          (elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A))
          (set_action (φ_reverse (elections_𝒜 A))) (result_action ψ_reverse))"
  by (rule 𝒮𝒲ℱ_result.equivar_dr_simple_dist_imp_equivar_quotient_dr[OF simple
        closed_domain invar_res invar_C invar_dr anon_hom_equiv cons_subset
        reversal_symmetry_in_elections_𝒜[OF rev_sym]
        φ_reverse_elections_𝒜_compat φ_reverse_elections_𝒜_invertible])

subsection ‹Anonymity Holds Trivially on the Quotient Rule›

text ‹
  [ANON'_Q]: Renaming voters does not move any anon-hom class, so every
  quotient rule is unchanged under the induced voter-renaming action
  (with no extra assumptions). Anonymity
  and homogeneity are absorbed into the quotient. The symmetries that survive as genuine actions on the quotient are
  those that permute vote fractions, like neutrality and reversal. For properties like consistency this is less clear.
›

corollary (in result) quotient_dr_anonymous:
  fixes
    d :: "('a, 'v) Election Distance" and
    C :: "('a, 'v, 'r Result) Consensus_Class" and
    A :: "'a set" and
    π :: "'v ⇒ 'v" and
    CLS :: "('a, 'v) Election set"
  assumes
    bij_π: "bij π" and
    cls: "CLS ∈ elections_𝒜 A // anonymity_homogeneity⇩ℛ (elections_𝒜 A)"
  shows "distance_ℛ⇩𝒬 (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) d C
      (set_action (φ_anon (elections_𝒜 A)) π CLS)
    = distance_ℛ⇩𝒬 (anonymity_homogeneity⇩ℛ (elections_𝒜 A)) d C CLS"
  by (simp only: set_action.simps
        anon_acts_trivially_on_quotient[OF bij_π cls])


end
