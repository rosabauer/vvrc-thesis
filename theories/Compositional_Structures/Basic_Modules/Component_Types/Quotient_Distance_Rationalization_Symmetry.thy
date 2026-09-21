(*  File:  theories/Compositional_Structures/Basic_Modules/Component_Types/
           Quotient_Distance_Rationalization_Symmetry.thy
*)

section ‹Symmetry Properties of Quotient Distance-Rationalized Rules›

theory Quotient_Distance_Rationalization_Symmetry
  imports  Quotient_Distance_Rationalization
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
    by blast 
  have res: "∀ E E'. (E, E') ∈ r ⟶
      limit (alternatives_ℰ E) UNIV = limit (alternatives_ℰ E') UNIV"
    using invar_res
    unfolding is_symmetry.simps
    by blast 
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
      by blast 
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

end
