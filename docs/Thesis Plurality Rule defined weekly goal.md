# Thesis Plurality Rule defined weekly goal  
  
  

| # | File | Artifact you produce | What it proves  |  | Build on / how | Effort & risk |
| --- | --------------------------------- | -------------------------------------------------- | --------------------------------------------------------------------------------------- | - | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------ |
| 0a | — | 3 new files + ROOT edits | Workspace exists and compiles |  | Add Quotient_Swap_Rationalization, Quotient_Kemeny_Rule, Quotient_Plurality_Rule to theories/ROOT after Kemeny_Rule | Trivial |
| P0 | Quotient_Swap_Rationalization.thy | anon_hom_equiv | Your way of grouping elections is a valid equivalence |  | Point at anonymity_homogeneity_is_equivalence (Election_Quotients.thy); finiteness is free from elections_\\<A> | Easy |
| P3 | same | limit_invar_anon_hom | The set of possible winners is the same across a group |  | Alternatives are constant on each group (all elections use UNIV) | Easy |
| S8 | same | strong_unanimity_subset | The "everyone agrees" elections lie inside your election pool |  | Unfold strong_unanimity_def, elections_\\<K>, well_formed_elections | Easy |
| P2 | same | strong_unanimity_closed_under_anon_hom | Swapping an "everyone agrees" election for an equivalent one keeps it "everyone agrees" |  | Copy the structure of strong_unanimity_closed_under_neutrality (Consensus_Class.thy, line 644) | Medium — [NEW] |
| P4 | same | strong_unanimity_invar_anon_hom | The "everyone agrees" rule gives the same answer for equivalent elections |  | Combine strong_unanimity_anonymous (line 432) + strong_unanimity_neutral' (line 617) | Medium — [NEW], risk U2 (anonymity+homogeneity → one relation) |
| P5a | same | (part of swap_dr_invar_anon_hom) | Reordering voters doesn't change the rule's answer |  | Reuse the anonymity chain from kemeny_rule_anonymous: distance_anonymity', symmetric_norm_imp_distance_anonymous (Votewise_Distance.thy, line 304), l_one_is_sym | Medium — [NEW] |
| P5b | same | swap_dist_homogeneous, then swap_dr_invar_anon_hom | Duplicating the whole electorate doesn't change the rule's answer |  | Prove swap distance ignores duplication, then feed distance_homogeneity_imp_distance_\\<R>_homogeneity (Distance_Rationalization_Symmetry.thy, line 709) | Medium–Hard — [NEW], risk U3 (homogeneity lemma may not exist yet) |
| P1 | same | swap_dist_simple | For each group, one representative election gives the same distances as the whole group |  | Prove by hand — the two shortcut lemmas (invar_dist_simple, tot_invar_dist_simple) do not apply. Follow Appelhagen thesis §A.7.5 | Hard — biggest task, risk U1 |
| K | Quotient_Kemeny_Rule.thy | kemeny_quotient_eq | Kemeny gives the same result on a group as on any single election in it |  | Unfold kemeny_rule = distance_\\<R> (votewise_distance swap l_one) strong_unanimity, apply the target theorem, feed P0–P5 + S8 + hypothesis | Easy once P0–P5 done |
| A0 | Quotient_Plurality_Rule.thy | plurality_dr (definition) | Defines Plurality as a distance-based rule |  | Use distance + consensus from Hadjibeyli–Wilson Example 2.17 | Blocked — risk U4 (values not in repo; get from paper) |
| A1 | same | plurality_dr_equiv | New Plurality definition matches the existing plurality_rule |  | Compare against existing Plurality_Rule.thy | Medium — depends on A0 |
| A2 | same | Plurality versions of P1, P2, P5 | Same facts as above, but for Plurality's distance and consensus |  | If A0 = swap + strong_unanimity → reuse P1/P2/P5. If different → redo them (includes Plurality's own Simplicity proof) | Easy or Hard — depends entirely on U4 |
| A3 | same | plurality_quotient_eq | Plurality gives the same result on a group as on any single election in it |  | Same assembly as K | Easy once A2 done |
| V | — | Clean build | No errors, no sorry anywhere |  | isabelle build -D theories | Final check |
  
**Work order:** P0 → P3 → S8 → P2 → P4 → P5a → P5b → **P1** → K → (decide U4) → A0 → A1 → A2 → A3 → V.  
  
**Four things most likely to cost extra time:** U1 = the Simplicity proof (P1); U2 = combining anonymity + homogeneity (P4); U3 = the duplication lemma (P5b); U4 = finding Plurality's distance and consensus from the paper (A0). Each can eat a day.  
