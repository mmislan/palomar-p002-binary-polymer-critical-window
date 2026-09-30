module

public import proofs.HordijkSteelThreshold.TargetTrials
public import proofs.HordijkSteelThreshold.StaticSeedProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- Fix the base field before sampling the independent sprinkling. Each
separated generated word supplies one bounded-cost target trial. -/
theorem finite_sprinkling_target_failure {N : ℕ} {J : Type*} [Fintype J]
    (base : Finset (Reaction N)) (words : J → List Bool) (v : List Bool)
    (hv : 0 < v.length)
    (hw : ∀ j, 0 < (words j).length)
    (hcap : ∀ j, (words j).length + v.length ≤ N)
    (hsep : ∀ i j, i ≠ j →
      (words i).length + v.length ≤ (words j).length ∨
      (words j).length + v.length ≤ (words i).length)
    (hbase : ∀ j, ∃ x ∈ temporaryReactionClosure 2 base, moleculeWord x = words j)
    (a : I) :
    staticReactionMeasure N a {ω | ¬ ∃ y ∈ temporaryReactionClosure 2
      (base ∪ staticOpenReactions ω), moleculeWord y = v} ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^Fintype.card J := by
  choose support hsize hband hgen using
    (fun j => target_trial_support (words j) v (hw j) hv (hcap j))
  have hdis : ∀ i ∈ (Finset.univ : Finset J), ∀ j ∈ (Finset.univ : Finset J),
      i ≠ j → Disjoint (support i) (support j) := by
    intro i _ j _ hij
    rcases hsep i j hij with h | h
    · exact target_trial_bands_disjoint (support i) (support j) h
        (fun r hr => (hband i r hr).2) (fun r hr => (hband j r hr).1)
    · exact (target_trial_bands_disjoint (support j) (support i) h
        (fun r hr => (hband j r hr).2) (fun r hr => (hband i r hr).1)).symm
  have hsub : {ω | ¬ ∃ y ∈ temporaryReactionClosure 2
      (base ∪ staticOpenReactions ω), moleculeWord y = v} ⊆
      {ω | ∀ j ∈ (Finset.univ : Finset J),
        detourFailed (fun r ω => ω r) (support j) ω} := by
    intro ω hω j _ hopen
    obtain ⟨x, hx, hword⟩ := hbase j
    apply hω
    apply hgen j (base ∪ staticOpenReactions ω)
    · intro r hr
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen r hr⟩)
    · exact temporaryReactionClosure_mono Finset.subset_union_left hx
    · exact hword
  calc
    _ ≤ staticReactionMeasure N a {ω | ∀ j ∈ (Finset.univ : Finset J),
        detourFailed (fun r ω => ω r) (support j) ω} := measure_mono hsub
    _ = ∏ j : J, (1-(toNNReal a : ENNReal)^(support j).card) :=
      measure_disjoint_detours_failed (staticReactionMeasure N a) (fun r ω => ω r)
        (staticReactionMeasure_indep N a) (fun r => measurable_pi_apply r)
        (toNNReal a : ENNReal) (staticReactionMeasure_open a) support Finset.univ hdis
    _ ≤ ∏ _j : J, (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      apply Finset.prod_le_prod
      intro j _
      apply tsub_le_tsub_left
      apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
      · exact_mod_cast a.property.2
      · exact hsize j
    _ = _ := by simp

end HordijkSteelThreshold
