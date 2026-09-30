module

public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordMoleculeContourCount
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

theorem wordMoleculeContourEnvelope_member_card {L N b : ℕ} {s : List Bool}
    {C : Finset (WordBasicEdge L N)} (hC : C ∈ wordMoleculeContourEnvelope L N s b) :
    C.card = b := by
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hC
  exact (Finset.mem_filter.mp he).2.1

noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  (molecularContourConstant : ENNReal) * (1-(toNNReal a : ENNReal)^2)^k

theorem measure_molecule_contours_size_le {L N w k b : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (hb : 0 < b) (a : I) :
    staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s b,
      contourDetoursFailed hL C (fun r ω => ω r) ω} ≤ (contourBudget a k)^b := by
  classical
  let E := wordMoleculeContourEnvelope L N s b
  have hcount : (E.card : ENNReal) ≤ (molecularContourConstant : ENNReal)^b := by
    exact_mod_cast wordMoleculeContourEnvelope_card L N s b hb
  have he : {ω : Reaction N → Prop | ∃ C ∈ E,
      contourDetoursFailed hL C (fun r ω => ω r) ω} =
      ⋃ C ∈ E, {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} := by ext ω; simp
  change staticReactionMeasure N a {ω | ∃ C ∈ E,
    contourDetoursFailed hL C (fun r ω => ω r) ω} ≤ _
  rw [he]
  calc
    _ ≤ ∑ C ∈ E, staticReactionMeasure N a
      {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} := measure_biUnion_finset_le E _
    _ ≤ ∑ _C ∈ E, ((1-(toNNReal a : ENNReal)^2)^k)^b := by
      apply Finset.sum_le_sum
      intro C hC
      have hcard := wordMoleculeContourEnvelope_member_card hC
      simpa only [hcard] using staticReaction_contour_failure hL hk C a
    _ = (E.card : ENNReal) * ((1-(toNNReal a : ENNReal)^2)^k)^b := by simp
    _ ≤ (molecularContourConstant : ENNReal)^b * ((1-(toNNReal a : ENNReal)^2)^k)^b := by
      gcongr
    _ = (contourBudget a k)^b := by rw [contourBudget, mul_pow]

/-- A per-molecule envelope of all positive-size disabled contours. Its
probability bounds actual smaller-side membership by the compiled anchor theorem. -/
def moleculeContourBad {L N w : ℕ} (hL : 2*w ≤ L) (s : List Bool)
    (ω : Reaction N → Prop) : Prop :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
    contourDetoursFailed hL C (fun r ω => ω r) ω

theorem wordBond_smaller_side_bad {L N w : ℕ} (hL : 2*w ≤ L)
    (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) (ω : Reaction N → Prop)
    (hfailed : contourDetoursFailed hL (wordGraphCut f) (fun r ω => ω r) ω) :
    moleculeContourBad hL s ω := by
  have hb := Finset.card_pos.mpr hn
  have hcard : (wordGraphCut f).card-1+1 = (wordGraphCut f).card := by omega
  refine ⟨(wordGraphCut f).card-1, wordGraphCut f, ?_, hfailed⟩
  rw [hcard]
  exact wordBond_mem_molecule_envelope f hmin hn c hminor s hs

/-- Uniform bad-side marginal; no independence between contours is required. -/
theorem measure_moleculeContourBad_le {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (a : I) :
    staticReactionMeasure N a {ω | moleculeContourBad hL s ω} ≤
      contourBudget a k / (1-contourBudget a k) := by
  have he : {ω | moleculeContourBad hL s ω} =
      ⋃ j : ℕ, {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
        contourDetoursFailed hL C (fun r ω => ω r) ω} := by ext ω; simp [moleculeContourBad]
  rw [he]
  calc
    _ ≤ ∑' j : ℕ, staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
      contourDetoursFailed hL C (fun r ω => ω r) ω} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, (contourBudget a k)^(j+1) := ENNReal.tsum_le_tsum
      (fun j => measure_molecule_contours_size_le hL hk s (by omega) a)
    _ = _ := by rw [ENNReal.tsum_geometric_add_one, div_eq_mul_inv]

end HordijkSteelThreshold
