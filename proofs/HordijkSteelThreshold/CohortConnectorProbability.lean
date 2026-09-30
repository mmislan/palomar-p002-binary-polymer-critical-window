module

public import proofs.HordijkSteelThreshold.FamilyOpenProbability

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A fixed reaction family has no retained catalyst but has a catalyst in the
preceding deleted cohort. Pools here are deterministic, not conditionally sampled. -/
def cohortFamilyLost {n : Nat} (ω : AmbientCoord n → Prop)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) : Prop :=
  ¬ catalystPoolFamilyOpen ω K R ∧ catalystPoolFamilyOpen ω D R

theorem catalystPoolFamilyOpen_union {n : Nat} (ω : AmbientCoord n → Prop)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) :
    catalystPoolFamilyOpen ω (K ∪ D) R ↔
      catalystPoolFamilyOpen ω K R ∨ catalystPoolFamilyOpen ω D R := by
  simp only [catalystPoolFamilyOpen, catalystPoolOpen, Finset.mem_union]
  aesop

/-- Exact fixed-cohort cost, valid even for overlapping pools. The family event
requires one deleted-cohort witness somewhere in R, not one for every r in R. -/
theorem measure_cohortFamilyLost {n : Nat} (lambda : ℝ)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | cohortFamilyLost ω K D R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (K.card * R.card) -
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ ((K ∪ D).card * R.card) := by
  have he : {ω : AmbientCoord n → Prop | cohortFamilyLost ω K D R} =
      {ω | ¬ catalystPoolFamilyOpen ω K R} \
      {ω | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, cohortFamilyLost,
      catalystPoolFamilyOpen_union]
    tauto
  have hs : {ω : AmbientCoord n → Prop | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} ⊆
      {ω | ¬ catalystPoolFamilyOpen ω K R} := by
    intro ω h hk
    exact h ((catalystPoolFamilyOpen_union ω K D R).mpr (Or.inl hk))
  have hm : MeasurableSet
      {ω : AmbientCoord n → Prop | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} := by
    exact Set.Finite.measurableSet (Set.toFinite _)
  rw [he, measure_sdiff hs hm.nullMeasurableSet (measure_ne_top _ _),
    measure_catalystPoolFamilyClosed, measure_catalystPoolFamilyClosed]

/-- The singleton specialization is the chronological connector's exact cost. -/
theorem measure_cohortConnectorLost {n : Nat} (lambda : ℝ)
    (K D : Finset (Molecule n)) (r : Reaction n) (hKD : Disjoint K D) :
    ambientPiMeasure n lambda {ω | cohortFamilyLost ω K D {r}} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ K.card -
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (K.card + D.card) := by
  rw [measure_cohortFamilyLost, Finset.card_union_of_disjoint hKD]
  simp

end HordijkSteelThreshold
