module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval

def sprinklingParameter (a b : I) : I := σ ((σ a) * (σ b))

theorem sprinklingParameter_value (a b : I) :
    (sprinklingParameter a b : ℝ) = (a : ℝ) + (1-(a : ℝ))*(b : ℝ) := by
  change 1-((1-(a : ℝ))*(1-(b : ℝ))) = _
  ring

/-- Exact law of the union of two independent Bernoulli coordinates. -/
theorem ambientCoordLaw_union (a b : I) :
    ((ambientCoordLaw a).prod (ambientCoordLaw b)).map (fun p : Prop × Prop => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
  let μ := ((ambientCoordLaw a).prod (ambientCoordLaw b)).map
    (fun p : Prop × Prop => p.1 ∨ p.2)
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (((ambientCoordLaw a).prod (ambientCoordLaw b)).map
      (fun p : Prop × Prop => p.1 ∨ p.2))
    infer_instance
  have hf : μ {False} = ambientCoordLaw (sprinklingParameter a b) {False} := by
    rw [show μ = _ from rfl, Measure.map_apply (measurable_of_finite _)
      (MeasurableSet.singleton False)]
    have he : (fun p : Prop × Prop => p.1 ∨ p.2) ⁻¹' {False} =
        ({False} : Set Prop) ×ˢ {False} := by ext p; simp [Prod.ext_iff]
    rw [he, Measure.prod_prod]
    simp [ambientCoordLaw, sprinklingParameter, ← ENNReal.coe_mul]
    rfl
  have ht : μ {True} = ambientCoordLaw (sprinklingParameter a b) {True} := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext p; simp
    rw [he, measure_compl (MeasurableSet.singleton False) (measure_ne_top _ _),
      measure_compl (MeasurableSet.singleton False) (measure_ne_top _ _), hf]
    simp
  apply Measure.ext_of_singleton
  intro P
  by_cases h : P
  · simpa only [show P = True from propext (iff_true_intro h)] using ht
  · simpa only [show P = False from propext (iff_false_intro h)] using hf

end HordijkSteelThreshold
