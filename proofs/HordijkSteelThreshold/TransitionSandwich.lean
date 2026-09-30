module

public import proofs.HordijkSteelThreshold.TransitionLowerBound
public import proofs.HordijkSteelThreshold.TransitionUpperBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem transition_probability_sandwich {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda)) :
    staticSurvivalLeft (a : ℝ) ≤
      liminf (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop ∧
    limsup (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop ≤
      staticSurvival a := by
  exact ⟨by simpa only [ha] using transition_liminf_lower hlambda,
    transition_limsup_upper hlambda a ha⟩

/-- The remaining gap is explicit; no continuity assertion is assumed silently. -/
theorem transition_tendsto_of_no_gap {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda))
    (hgap : staticSurvival a ≤ staticSurvivalLeft (a : ℝ)) :
    Tendsto (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop
      (𝓝 (staticSurvival a)) := by
  obtain ⟨hl,hu⟩ := transition_probability_sandwich hlambda a ha
  exact tendsto_of_le_liminf_of_limsup_le (hgap.trans hl) hu

end HordijkSteelThreshold
