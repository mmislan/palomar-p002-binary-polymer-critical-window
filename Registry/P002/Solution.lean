module

public import proofs.HordijkSteelThreshold.PublicationResolution

@[expose] public section

namespace HordijkSteelThreshold
open RAF.Concrete Filter Topology

/-- A continuous monotone, strictly interior limiting law for every sequence
of mean catalysis intensities with a positive finite linear-scale limit. -/
theorem palomar_critical_window_variable_intensity :
    ∃ L : {lambda : ℝ // 0 < lambda} → ℝ,
      Continuous L ∧ Monotone L ∧
      ∀ lambda : {lambda : ℝ // 0 < lambda},
        0 < L lambda ∧ L lambda ≤ 1-Real.exp (-36*lambda.val) ∧ L lambda < 1 ∧
        ∀ f : ℕ → ℝ,
          Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda.val) →
          Tendsto (fun n => rafProbability n (f n/(n : ℝ))) atTop (𝓝 (L lambda)) := by
  refine ⟨fun x => transitionLimit x.val x.property, continuous_transitionLimit, ?_, ?_⟩
  · intro x y hxy
    exact transitionLimit_mono x.property y.property hxy
  · intro lambda
    have h := (corrected_transition lambda.val lambda.property).2
    refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    intro f hf
    exact variable_intensity_transition lambda.property hf

end HordijkSteelThreshold
