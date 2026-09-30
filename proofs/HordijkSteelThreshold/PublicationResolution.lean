module

public import proofs.HordijkSteelThreshold.OuterScalingRegimes

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped Topology

/-- Publication-facing law with the infinite survival event exposed literally. -/
theorem publication_resolution {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => rafProbability n (f n/(n : ℝ))) atTop
      (𝓝 ((infiniteStaticMeasure (transitionOpenness lambda hlambda)
        {field | ReversibleUnbounded 2 field}).toReal)) ∧
    0 < transitionLimit lambda hlambda ∧ transitionLimit lambda hlambda < 1 ∧
    Continuous (fun x : {x : ℝ // 0 < x} => transitionLimit x.val x.property) ∧
    (∀ x y : ℝ, ∀ hx : 0 < x, ∀ hy : 0 < y,
      x ≤ y → transitionLimit x hx ≤ transitionLimit y hy) := by
  exact ⟨variable_intensity_transition hlambda hf,
    (transitionLimit_mem_Ioo lambda hlambda).1,(transitionLimit_mem_Ioo lambda hlambda).2,
    continuous_transitionLimit,fun _ _ hx hy hxy => transitionLimit_mono hx hy hxy⟩

end HordijkSteelThreshold
