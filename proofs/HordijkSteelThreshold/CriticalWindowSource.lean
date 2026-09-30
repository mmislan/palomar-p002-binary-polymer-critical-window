module

public import proofs.HordijkSteelThreshold.VariableIntensityTransition

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter RAF.Concrete
open scoped Topology

/-- The totalized model uses the literal f_n / |R_n| Bernoulli probability
eventually throughout the positive critical window. -/
theorem critical_window_parameter_exact {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, (catalysisP n (f n/(n : ℝ)) : ℝ) =
      f n/Fintype.card (RAF.Polymer.Reaction n) := by
  filter_upwards [hf.eventually_const_lt hlambda,
    hf.eventually_lt_const (show lambda < 2*lambda by linarith),
    catalysisP_eq_raw_eventually (show 0 < 2*lambda by linarith),eventually_ge_atTop 1]
      with n hn0 hnu hraw hn
  have hp0 : 0 ≤ rawCatalysisP n (f n/(n : ℝ)) := by
    unfold rawCatalysisP
    positivity
  have hpu : rawCatalysisP n (f n/(n : ℝ)) ≤ rawCatalysisP n (2*lambda) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnu.le (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hp1 : rawCatalysisP n (f n/(n : ℝ)) ≤ 1 := by
    rw [← hraw] at hpu
    exact hpu.trans (catalysisP n (2*lambda)).property.2
  change min 1 (max 0 (rawCatalysisP n (f n/(n : ℝ)))) = _
  rw [max_eq_right hp0,min_eq_right hp1]
  exact rawCatalysisP_ratio n (by omega) (f n)

/-- Source-complete corrected transition law for the locked food-two,
split-position reversible binary-polymer model. -/
theorem full_corrected_transition {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    (∀ᶠ n in atTop, (catalysisP n (f n/(n : ℝ)) : ℝ) =
      f n/Fintype.card (RAF.Polymer.Reaction n)) ∧
    Tendsto (fun n => rafProbability n (f n/(n : ℝ))) atTop
      (𝓝 (transitionLimit lambda hlambda)) ∧
    0 < transitionLimit lambda hlambda ∧
    transitionLimit lambda hlambda ≤ 1-Real.exp (-36*lambda) ∧
    transitionLimit lambda hlambda < 1 := by
  exact ⟨critical_window_parameter_exact hlambda hf,critical_window_transition hlambda hf⟩

end HordijkSteelThreshold
