module

public import proofs.HordijkSteelThreshold.SourceSurvivalLower

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem source_probability_eventually_above {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) < 1-Real.exp (-lambda))
    (c : ENNReal) (hc : c < staticSurvival a) :
    ∀ᶠ n in atTop, c < uniformCatalysisMeasure n lambda (HasRAFEvent n) := by
  let q : I := ⟨((a : ℝ)+(1-Real.exp (-lambda)))/2, by
    have ha0 := a.property.1
    have hp := Real.exp_pos (-lambda)
    constructor <;> linarith⟩
  have haq : (a : ℝ) < q := by dsimp [q]; linarith
  have hq : (q : ℝ) < 1-Real.exp (-lambda) := by dsimp [q]; linarith
  obtain ⟨b, hbe⟩ := exists_sprinkling_increment (show a ≤ q from haq.le)
  have hb : 0 < (b : ℝ) := by
    by_contra h
    have hz : (b : ℝ) = 0 := le_antisymm (le_of_not_gt h) b.property.1
    have hv := sprinklingParameter_value a b
    rw [hbe, hz, mul_zero, add_zero] at hv
    linarith
  obtain ⟨d, hcd, hds⟩ := exists_between hc
  have hsmall : Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero :
      Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 (c+0)))
  obtain ⟨m, hqm, hem, hm⟩ := ((nearFullPool_limit_tendsto lambda).eventually_const_lt hq |>.and
    ((hsmall.eventually_lt_const hcd).and (eventually_ge_atTop 2))).exists
  have hparam : (sprinklingParameter a b : ℝ) <
      1-Real.exp (-(lambda*(1-1/(m : ℝ)))) := by simpa [hbe] using hqm
  filter_upwards [source_survival_lower_error hlambda a b hb m hm hparam d hds] with n hn
  exact lt_of_add_lt_add_right (hem.trans_le hn)

noncomputable def staticSurvivalLeft (t : ℝ) : ENNReal :=
  ⨆ a : I, ⨆ (_h : (a : ℝ) < t), staticSurvival a

theorem transition_liminf_lower {lambda : ℝ} (hlambda : 0 < lambda) :
    staticSurvivalLeft (1-Real.exp (-lambda)) ≤
      liminf (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  apply (le_liminf_iff').mpr
  intro c hc
  exact (source_probability_eventually_above hlambda a ha c hc).mono (fun _ h => h.le)

end HordijkSteelThreshold
