module

public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.HordijkSteelThreshold.StaticSeedMassBound
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem source_survival_lower_error {lambda : ℝ} (hlambda : 0 < lambda)
    (a b : I) (hb : 0 < (b : ℝ)) (m : ℕ) (hm : 2 ≤ m)
    (hq : (sprinklingParameter a b : ℝ) < 1-Real.exp (-(lambda*(1-1/(m : ℝ)))))
    (c : ENNReal) (hc : c < staticSurvival a) :
    ∀ᶠ n in atTop, c ≤ uniformCatalysisMeasure n lambda (HasRAFEvent n) + (m : ENNReal)⁻¹ := by
  have hp := (nearFullPoolParameter_tendsto hlambda m (by omega)).eventually_const_lt hq
  filter_upwards [hp, nearFullPoolSize_eventually_nonfood m hm,
    static_survival_bulk_eventually a b hb m (by omega) c hc] with n hparam hsize hstatic
  have hq' : sprinklingParameter a b ≤ fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) ((m-1)*(Fintype.card (Molecule n)/m))).card := hparam.le
  have hr := canonical_raf_ge_near_full_static n m lambda (by omega) (sprinklingParameter a b) hsize hq'
  exact hstatic.trans (add_le_add hr le_rfl)

theorem nearFullPool_limit_tendsto (lambda : ℝ) :
    Tendsto (fun m : ℕ => 1-Real.exp (-(lambda*(1-1/(m : ℝ))))) atTop
      (𝓝 (1-Real.exp (-lambda))) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hinner : Tendsto (fun m : ℕ => -(lambda * (1 - (m : ℝ)⁻¹))) atTop
      (𝓝 (-lambda)) := by
    simpa only [sub_zero, mul_one] using ((hconst.sub hi).const_mul lambda).neg
  have ht : Tendsto (fun m : ℕ =>
      1 - Real.exp (-(lambda * (1 - (m : ℝ)⁻¹)))) atTop
      (𝓝 (1 - Real.exp (-lambda))) :=
    hconst.sub (Real.continuous_exp.tendsto _ |>.comp hinner)
  simpa only [one_div] using ht

end HordijkSteelThreshold
