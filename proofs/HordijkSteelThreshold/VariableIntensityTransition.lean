module

public import proofs.HordijkSteelThreshold.CorrectedTransition
public import proofs.HordijkSteelThreshold.StaticSurvivalContinuity
public import proofs.HordijkSteelThreshold.CanonicalParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped ENNReal Topology

noncomputable def intensityBelow (lambda : ℝ) (k : ℕ) : ℝ :=
  lambda*(lowerOpenness 1 k : ℝ)

theorem intensityBelow_bounds {lambda : ℝ} (hlambda : 0 < lambda) (k : ℕ) :
    0 < intensityBelow lambda k ∧ intensityBelow lambda k < lambda := by
  have hlo := half_le_lowerOpenness (1 : I) k
  have hhi := lowerOpenness_lt (1 : I) (by norm_num) k
  change (1 : ℝ)/2 ≤ (lowerOpenness 1 k : ℝ) at hlo
  change (lowerOpenness 1 k : ℝ) < 1 at hhi
  dsimp [intensityBelow]
  constructor
  · exact mul_pos hlambda (by linarith)
  · nlinarith

theorem intensityBelow_tendsto (lambda : ℝ) :
    Tendsto (intensityBelow lambda) atTop (𝓝 lambda) := by
  have h := continuous_subtype_val.continuousAt.tendsto.comp (lowerOpenness_tendsto (1 : I))
  change Tendsto (fun k => lambda*(lowerOpenness 1 k : ℝ)) atTop (𝓝 lambda)
  have hh := (tendsto_const_nhds.mul h :
    Tendsto (fun k => lambda*(lowerOpenness 1 k : ℝ)) atTop (𝓝 (lambda*(1 : I))))
  convert hh using 1
  norm_num

theorem transitionOpenness_tendsto {v : ℕ → ℝ} {lambda : ℝ}
    (hv : ∀ k, 0 < v k) (hlambda : 0 < lambda) (ht : Tendsto v atTop (𝓝 lambda)) :
    Tendsto (fun k => transitionOpenness (v k) (hv k)) atTop
      (𝓝 (transitionOpenness lambda hlambda)) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_const_nhds.sub (Real.continuous_exp.continuousAt.tendsto.comp ht.neg)

/-- The original critical-window quantifier: intensity may vary with n and
only needs to converge to a positive value. -/
theorem variable_intensity_canonical_tendsto {v : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hv : Tendsto v atTop (𝓝 lambda)) :
    Tendsto (fun n => uniformCatalysisMeasure n (v n) (HasRAFEvent n)) atTop
      (𝓝 (staticSurvival (transitionOpenness lambda hlambda))) := by
  let lo : ℕ → ℝ := intensityBelow lambda
  let hi : ℕ → ℝ := fun k => 2*lambda-lo k
  have hlo (k : ℕ) : 0 < lo k ∧ lo k < lambda := intensityBelow_bounds hlambda k
  have hhi (k : ℕ) : 0 < hi k ∧ lambda < hi k := by
    dsimp [hi]
    constructor <;> linarith [(hlo k).2]
  have htlo : Tendsto lo atTop (𝓝 lambda) := intensityBelow_tendsto lambda
  have hthi : Tendsto hi atTop (𝓝 lambda) := by
    simpa [hi,show 2*lambda-lambda=lambda by ring] using (tendsto_const_nhds.sub htlo :
      Tendsto (fun k => 2*lambda-lo k) atTop (𝓝 (2*lambda-lambda)))
  have ha : 0 < (transitionOpenness lambda hlambda : ℝ) := by
    change 0 < 1-Real.exp (-lambda)
    have := Real.exp_lt_one_iff.mpr (show -lambda < 0 by linarith)
    linarith
  have hsl := staticSurvival_tendsto ha
    (transitionOpenness_tendsto (fun k => (hlo k).1) hlambda htlo)
  have hsu := staticSurvival_tendsto ha
    (transitionOpenness_tendsto (fun k => (hhi k).1) hlambda hthi)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    (Filter.isBoundedUnder_of ⟨⊤,fun _ => le_top⟩)
    (Filter.isBoundedUnder_of ⟨0,fun _ => zero_le⟩)
  · apply le_of_tendsto hsl
    apply Eventually.of_forall
    intro k
    apply (le_liminf_iff').mpr
    intro c hc
    filter_upwards [(canonical_transition_tendsto (lo k) (hlo k).1).eventually_const_lt hc,
      hv.eventually_const_lt (hlo k).2] with n hn hvn
    exact hn.le.trans (canonical_raf_measure_mono n hvn.le)
  · apply ge_of_tendsto' hsu
    intro k
    apply (limsup_le_iff).mpr
    intro c hc
    filter_upwards [(canonical_transition_tendsto (hi k) (hhi k).1).eventually_lt_const hc,
      hv.eventually_lt_const (hhi k).2] with n hn hvn
    exact (canonical_raf_measure_mono n hvn.le).trans_lt hn

theorem variable_intensity_transition {v : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hv : Tendsto v atTop (𝓝 lambda)) :
    Tendsto (fun n => rafProbability n (v n)) atTop (𝓝 (transitionLimit lambda hlambda)) := by
  exact (ENNReal.tendsto_toReal (show staticSurvival (transitionOpenness lambda hlambda) ≠ ∞
    from measure_ne_top _ _)).comp (variable_intensity_canonical_tendsto hlambda hv)

/-- Substituting v_n=f_n/n gives the requested linear-catalysis window. -/
theorem rawCatalysisP_ratio (n : ℕ) (hn : 0 < n) (f : ℝ) :
    rawCatalysisP n (f/(n : ℝ)) = f/Fintype.card (RAF.Polymer.Reaction n) := by
  unfold rawCatalysisP
  rw [div_mul_cancel₀ f (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))]

theorem critical_window_transition {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => rafProbability n (f n/(n : ℝ))) atTop
      (𝓝 (transitionLimit lambda hlambda)) ∧
    0 < transitionLimit lambda hlambda ∧
    transitionLimit lambda hlambda ≤ 1-Real.exp (-36*lambda) ∧
    transitionLimit lambda hlambda < 1 := by
  exact ⟨variable_intensity_transition hlambda hf,(corrected_transition lambda hlambda).2⟩

end HordijkSteelThreshold
