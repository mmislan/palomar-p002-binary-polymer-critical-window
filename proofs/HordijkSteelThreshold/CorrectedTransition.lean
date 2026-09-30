module

public import proofs.HordijkSteelThreshold.StaticSurvivalLeftContinuity
public import proofs.HordijkSteelThreshold.TransitionSandwich
public import proofs.HordijkSteelThreshold.PositiveLowerPhase

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped ENNReal Topology

noncomputable def transitionOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · have := Real.exp_le_one_iff.mpr (show -lambda ≤ 0 by linarith)
      linarith
    · linarith [Real.exp_pos (-lambda)]⟩

noncomputable def transitionLimit (lambda : ℝ) (hlambda : 0 < lambda) : ℝ :=
  (staticSurvival (transitionOpenness lambda hlambda)).toReal

theorem canonical_transition_tendsto (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop
      (𝓝 (staticSurvival (transitionOpenness lambda hlambda))) := by
  apply transition_tendsto_of_no_gap hlambda (transitionOpenness lambda hlambda) rfl
  apply staticSurvival_le_left
  change 0 < 1-Real.exp (-lambda)
  have := Real.exp_lt_one_iff.mpr (show -lambda < 0 by linarith)
  linarith

theorem rafProbability_tendsto_transitionLimit (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun n => rafProbability n lambda) atTop (𝓝 (transitionLimit lambda hlambda)) := by
  exact (ENNReal.tendsto_toReal (show staticSurvival (transitionOpenness lambda hlambda) ≠ ∞
    from measure_ne_top _ _)).comp (canonical_transition_tendsto lambda hlambda)

/-- Full corrected fixed-intensity transition law in the literal canonical RAF
model: the limit is iid reversible survival, is positive, and stays below one. -/
theorem corrected_transition (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun n => rafProbability n lambda) atTop (𝓝 (transitionLimit lambda hlambda)) ∧
    0 < transitionLimit lambda hlambda ∧
    transitionLimit lambda hlambda ≤ 1-Real.exp (-36*lambda) ∧
    transitionLimit lambda hlambda < 1 := by
  have ht := rafProbability_tendsto_transitionLimit lambda hlambda
  obtain ⟨c,hc,he⟩ := rafProbability_eventually_positive hlambda
  have hp : 0 < transitionLimit lambda hlambda := hc.trans_le (ge_of_tendsto ht he)
  have hu : transitionLimit lambda hlambda ≤ 1-Real.exp (-36*lambda) := by
    rw [← ht.limsup_eq]
    exact rafProbability_limsup_le_gateway_ceiling hlambda
  exact ⟨ht,hp,hu,hu.trans_lt (by linarith [Real.exp_pos (-36*lambda)])⟩

end HordijkSteelThreshold
