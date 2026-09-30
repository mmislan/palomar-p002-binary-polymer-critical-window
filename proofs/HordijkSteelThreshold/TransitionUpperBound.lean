module

public import proofs.HordijkSteelThreshold.CanonicalEscapeUpper
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem fullPoolParameter_tendsto {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda)) :
    Tendsto (fun n => fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
      atTop (𝓝 a) := by
  apply tendsto_subtype_rng.mpr
  rw [ha]
  simpa [fixedPoolParameter_coe, catalystPoolOpenProbability,
    catalystPoolClosedProbability] using
    catalystPoolOpenProbability_tendsto (fun n => (Finset.univ : Finset (Molecule n)))
      hlambda (by simpa using catalysisP_mul_card_molecule_tendsto hlambda)

theorem catalysisP_ennreal_tendsto_zero {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (toNNReal (catalysisP n lambda) : ENNReal)) atTop (𝓝 0) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (catalysisP_tendsto_zero hlambda)
  simpa only [Function.comp_def, ← coe_toNNReal, ENNReal.ofReal_zero,
    ENNReal.ofReal_coe_nnreal] using ht

theorem transition_limsup_le_finite_escape {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda)) (K : ℕ) :
    limsup (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop ≤
      staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) := by
  have ht := (continuous_static_event_probability (2*(K+2)) (staticEscapeEvent 2 K)).tendsto a
    |>.comp (fullPoolParameter_tendsto hlambda a ha)
  have herr := ENNReal.Tendsto.const_mul (catalysisP_ennreal_tendsto_zero hlambda)
    (Or.inr (by finiteness : (Fintype.card (Molecule (K+2)) : ENNReal)*68 ≠ ⊤))
  have hsum := ht.add herr
  simp only [mul_zero, add_zero] at hsum
  apply (limsup_le_iff).mpr
  intro c hc
  filter_upwards [hsum.eventually_lt_const hc] with n hn
  exact (canonical_raf_le_finite_escape n K lambda).trans_lt hn

theorem transition_limsup_upper {lambda : ℝ} (hlambda : 0 < lambda)
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda)) :
    limsup (fun n => uniformCatalysisMeasure n lambda (HasRAFEvent n)) atTop ≤
      staticSurvival a := by
  exact ge_of_tendsto' (finite_static_escape_probability_tendsto a)
    (fun K => transition_limsup_le_finite_escape hlambda a ha K)

end HordijkSteelThreshold
