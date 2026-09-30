module

public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.CanonicalCatalysisLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

theorem canonical_raf_measure_eq_ambient (n : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} := by
  rw [← ambientPartition_map n lambda, Measure.map_apply (measurable_of_finite _)
    (measurableSet_hasRAFEvent n)]
  have hc (ω : AmbientCoord n → Prop) : catalysisOf (ambientPartition ω) =
      (fun x r => ω (x,r)) := by
    funext x r
    exact propext (catalysisOf_ambientPartition ω x r)
  simp only [Set.preimage, HasRAFEvent, Set.mem_ofPred_eq, hc]

/-- The positive lower phase in the canonical literal RAF probability:
every fixed positive catalysis intensity has an eventual positive lower bound.
This does not assert convergence or identify the limiting transition curve. -/
theorem rafProbability_eventually_positive {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ rafProbability n lambda := by
  obtain ⟨c,hc,he⟩ := ambient_raf_probability_eventually_positive hlambda
  obtain ⟨n,hn⟩ := he.exists
  have hc1 : c ≤ 1 := hn.trans prob_le_one
  have hctop : c ≠ ∞ := ne_of_lt (hc1.trans_lt (by simp))
  refine ⟨c.toReal, ENNReal.toReal_pos (ne_of_gt hc) hctop, ?_⟩
  filter_upwards [he] with n hn
  rw [← canonical_raf_measure_eq_ambient n lambda] at hn
  exact ENNReal.toReal_mono (measure_ne_top _ _) hn

/-- Explicit eventual lower bound, with all source parameters supplied. -/
theorem positive_lower_phase (lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c ≤ rafProbability n lambda := by
  obtain ⟨c,hc,he⟩ := rafProbability_eventually_positive hlambda
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  exact ⟨c,hc,N,hN⟩

end HordijkSteelThreshold
