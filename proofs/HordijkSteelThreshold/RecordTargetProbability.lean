module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory unitInterval
open scoped ENNReal

/-- Same-parameter target failure on an arbitrary prefix event which has
already generated a specified record word. No extra sprinkling is used. -/
theorem record_target_failure_bound (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrecord : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (currySplitField ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ InfiniteReversibleGenerated 2 (currySplitField ω) v}) ≤
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  obtain ⟨T,hsize,hdis,hgen⟩ := record_target_support w v hw hv
  have hs : E ∩ {ω | ¬ InfiniteReversibleGenerated 2 (currySplitField ω) v} ⊆
      E ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    intro hopen
    exact hω.2 (hgen (currySplitField ω) (hrecord ω hω.1) hopen)
  apply (measure_mono hs).trans
  rw [split_prefix_failure_measure a _ T hdis E hE]
  have hpow : (toNNReal a : ENNReal)^(v.length+1) ≤ (toNNReal a : ENNReal)^T.card := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · exact hsize
  exact mul_le_mul_right (tsub_le_tsub_left hpow 1) _

end HordijkSteelThreshold
