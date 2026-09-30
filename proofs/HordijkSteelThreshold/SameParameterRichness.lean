module

public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.SplitCylinderNull
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory unitInterval
open scoped ENNReal

theorem unbounded_missing_target_null (a : I) (ha : 0 < (a : ℝ))
    (v : List Bool) (hv : 0 < v.length) :
    infiniteSplitPi a (unboundedMissingTarget v) = 0 := by
  have hm : MeasurableSet (unboundedMissingTarget v) :=
    ((measurableSet_reversibleUnbounded 2).inter
      (measurableSet_infiniteReversibleGenerated 2 v).compl).preimage measurable_currySplitField
  have hapos : 0 < (toNNReal a : ENNReal) := by exact_mod_cast ha
  apply split_cylinder_deficit_null (infiniteSplitPi a) (unboundedMissingTarget v) hm
    (1-(toNNReal a : ENNReal)^(v.length+1))
  · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (pow_ne_zero _ (ne_of_gt hapos))
  · exact record_cylinder_deficit a v hv

/-- Infinite growth generates every prescribed target at the original iid
openness. Freshness is supplied by own-cap records, not an extra field. -/
theorem same_parameter_target_ae (a : I) (ha : 0 < (a : ℝ))
    (v : List Bool) (hv : 0 < v.length) :
    ∀ᵐ field ∂infiniteStaticMeasure a, ReversibleUnbounded 2 field →
      InfiniteReversibleGenerated 2 field v := by
  rw [ae_iff]
  have he : {field : InfiniteSplitEnvironment | ¬ (ReversibleUnbounded 2 field →
      InfiniteReversibleGenerated 2 field v)} =
      {field | ReversibleUnbounded 2 field} ∩
        {field | InfiniteReversibleGenerated 2 field v}ᶜ := by ext field; simp
  rw [he,infiniteStaticMeasure,Measure.map_apply measurable_currySplitField
    ((measurableSet_reversibleUnbounded 2).inter
      (measurableSet_infiniteReversibleGenerated 2 v).compl)]
  exact unbounded_missing_target_null a ha v hv

theorem staticSurvival_le_same_parameter_seed (a : I) (ha : 0 < (a : ℝ))
    (seed : Finset (List Bool)) (hseed : ∀ w ∈ seed, 0 < w.length) :
    staticSurvival a ≤ infiniteStaticMeasure a
      {field | ∀ w ∈ seed, InfiniteReversibleGenerated 2 field w} := by
  apply measure_mono_ae
  have hall : ∀ᵐ field ∂infiniteStaticMeasure a, ∀ w : seed,
      ReversibleUnbounded 2 field → InfiniteReversibleGenerated 2 field w.val :=
    (ae_all_iff).mpr (fun w => same_parameter_target_ae a ha w.val (hseed w.val w.property))
  filter_upwards [hall] with field hfield
  intro hu w hw
  exact hfield ⟨w,hw⟩ hu

end HordijkSteelThreshold
