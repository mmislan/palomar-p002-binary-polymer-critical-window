module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.HordijkSteelThreshold.TargetTrialProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

def unionSplitField (base extra : InfiniteSplitEnvironment) : InfiniteSplitEnvironment :=
  fun w k => base w k ∨ extra w k

theorem fixed_base_sprinkling_failure_le (base : InfiniteSplitEnvironment)
    (hbase : ReversibleUnbounded 2 base) (v : List Bool) (hv : 0 < v.length)
    (a : I) (J : ℕ) :
    infiniteStaticMeasure a {extra | ¬ InfiniteReversibleGenerated 2 (unionSplitField base extra) v} ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^J := by
  obtain ⟨N, W, hcard, hgen, hsep⟩ := unbounded_finite_trials (ell := v.length) hbase J
  let B := restrictedSplitReactions N base
  let restrict : InfiniteSplitEnvironment → (Reaction N → Prop) :=
    fun extra r => extra (moleculeWord (reactionProduct r)) (reactionLeftLength r)
  have hm : Measurable restrict := by
    apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  have he (extra : InfiniteSplitEnvironment) : B ∪ staticOpenReactions (restrict extra) =
      restrictedSplitReactions N (unionSplitField base extra) := by
    dsimp only [B, restrict]
    unfold restrictedSplitReactions staticOpenReactions unionSplitField
    ext r
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : {extra | ¬ InfiniteReversibleGenerated 2 (unionSplitField base extra) v} ⊆
      {extra | ¬ ∃ y ∈ temporaryReactionClosure 2 (B ∪ staticOpenReactions (restrict extra)),
        moleculeWord y = v} := by
    intro extra hno hyes
    rw [he] at hyes
    exact hno (finiteReversibleGenerated_to_infinite
      ((finiteReversible_iff_literalClosure _ v).mpr hyes))
  have hmap : infiniteStaticMeasure a {extra | ¬ ∃ y ∈ temporaryReactionClosure 2
      (B ∪ staticOpenReactions (restrict extra)), moleculeWord y = v} =
      staticReactionMeasure N a {ω | ¬ ∃ y ∈ temporaryReactionClosure 2
        (B ∪ staticOpenReactions ω), moleculeWord y = v} := by
    rw [← infiniteStatic_restriction_map N a, Measure.map_apply hm
      (Set.Finite.measurableSet (Set.toFinite _))]
    rfl
  have hb := finite_sprinkling_target_failure B (fun w : W => w.val) v hv
    (fun w => (hgen w.val w.property).1)
    (fun w => (hgen w.val w.property).2.1)
    (fun u w hne => hsep u.val u.property w.val w.property (fun h => hne (Subtype.ext h)))
    (fun w => finiteReversible_to_literalClosure (hgen w.val w.property).2.2) a
  calc
    _ ≤ _ := measure_mono hsub
    _ = _ := hmap
    _ ≤ _ := by simpa only [Fintype.card_coe, hcard] using hb

/-- Every fixed unbounded base language becomes rich after any positive
independent sprinkling, one nonempty target at a time. -/
theorem fixed_base_sprinkling_target_ae (base : InfiniteSplitEnvironment)
    (hbase : ReversibleUnbounded 2 base) (v : List Bool) (hv : 0 < v.length)
    (a : I) (ha : 0 < (a : ℝ)) :
    ∀ᵐ extra ∂infiniteStaticMeasure a, InfiniteReversibleGenerated 2 (unionSplitField base extra) v := by
  rw [ae_iff]
  apply le_antisymm _ zero_le
  have hap : (toNNReal a : ENNReal) ≠ 0 := by
    have hh : 0 < (toNNReal a : ENNReal) := by exact_mod_cast ha
    exact ne_of_gt hh
  have hq : 1-(toNNReal a : ENNReal)^(v.length+1) < 1 :=
    ENNReal.sub_lt_self (by simp) (by simp) (pow_ne_zero _ hap)
  exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    (fun J => fixed_base_sprinkling_failure_le base hbase v hv a J)

end HordijkSteelThreshold
