module

public import proofs.HordijkSteelThreshold.SameParameterRichness
public import proofs.HordijkSteelThreshold.SeedSurvivalApproximation

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory unitInterval
open scoped ENNReal

def CompleteReversibleClosure (field : InfiniteSplitEnvironment) : Prop :=
  ∀ w : List Bool, w ≠ [] → InfiniteReversibleGenerated 2 field w

theorem completeClosure_unbounded {field : InfiniteSplitEnvironment}
    (h : CompleteReversibleClosure field) : ReversibleUnbounded 2 field := by
  intro K
  refine ⟨List.replicate (K+1) false, by simp, h _ ?_⟩
  simp

theorem survival_iff_complete_ae (a : I) (ha : 0 < (a : ℝ)) :
    ∀ᵐ field ∂infiniteStaticMeasure a,
      ReversibleUnbounded 2 field ↔ CompleteReversibleClosure field := by
  have ht : ∀ᵐ field ∂infiniteStaticMeasure a, ∀ w : List Bool,
      w ≠ [] → ReversibleUnbounded 2 field → InfiniteReversibleGenerated 2 field w := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : w = []
    · simp [hw]
    · exact (same_parameter_target_ae a ha w (List.length_pos_iff.mpr hw)).mono
        (fun _ h _ => h)
  filter_upwards [ht] with field hf
  exact ⟨fun hs w hw => hf w hw hs,completeClosure_unbounded⟩

theorem staticSurvival_eq_complete (a : I) (ha : 0 < (a : ℝ)) :
    staticSurvival a = infiniteStaticMeasure a {field | CompleteReversibleClosure field} := by
  apply measure_congr
  exact (survival_iff_complete_ae a ha).mono (fun _ h => propext h)

theorem finite_or_complete_ae (a : I) (ha : 0 < (a : ℝ)) :
    ∀ᵐ field ∂infiniteStaticMeasure a,
      (∃ K : ℕ, ∀ w, InfiniteReversibleGenerated 2 field w → w.length ≤ K) ∨
        CompleteReversibleClosure field := by
  filter_upwards [survival_iff_complete_ae a ha] with field hf
  by_cases h : ReversibleUnbounded 2 field
  · exact Or.inr (hf.mp h)
  · left
    change ¬ ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 field w at h
    push Not at h
    obtain ⟨K,hK⟩ := h
    exact ⟨K,fun w hw => le_of_not_gt (fun hl => hK w hl hw)⟩

theorem uniform_seed_survival_approximation (b0 : I) (hb0 : 0 < (b0 : ℝ))
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : I, b0 ≤ b →
      staticSurvival b ≤ infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ∧
      infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ staticSurvival b+(m : ENNReal)⁻¹ := by
  obtain ⟨L,hL,h⟩ := seed_probability_le_survival_add_error b0 hb0 m hm
  refine ⟨L,hL,fun b hb => ⟨?_,h b hb⟩⟩
  exact staticSurvival_le_same_parameter_seed b (hb0.trans_le hb) _
    (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)

end HordijkSteelThreshold
