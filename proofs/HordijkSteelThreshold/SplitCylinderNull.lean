module

public import proofs.HordijkSteelThreshold.SplitCylinderApproximation

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory
open scoped symmDiff ENNReal

/-- A measurable event with a uniform strict deficit on all finite-prefix
cylinders is null. This consumes the actual prefix approximation theorem. -/
theorem split_cylinder_deficit_null (μ : Measure SplitField) [IsFiniteMeasure μ]
    (A : Set SplitField) (hA : MeasurableSet A) (q : ENNReal) (hq : q < 1)
    (hdef : ∀ B C, SplitPrefixDetermined (splitPrefixCoordinates B) C →
      μ (A ∩ C) ≤ μ C * q) : μ A = 0 := by
  by_contra hpos
  have ha : 0 < (μ A).toReal := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have hqt : q ≠ ⊤ := ne_of_lt (hq.trans_le (by simp))
  have hqr : q.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hqt ENNReal.one_ne_top).mpr hq
  have hq0 : 0 ≤ q.toReal := ENNReal.toReal_nonneg
  let ε : ℝ := (1-q.toReal)*(μ A).toReal/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B,C,hC,hclose⟩ := split_prefix_approximation μ A hA (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  have hsmall : (μ (C ∆ A)).toReal < ε := by
    have ht := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hclose
    simpa only [ENNReal.toReal_ofReal hε.le] using ht
  have hsubA : A ⊆ (A ∩ C) ∪ (C ∆ A) := by
    intro x hx
    by_cases hc : x ∈ C
    · exact Or.inl ⟨hx,hc⟩
    · exact Or.inr (by simp [Set.mem_symmDiff,hx,hc])
  have hsubC : C ⊆ A ∪ (C ∆ A) := by
    intro x hx
    by_cases ha : x ∈ A
    · exact Or.inl ha
    · exact Or.inr (by simp [Set.mem_symmDiff,hx,ha])
  have h1 := ENNReal.toReal_mono
    (show μ (A ∩ C)+μ (C ∆ A) ≠ ⊤ by finiteness)
    ((measure_mono hsubA).trans (measure_union_le _ _))
  have h2 := ENNReal.toReal_mono
    (show μ A+μ (C ∆ A) ≠ ⊤ by finiteness)
    ((measure_mono hsubC).trans (measure_union_le _ _))
  have h3 := ENNReal.toReal_mono
    (show μ C*q ≠ ⊤ from ENNReal.mul_ne_top (measure_ne_top _ _) hqt) (hdef B C hC)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h1 h2
  rw [ENNReal.toReal_mul] at h3
  have he : 4*ε = (1-q.toReal)*(μ A).toReal := by dsimp [ε]; ring
  nlinarith

end HordijkSteelThreshold
