module

public import proofs.HordijkSteelThreshold.SeedSurvivalApproximation
public import proofs.HordijkSteelThreshold.SameParameterRichness
public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.HordijkSteelThreshold.TransitionLowerBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

noncomputable def lowerOpenness (a : I) (n : ℕ) : I :=
  ⟨(a : ℝ)*(1-1/((n : ℝ)+2)), by
    have hn : (2 : ℝ) ≤ (n : ℝ)+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hi : 0 < 1/((n : ℝ)+2) := by positivity
    have hj : 1/((n : ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    constructor
    · exact mul_nonneg a.property.1 (by linarith)
    · nlinarith [a.property.1,a.property.2]⟩

theorem lowerOpenness_lt (a : I) (ha : 0 < (a : ℝ)) (n : ℕ) :
    (lowerOpenness a n : ℝ) < a := by
  have hi : 0 < 1/((n : ℝ)+2) := by positivity
  dsimp [lowerOpenness]
  nlinarith

theorem half_le_lowerOpenness (a : I) (n : ℕ) :
    (a : ℝ)/2 ≤ lowerOpenness a n := by
  have hn : (2 : ℝ) ≤ (n : ℝ)+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : 1/((n : ℝ)+2) ≤ 1/2 := by
    exact one_div_le_one_div_of_le (by norm_num) hn
  dsimp [lowerOpenness]
  nlinarith [a.property.1]

theorem lowerOpenness_tendsto (a : I) :
    Tendsto (lowerOpenness a) atTop (𝓝 a) := by
  apply tendsto_subtype_rng.mpr
  have hi : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def,Nat.cast_add,add_assoc,show (1 : ℝ)+1=2 by norm_num] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa [lowerOpenness] using
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hi) :
      Tendsto (fun n : ℕ => (a : ℝ)*(1-1/((n : ℝ)+2))) atTop (𝓝 ((a : ℝ)*(1-0))))

/-- Finite seed approximation removes the entire left endpoint gap. -/
theorem staticSurvival_le_left (a : I) (ha : 0 < (a : ℝ)) :
    staticSurvival a ≤ staticSurvivalLeft (a : ℝ) := by
  let b0 : I := ⟨(a : ℝ)/2, by constructor <;> nlinarith [a.property.1,a.property.2]⟩
  have hb0 : 0 < (b0 : ℝ) := by dsimp [b0]; positivity
  have herr (m : ℕ) (hm : 2 ≤ m) :
      staticSurvival a ≤ staticSurvivalLeft (a : ℝ)+(m : ENNReal)⁻¹ := by
    obtain ⟨L,_hL,hseed⟩ := seed_probability_le_survival_add_error b0 hb0 m hm
    apply (staticSurvival_le_same_parameter_seed a ha (actualBinaryWords L)
      (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)).trans
    apply le_of_tendsto (finite_static_seed_probability_tendsto 2 a (actualBinaryWords L))
    apply Eventually.of_forall
    intro N
    apply le_of_tendsto ((continuous_static_event_probability N
      {ω | ∀ w ∈ actualBinaryWords L, ∃ x ∈ temporaryReactionClosure 2
        (staticOpenReactions ω), moleculeWord x = w}).continuousAt.tendsto.comp
          (lowerOpenness_tendsto a))
    apply Eventually.of_forall
    intro n
    have hfin : staticReactionMeasure N (lowerOpenness a n)
        {ω | ∀ w ∈ actualBinaryWords L, ∃ x ∈ temporaryReactionClosure 2
          (staticOpenReactions ω), moleculeWord x = w} ≤
        infiniteStaticMeasure (lowerOpenness a n) {field | ∀ w ∈ actualBinaryWords L,
          InfiniteReversibleGenerated 2 field w} := by
      rw [finite_static_seed_measure_eq]
      apply measure_mono
      intro field hf w hw
      exact finiteReversibleGenerated_to_infinite (hf w hw)
    have hl : staticSurvival (lowerOpenness a n) ≤ staticSurvivalLeft (a : ℝ) :=
      le_iSup_of_le (lowerOpenness a n) (le_iSup_of_le (lowerOpenness_lt a ha n) le_rfl)
    exact hfin.trans ((hseed (lowerOpenness a n) (half_le_lowerOpenness a n)).trans
      (add_le_add_left hl _))
  have ht : Tendsto (fun m : ℕ => staticSurvivalLeft (a : ℝ)+(m : ENNReal)⁻¹)
      atTop (𝓝 (staticSurvivalLeft (a : ℝ))) := by
    simpa using (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero :
      Tendsto (fun m : ℕ => staticSurvivalLeft (a : ℝ)+(m : ENNReal)⁻¹)
        atTop (𝓝 (staticSurvivalLeft (a : ℝ)+0)))
  exact ge_of_tendsto ht ((eventually_ge_atTop 2).mono (fun m hm => herr m hm))

end HordijkSteelThreshold
