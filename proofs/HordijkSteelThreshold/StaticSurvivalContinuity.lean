module

public import proofs.HordijkSteelThreshold.StaticSurvivalLeftContinuity

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem staticSurvival_le_finite_escape (a : I) (K : ℕ) :
    staticSurvival a ≤ staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) := by
  rw [finite_static_escape_measure_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

/-- Sequential continuity at every positive openness, with no uniform finite
witness cap assumed. -/
theorem staticSurvival_tendsto {u : ℕ → I} {a : I}
    (ha : 0 < (a : ℝ)) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => staticSurvival (u n)) atTop (𝓝 (staticSurvival a)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨d,hcd,hds⟩ := exists_between hc
    have ht : Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 c) := by
      simpa using (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero :
        Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 (c+0)))
    obtain ⟨m,hem,hm⟩ := ((ht.eventually_lt_const hcd).and (eventually_ge_atTop 2)).exists
    let b0 : I := ⟨(a : ℝ)/2, by constructor <;> nlinarith [a.property.1,a.property.2]⟩
    have hb0 : 0 < (b0 : ℝ) := by dsimp [b0]; positivity
    obtain ⟨L,_hL,hseed⟩ := seed_probability_le_survival_add_error b0 hb0 m hm
    have hg := staticSurvival_le_same_parameter_seed a ha (actualBinaryWords L)
      (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)
    obtain ⟨N,hN⟩ := ((finite_static_seed_probability_tendsto 2 a (actualBinaryWords L)).eventually_const_lt
      (hds.trans_le hg)).exists
    have hfinite := ((continuous_static_event_probability N
      {ω | ∀ w ∈ actualBinaryWords L, ∃ x ∈ temporaryReactionClosure 2
        (staticOpenReactions ω), moleculeWord x = w}).tendsto a).comp hu
    have hbase : ∀ᶠ n in atTop, b0 ≤ u n := by
      have hr := continuous_subtype_val.continuousAt.tendsto.comp hu
      exact (hr.eventually_const_lt (show (b0 : ℝ) < (a : ℝ) by dsimp [b0]; linarith)).mono
        (fun _ h => h.le)
    filter_upwards [hfinite.eventually_const_lt hN,hbase] with n hn hbn
    have hf : staticReactionMeasure N (u n) {ω | ∀ w ∈ actualBinaryWords L,
        ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ≤
        infiniteStaticMeasure (u n) {field | ∀ w ∈ actualBinaryWords L,
          InfiniteReversibleGenerated 2 field w} := by
      rw [finite_static_seed_measure_eq]
      apply measure_mono
      intro field h w hw
      exact finiteReversibleGenerated_to_infinite (h w hw)
    exact lt_of_add_lt_add_right (hem.trans (hn.trans_le (hf.trans (hseed (u n) hbn))))
  · intro c hc
    obtain ⟨K,hK⟩ := ((finite_static_escape_probability_tendsto a).eventually_lt_const hc).exists
    have ht := ((continuous_static_event_probability (2*(K+2)) (staticEscapeEvent 2 K)).tendsto a).comp hu
    exact (ht.eventually_lt_const hK).mono (fun n hn => (staticSurvival_le_finite_escape (u n) K).trans_lt hn)

end HordijkSteelThreshold
