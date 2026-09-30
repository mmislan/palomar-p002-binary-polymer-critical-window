module

public import proofs.HordijkSteelThreshold.ReversibleEscape
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem reversible_escape_probability_tendsto
    (μ : Measure InfiniteSplitEnvironment) [IsFiniteMeasure μ] (L : ℕ) :
    Filter.Tendsto (fun K => μ (reversibleEscapeEvent L K)) Filter.atTop
      (nhds (μ {field | ReversibleUnbounded L field})) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun K => (measurableSet_reversibleEscapeEvent L K).nullMeasurableSet)
    (reversibleEscapeEvent_antitone L) ⟨0, measure_ne_top _ _⟩
  rw [reversibleEscapeEvent_inter] at ht
  exact ht

def staticEscapeEvent (L K : ℕ) : Set (Reaction (2*(K+L)) → Prop) :=
  {ω | ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω),
    K+L < (moleculeWord x).length}

theorem finite_static_escape_measure_eq (L K : ℕ) (a : I) :
    staticReactionMeasure (2*(K+L)) a (staticEscapeEvent L K) =
      infiniteStaticMeasure a (reversibleEscapeEvent L K) := by
  rw [← infiniteStatic_restriction_map (2*(K+L)) a, Measure.map_apply]
  · congr 1
    ext field
    change (∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions _ field),
      K+L < (moleculeWord x).length) ↔
      ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L field w
    constructor
    · rintro ⟨x, hx, hl⟩
      exact ⟨moleculeWord x, hl, literalClosure_to_finiteReversible field x hx⟩
    · rintro ⟨w, hw, hg⟩
      obtain ⟨x, hx, he⟩ := finiteReversible_to_literalClosure hg
      exact ⟨x, hx, by simpa [he] using hw⟩
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)

/-- Survival is approximated from above by actual finite static events. -/
theorem finite_static_escape_probability_tendsto (a : I) :
    Filter.Tendsto (fun K => staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K))
      Filter.atTop (nhds (staticSurvival a)) := by
  simp_rw [finite_static_escape_measure_eq]
  exact reversible_escape_probability_tendsto (infiniteStaticMeasure a) 2

end HordijkSteelThreshold
