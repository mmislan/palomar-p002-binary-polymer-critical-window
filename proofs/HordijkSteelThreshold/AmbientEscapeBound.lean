module

public import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem static_capped_escape_le (N K : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∃ x ∈ temporaryReactionClosure 2
      (staticOpenReactions ω), K+2 < molLength x} ≤
      infiniteStaticMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infiniteStatic_restriction_map N a, Measure.map_apply]
  · apply measure_mono
    intro field h
    change ∃ x ∈ temporaryReactionClosure 2 (restrictedSplitReactions N field),
      K+2 < molLength x at h
    obtain ⟨x,hx,hl⟩ := h
    apply (reversibleEscapeEvent_iff 2 K field).mpr
    exact ⟨moleculeWord x, by simpa only [moleculeWord_length] using hl,
      finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible field x hx)⟩
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)

theorem ambient_escape_le_finite_static (n K : ℕ) (lambda : ℝ) :
    ambientPiMeasure n lambda {ω | ∃ x ∈ temporaryReactionClosure 2
      (catalystActive ω Finset.univ), K+2 < molLength x} ≤
    staticReactionMeasure (2*(K+2))
      (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
      (staticEscapeEvent 2 K) := by
  rw [fixedPool_closure_statistic lambda Finset.univ (temporaryReactionClosure 2)
    (fun S => ∃ x ∈ S, K+2 < molLength x), Finset.card_univ,
    finite_static_escape_measure_eq]
  exact static_capped_escape_le n K _

end HordijkSteelThreshold
