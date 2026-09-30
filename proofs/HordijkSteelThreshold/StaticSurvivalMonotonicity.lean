module

public import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem static_escape_probability_mono (K : ℕ) {a b : I} (hab : a ≤ b) :
    staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) ≤
      staticReactionMeasure (2*(K+2)) b (staticEscapeEvent 2 K) := by
  apply static_increasing_event_mono _ hab
    (fun S => ∃ x ∈ temporaryReactionClosure 2 S, K+2 < (moleculeWord x).length)
  intro S T hST
  rintro ⟨x,hx,hl⟩
  exact ⟨x,temporaryReactionClosure_mono hST hx,hl⟩

theorem staticSurvival_mono : Monotone staticSurvival := by
  intro a b hab
  exact le_of_tendsto_of_tendsto (finite_static_escape_probability_tendsto a)
    (finite_static_escape_probability_tendsto b)
    (Filter.Eventually.of_forall (fun K => static_escape_probability_mono K hab))

end HordijkSteelThreshold
