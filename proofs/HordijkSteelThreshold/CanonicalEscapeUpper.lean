module

public import proofs.HordijkSteelThreshold.BoundedRAFProbability
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.PositiveLowerPhase

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- A finite upper comparison in the canonical source. The cutoff is fixed
independently of ambient size; no conditioning on extinction occurs. -/
theorem canonical_raf_le_finite_escape (n K : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) ≤
    staticReactionMeasure (2*(K+2))
      (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
      (staticEscapeEvent 2 K) +
      (Fintype.card (Molecule (K+2)) : ENNReal) * 68 *
        (toNNReal (catalysisP n lambda) : ENNReal) := by
  rw [canonical_raf_measure_eq_ambient]
  exact (ambient_raf_le_escape_add_seed n (K+2) lambda).trans
    (add_le_add_left (ambient_escape_le_finite_static n K lambda) _)

end HordijkSteelThreshold
