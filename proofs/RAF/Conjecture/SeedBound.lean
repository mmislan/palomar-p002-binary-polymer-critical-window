module

public import proofs.RAF.Core.Seed
public import proofs.RAF.Probability.SeedEvent

@[expose] public section

namespace RAF.Conjecture

/-- Event containment `RAF ⊆ seed-open`, expressed at probability level. -/
theorem raf_probability_seed_bound {rafProbability seedClosedProbability : ℝ}
    (hcontain : rafProbability ≤ 1 - seedClosedProbability) :
    rafProbability + seedClosedProbability ≤ 1 := by
  linarith

end RAF.Conjecture
