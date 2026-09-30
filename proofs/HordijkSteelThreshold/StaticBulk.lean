module

public import proofs.HordijkSteelThreshold.StaticClosureMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- Static temporary-food bulk at every positive openness. For every m>=1,
one fixed food cutoff gives density at least 1-1/m with failure probability
at most 1/m, uniformly in every positive ambient cap. -/
theorem static_bulk_near_full (a : I) (ha : 0 < (a : ℝ)) (m : ℕ) (hm : 0 < m) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
          (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
  let η : ENNReal := (m : ENNReal)⁻¹/(m+1)
  have hη : 0 < η := by
    exact ENNReal.div_pos (by simp) (by simp)
  obtain ⟨L, hL, hbulk⟩ := static_bulk_deficit_bound a ha η hη
  refine ⟨L, hL, ?_⟩
  intro N hN
  let U := Fintype.card (Molecule N)
  let d := U/m+1
  have hd : 0 < d := Nat.succ_pos _
  have hUd : U ≤ m*d := by
    have ht : U/m < U/m+1 := by omega
    have hh := (Nat.div_lt_iff_lt_mul hm).mp ht
    dsimp [d]
    nlinarith
  have hsub : {ω : Reaction N → Prop |
      m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U} ⊆
      {ω | (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := by
    intro ω hω
    have hdiv := Nat.div_mul_le_self U m
    have hm1 : m-1+1 = m := by omega
    dsimp [d]
    change m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U at hω
    nlinarith
  have hcast : (U : ENNReal) ≤ (m : ENNReal)*d := by exact_mod_cast hUd
  have hratio : (U : ENNReal)*η/d ≤ (m : ENNReal)*η := by
    calc
      _ ≤ ((m : ENNReal)*d)*η/d := by gcongr
      _ = (m : ENNReal)*η := by
        rw [mul_right_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Nat.ne_of_gt hd) (by simp)]
  have htotal : η+(m : ENNReal)*η = (m : ENNReal)⁻¹ := by
    calc
      η+(m : ENNReal)*η = (1+(m : ENNReal))*η := by rw [add_mul, one_mul]
      _ = _ := ?_
    have he : (1 : ENNReal)+m = m+1 := add_comm _ _
    rw [he]
    exact ENNReal.mul_div_cancel (by simp) (by simp)
  calc
    _ ≤ staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := measure_mono hsub
    _ ≤ η+(U : ENNReal)*η/d := hbulk N hN d hd
    _ ≤ η+(m : ENNReal)*η := add_le_add le_rfl hratio
    _ = _ := htotal

end HordijkSteelThreshold
