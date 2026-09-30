module

public import proofs.HordijkSteelThreshold.StaticSeedProbability
public import proofs.HordijkSteelThreshold.StaticSeedBudget

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- At every positive iid reaction openness, ordinary closure from the literal
food cutoff two has an extensive mass with uniformly positive probability. -/
theorem static_food_two_bulk_positive (a : I) (ha : 0 < (a : ℝ)) :
    ∃ c : ENNReal, 0 < c ∧ ∀ N : ℕ, 0 < N →
      c ≤ staticReactionMeasure N a {ω |
        Fintype.card (Molecule N)/2 ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card} := by
  obtain ⟨L, hL, hbulk⟩ := static_bulk_near_full a ha 2 (by omega)
  let b : ENNReal := toNNReal a
  have hb : b ≠ 0 := ne_of_gt (by dsimp [b]; exact_mod_cast ha : 0 < b)
  have hb1 : b ≤ 1 := by dsimp [b]; exact_mod_cast a.property.2
  let c : ENNReal := b^(Fintype.card (Reaction L)) * (2 : ENNReal)⁻¹
  have hc : 0 < c := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero (pow_ne_zero _ hb) (by simp)
  refine ⟨c, hc, ?_⟩
  intro N hN
  let U := Fintype.card (Molecule N)
  let bad : Set (Reaction N → Prop) := {ω |
    2*(temporaryReactionClosure L (staticOpenReactions ω)).card < U}
  have hbad : staticReactionMeasure N a bad ≤ (2 : ENNReal)⁻¹ := by
    simpa [bad, U] using hbulk N hN
  have hgood : (2 : ENNReal)⁻¹ ≤ staticReactionMeasure N a {ω |
      U/2 ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card} := by
    calc
      _ = 1-(2 : ENNReal)⁻¹ := by norm_num
      _ ≤ 1-staticReactionMeasure N a bad := tsub_le_tsub_left hbad 1
      _ = staticReactionMeasure N a badᶜ := by
        rw [measure_compl (Set.Finite.measurableSet (Set.toFinite bad))
          (measure_ne_top _ _), measure_univ]
      _ ≤ _ := by
        apply measure_mono
        intro ω hω
        change ¬ 2*(temporaryReactionClosure L (staticOpenReactions ω)).card < U at hω
        change U/2 ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card
        omega
  have hcost : b^(Fintype.card (Reaction L)) ≤ b^(lowProductBridge N L).card :=
    pow_le_pow_of_le_one (zero_le : 0 ≤ b) hb1 (lowProductBridge_card_le N L)
  calc
    c ≤ b^(lowProductBridge N L).card *
        staticReactionMeasure N a {ω |
          U/2 ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card} :=
      mul_le_mul' hcost hgood
    _ ≤ _ := static_food_two_mass_lower N L (U/2) a

end HordijkSteelThreshold
