module

public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

/-- Seed and supplied-seed bulk are evaluated in the same field. Their
dependence is harmless: seed probability is bounded by success plus bulk error. -/
theorem same_field_seed_mass_bound (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ≤
    staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
    staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  have hsub : {ω : Reaction N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ∪
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} := by
    intro ω hseed
    by_cases hb : m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule N)
    · exact Or.inr hb
    · left
      have hcontain : temporaryReactionClosure L (staticOpenReactions ω) ⊆
          temporaryReactionClosure 2 (staticOpenReactions ω) := by
        apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
        intro x hx
        have hw : moleculeWord x ∈ actualBinaryWords L :=
          (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x, by rwa [moleculeWord_length]⟩
        obtain ⟨y, hy, he⟩ := hseed _ hw
        exact moleculeWord_injective he ▸ hy
      exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hcontain))
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- The full smaller-parameter survival probability, up to arbitrary strict
slack and the explicit bulk error, lower-bounds near-full static mass. -/
theorem static_survival_bulk_eventually (a b : I) (hb : 0 < (b : ℝ))
    (m : ℕ) (hm : 0 < m) (c : ENNReal) (hc : c < staticSurvival a) :
    ∀ᶠ N in atTop, c ≤ staticReactionMeasure N (sprinklingParameter a b)
      {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} + (m : ENNReal)⁻¹ := by
  let q := sprinklingParameter a b
  have hq : 0 < (q : ℝ) := by
    rw [show (q : ℝ) = (a : ℝ)+(1-(a : ℝ))*(b : ℝ) from sprinklingParameter_value a b]
    have ha0 := a.property.1
    have ha1 := a.property.2
    have hb1 := b.property.2
    nlinarith
  obtain ⟨L, _, hbulk⟩ := static_bulk_near_full q hq m hm
  have hs := staticSurvival_le_sprinkled_seed a b hb (actualBinaryWords L)
    (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)
  have ht := finite_static_seed_probability_tendsto 2 q (actualBinaryWords L)
  have he := (tendsto_order.mp ht).1 c (hc.trans_le hs)
  filter_upwards [he, eventually_ge_atTop 1] with N hN hpos
  exact hN.le.trans ((same_field_seed_mass_bound N L m q).trans
    (add_le_add le_rfl (hbulk N (by omega))))

end HordijkSteelThreshold
