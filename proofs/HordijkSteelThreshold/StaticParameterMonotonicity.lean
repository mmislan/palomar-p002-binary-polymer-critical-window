module

public import proofs.HordijkSteelThreshold.InfiniteSprinklingLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    simp [he]
  · have hltI : a < c := lt_of_le_of_ne hac he
    have hlt : (a : ℝ) < c := hltI
    have hd : 0 < 1-(a : ℝ) := by have hc := c.property.2; linarith
    let b : I := ⟨((c : ℝ)-a)/(1-(a : ℝ)), by
      constructor
      · positivity
      · apply (div_le_one hd).mpr
        have hc := c.property.2
        linarith⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    dsimp [b]
    field_simp
    nlinarith

theorem static_increasing_event_sprinkling (N : ℕ) (a b : I)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :
    staticReactionMeasure N a {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N (sprinklingParameter a b) {ω | P (staticOpenReactions ω)} := by
  have he : staticReactionMeasure N a {ω | P (staticOpenReactions ω)} =
      ((staticReactionMeasure N a).prod (staticReactionMeasure N b))
        {p | P (staticOpenReactions p.1)} := by
    have hs : {p : (Reaction N → Prop) × (Reaction N → Prop) | P (staticOpenReactions p.1)} =
        {ω | P (staticOpenReactions ω)} ×ˢ Set.univ := by ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, mul_one]
  rw [he]
  have hu := iid_union_field_map (Reaction N) a b
  change _ = _ at hu
  rw [show staticReactionMeasure N (sprinklingParameter a b) = _ from hu.symm,
    Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite _))]
  apply measure_mono
  intro p hp
  apply hP _ hp
  intro r hr
  simp only [staticOpenReactions, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact Or.inl hr

theorem static_increasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :
    staticReactionMeasure N a {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N c {ω | P (staticOpenReactions ω)} := by
  obtain ⟨b, rfl⟩ := exists_sprinkling_increment hac
  exact static_increasing_event_sprinkling N a b P hP

end HordijkSteelThreshold
