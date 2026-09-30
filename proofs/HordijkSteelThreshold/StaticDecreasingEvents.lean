module

public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval

theorem static_decreasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Antitone P) :
    staticReactionMeasure N c {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | P (staticOpenReactions ω)} := by
  obtain ⟨b,rfl⟩ := exists_sprinkling_increment hac
  have hu := iid_union_field_map (Reaction N) a b
  change _ = _ at hu
  rw [show staticReactionMeasure N (sprinklingParameter a b) = _ from hu.symm,
    Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite _))]
  have hs : {p : (Reaction N → Prop) × (Reaction N → Prop) |
      P (staticOpenReactions (fun r => p.1 r ∨ p.2 r))} ⊆
      {ω | P (staticOpenReactions ω)} ×ˢ Set.univ := by
    intro p hp
    refine ⟨hP ?_ hp,Set.mem_univ _⟩
    intro r hr
    simp only [staticOpenReactions,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
    exact Or.inl hr
  exact (measure_mono hs).trans_eq (by rw [Measure.prod_prod,measure_univ,mul_one]; rfl)

end HordijkSteelThreshold
