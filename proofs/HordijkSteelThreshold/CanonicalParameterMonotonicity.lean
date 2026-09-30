module

public import proofs.HordijkSteelThreshold.PositiveLowerPhase
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval

theorem catalysisP_mono (N : ℕ) : Monotone (catalysisP N) := by
  intro a b hab
  change min 1 (max 0 (rawCatalysisP N a)) ≤ min 1 (max 0 (rawCatalysisP N b))
  apply min_le_min le_rfl
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

theorem canonical_raf_measure_mono (N : ℕ) {a c : ℝ} (hac : a ≤ c) :
    uniformCatalysisMeasure N a (HasRAFEvent N) ≤
      uniformCatalysisMeasure N c (HasRAFEvent N) := by
  rw [canonical_raf_measure_eq_ambient,canonical_raf_measure_eq_ambient]
  obtain ⟨b,hb⟩ := exists_sprinkling_increment (catalysisP_mono N hac)
  let E : Set (AmbientCoord N → Prop) := {ω | ∃ S : Finset (Reaction N),
    IsRevRAF (binaryPolymerCRS N 2) (fun x r => ω (x,r)) S}
  have he : ambientPiMeasure N a E =
      ((ambientPiMeasure N a).prod (Measure.infinitePi (fun _ : AmbientCoord N => ambientCoordLaw b)))
        (E ×ˢ Set.univ) := by rw [Measure.prod_prod,measure_univ,mul_one]
  change ambientPiMeasure N a E ≤ ambientPiMeasure N c E
  rw [he]
  have hu := iid_union_field_map (AmbientCoord N) (catalysisP N a) b
  rw [hb] at hu
  rw [show ambientPiMeasure N c = _ from hu.symm,
    Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite E))]
  apply measure_mono
  rintro p ⟨⟨S,hs,hg,hcat⟩,_⟩
  refine ⟨S,hs,hg,?_⟩
  intro r hr
  obtain ⟨x,k,hx,hc⟩ := hcat r hr
  exact ⟨x,k,hx,Or.inl hc⟩

end HordijkSteelThreshold
