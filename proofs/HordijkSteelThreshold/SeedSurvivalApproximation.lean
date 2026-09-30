module

public import proofs.HordijkSteelThreshold.StaticDecreasingEvents
public import proofs.HordijkSteelThreshold.StaticSeedMassBound
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem seed_probability_le_survival_add_error (b0 : I) (hb0 : 0 < (b0 : ℝ))
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : I, b0 ≤ b →
      infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ staticSurvival b + (m : ENNReal)⁻¹ := by
  obtain ⟨L,hL,hbulk⟩ := static_bulk_near_full b0 hb0 m (by omega)
  refine ⟨L,hL,?_⟩
  intro b hb
  have hbad (N : ℕ) (hN : 0 < N) :
      staticReactionMeasure N b {ω | m*(temporaryReactionClosure L
        (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
    apply (static_decreasing_event_mono N hb
      (fun S => m*(temporaryReactionClosure L S).card < (m-1)*Fintype.card (Molecule N)) ?_).trans
      (hbulk N hN)
    intro S T hST hT
    exact (Nat.mul_le_mul_left m (Finset.card_le_card (temporaryReactionClosure_mono hST))).trans_lt hT
  have hK (K : ℕ) :
      infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤
      staticReactionMeasure (2*(K+2)) b (staticEscapeEvent 2 K) + (m : ENNReal)⁻¹ := by
    apply le_of_tendsto (finite_static_seed_probability_tendsto 2 b (actualBinaryWords L))
    filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
      (m*Fintype.card (Molecule (K+2))+1),eventually_ge_atTop 1] with N hlarge hN
    have hmass : staticReactionMeasure N b {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
        staticReactionMeasure (2*(K+2)) b (staticEscapeEvent 2 K) := by
      rw [finite_static_escape_measure_eq]
      apply (measure_mono (show {ω : Reaction N → Prop |
        (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ⊆
        {ω | ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), K+2 < molLength x}
        from ?_)).trans (static_capped_escape_le N K b)
      intro ω hω
      by_contra h
      have hs : temporaryReactionClosure 2 (staticOpenReactions ω) ⊆ binaryFood N (K+2) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt (fun hl => h ⟨x,hx,hl⟩)⟩
      have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff N (K+2))
      change (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card at hω
      have hmult : Fintype.card (Molecule N) ≤ (m-1)*Fintype.card (Molecule N) := by
        have hh := Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m-1 by omega)
        simpa using hh
      nlinarith
    exact (same_field_seed_mass_bound N L m b).trans
      (add_le_add hmass (hbad N (by omega)))
  exact ge_of_tendsto' ((finite_static_escape_probability_tendsto b).add_const (m : ENNReal)⁻¹) hK

end HordijkSteelThreshold
