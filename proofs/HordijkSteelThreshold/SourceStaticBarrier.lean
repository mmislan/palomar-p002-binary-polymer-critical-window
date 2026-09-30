module

public import proofs.HordijkSteelThreshold.ScalarHistoryDistribution

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Every statistic of the active set at a fixed time transfers through the
compiled trace law. No measurable structure on finsets needs to be chosen. -/
theorem measure_peeling_statistic_eq_scalar {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (T : ℕ) (stat : Finset (Reaction n) → Prop) :
    ambientPiMeasure n lambda {ω | stat (peelingActiveAt (catalystActive ω) closure T)} =
    ambientPiMeasure n lambda {ω | stat (peelingActiveAt
      (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T)} := by
  classical
  let E : Set (Fin (T + 1) → Reaction n → Prop) :=
    {H | stat (Finset.univ.filter (H ⟨T, Nat.lt_succ_self T⟩))}
  have hfilterActive
      (response : Finset (Molecule n) → Finset (Reaction n)) :
      Finset.univ.filter
          (activeTrace response closure T ⟨T, Nat.lt_succ_self T⟩) =
        peelingActiveAt response closure T := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, activeTrace]
  have he := congrArg (fun μ : Measure (Fin (T + 1) → Reaction n → Prop) => μ E)
    (activeTrace_map_eq_scalar lambda closure hclosure T)
  rw [Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite E)),
    Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite E))] at he
  simpa only [E, Set.preimage, Set.mem_ofPred_eq, hfilterActive] using he

theorem prefix_static_barrier {n : ℕ} (ω : AmbientCoord n → Prop)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k : ℕ) (hk : k ≤ (closure
      (catalystActive ω (finiteInitialSegment (Molecule n) k))).card) (T : ℕ) :
    closure (catalystActive ω (finiteInitialSegment (Molecule n) k)) ⊆
      closure (peelingActiveAt
        (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T) := by
  have hq : Monotone (fun j => catalystActive ω (finiteInitialSegment (Molecule n) j)) :=
    (catalystActive_mono ω).comp (finiteInitialSegment_mono (Molecule n))
  induction T with
  | zero =>
    have hb : k ≤ Fintype.card (Molecule n) := hk.trans (Finset.card_le_univ _)
    simpa only [peelingActiveAt, Finset.card_univ] using hclosure (hq hb)
  | succ T ih =>
    exact hclosure (hq (hk.trans (Finset.card_le_card ih)))

/-- A static iid reaction field tested against a deterministic k-element
catalyst pool lower-bounds source closure mass at every peeling time. -/
theorem measure_source_mass_ge_static {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k T : ℕ) :
    ambientPiMeasure n lambda {ω | k ≤ (closure
      (catalystActive ω (finiteInitialSegment (Molecule n) k))).card} ≤
    ambientPiMeasure n lambda {ω | k ≤
      (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
  rw [measure_peeling_statistic_eq_scalar lambda closure hclosure T
    (fun A => k ≤ (closure A).card)]
  apply measure_mono
  intro ω hω
  exact hω.trans (Finset.card_le_card (prefix_static_barrier ω closure hclosure k hω T))

end HordijkSteelThreshold
