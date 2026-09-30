module

public import proofs.HordijkSteelThreshold.ScalarHistoryLaw
public import proofs.HordijkSteelThreshold.FiniteInitialSegments

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

def activeTrace {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ) :
    Fin (T + 1) → R → Prop :=
  fun t r => r ∈ peelingActiveAt response closure t.val

theorem activeTrace_fun {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ) (t : Fin (T + 1)) :
    activeTrace response closure T t = fun r => r ∈ peelingActiveAt response closure t.val :=
  rfl


noncomputable def traceHistory {R : Type*} [Fintype R] {T : ℕ}
    (H : Fin (T + 1) → R → Prop) (t : ℕ) : Finset R := by
  classical
  exact if ht : t < T + 1 then Finset.univ.filter (H ⟨t, ht⟩) else ∅

theorem activeTrace_eq_iff {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ)
    (H : Fin (T + 1) → R → Prop) :
    activeTrace response closure T = H ↔
      ∀ t ≤ T, peelingActiveAt response closure t = traceHistory H t := by
  classical
  constructor
  · intro h t ht
    apply Finset.ext
    intro r
    have he := congrFun (congrFun h ⟨t, by omega⟩) r
    simpa only [traceHistory, dite_eq_left (by omega : t < T + 1),
      Finset.mem_filter, Finset.mem_univ, true_and, activeTrace] using
      (eq_iff_iff.mp he)
  · intro h
    funext t r
    apply propext
    change r ∈ peelingActiveAt response closure t.val ↔ H t r
    rw [h t.val (by omega)]
    simp only [traceHistory, dite_eq_left t.isLt, Finset.mem_filter,
      Finset.mem_univ, true_and]

/-- Exact finite-dimensional distributional replacement in the literal
molecule-reaction product measure, with a constructed ordered-prefix model.
This asserts equality in law, not equality for the same catalyst sample. -/
theorem activeTrace_map_eq_scalar {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n))
    (hclosure : Monotone closure) (T : ℕ) :
    (ambientPiMeasure n lambda).map (fun ω => activeTrace (catalystActive ω) closure T) =
      (ambientPiMeasure n lambda).map (fun ω => activeTrace
        (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T) := by
  apply Measure.ext_of_singleton
  intro H
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H),
    Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H)]
  have hs := peeling_history_probability_eq_prefix_any lambda closure hclosure
    (finiteInitialSegment (Molecule n)) (finiteInitialSegment_mono (Molecule n))
    (card_finiteInitialSegment (Molecule n)) (traceHistory H) T
  simpa only [Set.preimage, Set.mem_singleton_iff, activeTrace_eq_iff] using hs

end HordijkSteelThreshold
