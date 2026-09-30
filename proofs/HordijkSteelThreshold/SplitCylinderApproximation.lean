module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Cylinders

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory
open scoped symmDiff ENNReal

/-- Actual rectangular split prefixes approximate every measurable event in
the countable field under a finite measure. -/
theorem split_prefix_approximation (μ : Measure SplitField) [IsFiniteMeasure μ]
    (A : Set SplitField) (hA : MeasurableSet A) (ε : ENNReal) (hε : 0 < ε) :
    ∃ B : ℕ, ∃ C : Set SplitField,
      SplitPrefixDetermined (splitPrefixCoordinates B) C ∧ μ (C ∆ A) < ε := by
  let G := measurableCylinders (fun _ : List Bool × ℕ => Prop)
  have hG : IsSetRing G := by
    constructor
    · exact empty_mem_measurableCylinders _
    · intro s t hs ht
      exact union_mem_measurableCylinders (α := fun _ : List Bool × ℕ => Prop) hs ht
    · intro s t hs ht
      exact sdiff_mem_measurableCylinders (α := fun _ : List Bool × ℕ => Prop) hs ht
  have hcover : ∃ D : Set (Set SplitField), D.Countable ∧ D ⊆ G ∧ μ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,?_⟩
    · intro s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      exact univ_mem_measurableCylinders _
    · simp
  obtain ⟨C,hC,hclose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hG hcover
    (generateFrom_measurableCylinders.symm) hA hε
  obtain ⟨P,S,_hS,hCS⟩ := (mem_measurableCylinders C).mp hC
  let B := P.sup (fun z => max z.1.length z.2)
  refine ⟨B,C,?_,hclose⟩
  rw [hCS]
  intro ω η he
  have hrestrict : (fun z : P => ω z.val) = (fun z : P => η z.val) := by
    funext z
    have hbound := Finset.le_sup (f := fun z : List Bool × ℕ => max z.1.length z.2) z.property
    apply he
    apply (mem_splitPrefixCoordinates B z.val).mpr
    dsimp [B] at *
    constructor <;> omega
  change ((fun z : P => ω z.val) ∈ S) ↔ ((fun z : P => η z.val) ∈ S)
  rw [hrestrict]

end HordijkSteelThreshold
