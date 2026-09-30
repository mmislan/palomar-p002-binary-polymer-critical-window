module

public import proofs.HordijkSteelThreshold.CatalystPoolFamilyBlocks

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- An arbitrary measurable predicate on one complete reaction column is
independent of arbitrary predicates on a disjoint family of other columns. -/
theorem columnEvent_indep_remaining {n : ℕ} (lambda : ℝ)
    (E : Reaction n → (Molecule n → Prop) → Prop)
    (r : Reaction n) (S : Finset (Reaction n)) (hr : r ∉ S) :
    IndepFun (fun ω : AmbientCoord n → Prop => E r (fun x => ω (x, r)))
      (fun ω => ∀ s ∈ S, E s (fun x => ω (x, s)))
      (ambientPiMeasure n lambda) := by
  classical
  let B := catalystPoolFamilyBlock (Finset.univ : Finset (Molecule n)) {r}
  let D := catalystPoolFamilyBlock (Finset.univ : Finset (Molecule n)) S
  have hdis : Disjoint B D :=
    catalystPoolFamilyBlock_disjoint Finset.univ (Finset.disjoint_singleton_left.mpr hr)
  have ht := (ambientCoordinate_iIndep n lambda).indepFun_finset B D hdis
    (fun _ => measurable_pi_apply _)
  let f : (B → Prop) → Prop := fun v =>
    E r (fun x => v ⟨(x, r), by simp [B, catalystPoolFamilyBlock]⟩)
  let g : (D → Prop) → Prop := fun v =>
    ∀ s, ∀ hs : s ∈ S,
      E s (fun x => v ⟨(x, s), by simp [D, catalystPoolFamilyBlock, hs]⟩)
  exact ht.comp (measurable_of_finite f) (measurable_of_finite g)

/-- Full product formula, not just pairwise independence. Predicates may
encode an entire fixed history of nested-pool observations in each column. -/
theorem measure_columnEvents {n : ℕ} (lambda : ℝ)
    (E : Reaction n → (Molecule n → Prop) → Prop) (S : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, E r (fun x => ω (x, r))} =
      ∏ r ∈ S, ambientPiMeasure n lambda {ω | E r (fun x => ω (x, r))} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert r S hr ih =>
    have hi := (columnEvent_indep_remaining lambda E r S hr).measure_inter_preimage_eq_mul
        {True} {True}
        (MeasurableSet.singleton True) (MeasurableSet.singleton True)
    have he : {ω : AmbientCoord n → Prop | ∀ s ∈ insert r S, E s (fun x => ω (x, s))} =
        {ω | E r (fun x => ω (x, r))} ∩
        {ω | ∀ s ∈ S, E s (fun x => ω (x, s))} := by
      ext ω
      simp
    rw [he, Finset.prod_insert hr]
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
      ih] using hi

end HordijkSteelThreshold
