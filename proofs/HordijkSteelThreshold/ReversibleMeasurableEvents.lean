module

public import proofs.HordijkSteelThreshold.ReversibleClosureDock

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete

theorem measurable_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    Measurable (fun field : InfiniteSplitEnvironment => FiniteReversibleGenerated N L field w) := by
  let restrict : InfiniteSplitEnvironment → (Reaction N → Prop) :=
    fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)
  have hm : Measurable restrict := by
    apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply (reactionLeftLength r)).comp
      (measurable_pi_apply (moleculeWord (reactionProduct r)))
  let event : (Reaction N → Prop) → Prop := fun ω => ∃ x ∈ temporaryReactionClosure L
    (Finset.univ.filter ω), moleculeWord x = w
  have he : (fun field => FiniteReversibleGenerated N L field w) = event ∘ restrict := by
    funext field
    exact propext (finiteReversible_iff_literalClosure field w)
  rw [he]
  exact (measurable_of_finite event).comp hm

theorem measurableSet_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} := by
  simpa using (MeasurableSet.singleton True).preimage (measurable_finiteReversibleGenerated N L w)

theorem measurableSet_infiniteReversibleGenerated (L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} := by
  have he : {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} =
      ⋃ N : ℕ, {field | FiniteReversibleGenerated N L field w} := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact infiniteReversibleGenerated_iff_finite_certificate
  rw [he]
  exact MeasurableSet.iUnion (fun N => measurableSet_finiteReversibleGenerated N L w)

/-- Any finite collection of infinite generation certificates fits in one cap. -/
theorem finite_seed_common_cap {L : ℕ} {field : InfiniteSplitEnvironment}
    (seed : Finset (List Bool)) :
    (∀ w ∈ seed, InfiniteReversibleGenerated L field w) ↔
      ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N L field w := by
  constructor
  · induction seed using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | @insert w seed _ ih =>
      intro h
      obtain ⟨N, hN⟩ := infiniteReversibleGenerated_finite_certificate
        (h w (Finset.mem_insert_self _ _))
      obtain ⟨M, hM⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
      refine ⟨max N M, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact finiteReversibleGenerated_mono_cap (Nat.le_max_left _ _) hN
      · exact finiteReversibleGenerated_mono_cap (Nat.le_max_right _ _) (hM v hv)
  · rintro ⟨N, hN⟩ w hw
    exact finiteReversibleGenerated_to_infinite (hN w hw)

theorem measurableSet_finite_seed (N L : ℕ) (seed : Finset (List Bool)) :
    MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
  have he : {field : InfiniteSplitEnvironment | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} =
      ⋂ w ∈ seed, {field | FiniteReversibleGenerated N L field w} := by ext field; simp
  rw [he]
  exact MeasurableSet.biInter (Finset.countable_toSet seed)
    (fun w _ => measurableSet_finiteReversibleGenerated N L w)

/-- Finite seed probabilities approximate the infinite seed event under any
fixed measure on the countable split environment. No cap exchange is assumed. -/
theorem finite_seed_probability_tendsto (μ : Measure InfiniteSplitEnvironment)
    (L : ℕ) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => μ {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w})
      Filter.atTop (nhds (μ {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  let E : ℕ → Set InfiniteSplitEnvironment :=
    fun N => {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w}
  have hm : Monotone E := by
    intro N M hNM field hfield w hw
    exact finiteReversibleGenerated_mono_cap hNM (hfield w hw)
  have he : (⋃ N, E N) = {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w} := by
    ext field
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, E]
    exact (finite_seed_common_cap seed).symm
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
  rw [he] at ht
  exact ht

end HordijkSteelThreshold
