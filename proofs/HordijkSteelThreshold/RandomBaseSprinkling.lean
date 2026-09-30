module

public import proofs.HordijkSteelThreshold.FixedBaseSprinkling

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

theorem measurable_unionSplitField :
    Measurable (fun p : InfiniteSplitEnvironment × InfiniteSplitEnvironment =>
      unionSplitField p.1 p.2) := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  have heval : Measurable (fun field : InfiniteSplitEnvironment => field w k) :=
    (measurable_pi_apply k).comp (measurable_pi_apply w)
  have h1 : Measurable (fun p : InfiniteSplitEnvironment × InfiniteSplitEnvironment => p.1 w k) :=
    heval.comp measurable_fst
  have h2 : Measurable (fun p : InfiniteSplitEnvironment × InfiniteSplitEnvironment => p.2 w k) :=
    heval.comp measurable_snd
  exact (measurable_of_finite (fun z : Prop × Prop => z.1 ∨ z.2)).comp (h1.prodMk h2)

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  have he : {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
      ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_h : K < w.length),
        {field | InfiniteReversibleGenerated L field w} := by
    ext field
    simp [ReversibleUnbounded]
  rw [he]
  exact MeasurableSet.iInter (fun _ => MeasurableSet.iUnion (fun w =>
    MeasurableSet.iUnion (fun _ => measurableSet_infiniteReversibleGenerated L w)))

/-- Pointwise zero sections suffice; no measurable choice of trial words
across different base samples is needed. -/
theorem random_base_sprinkling_target_ae (μ : Measure InfiniteSplitEnvironment)
    [SFinite μ] (v : List Bool) (hv : 0 < v.length) (a : I) (ha : 0 < (a : ℝ)) :
    ∀ᵐ p ∂μ.prod (infiniteStaticMeasure a), ReversibleUnbounded 2 p.1 →
      InfiniteReversibleGenerated 2 (unionSplitField p.1 p.2) v := by
  rw [ae_iff]
  have he : MeasurableSet {p : InfiniteSplitEnvironment × InfiniteSplitEnvironment |
      ¬ (ReversibleUnbounded 2 p.1 → InfiniteReversibleGenerated 2 (unionSplitField p.1 p.2) v)} := by
    have h1 : MeasurableSet {p : InfiniteSplitEnvironment × InfiniteSplitEnvironment |
        ReversibleUnbounded 2 p.1} := (measurableSet_reversibleUnbounded 2).preimage measurable_fst
    have h2 := (measurableSet_infiniteReversibleGenerated 2 v).preimage measurable_unionSplitField
    simp only [Classical.not_imp]
    change MeasurableSet ({p : InfiniteSplitEnvironment × InfiniteSplitEnvironment |
      ReversibleUnbounded 2 p.1} ∩
        {p | InfiniteReversibleGenerated 2 (unionSplitField p.1 p.2) v}ᶜ)
    exact h1.inter h2.compl
  rw [Measure.prod_apply he]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro base
  by_cases h : ReversibleUnbounded 2 base
  · simpa [h] using (ae_iff.mp (fixed_base_sprinkling_target_ae base h v hv a ha))
  · simp [h]

/-- After positive independent sprinkling, an unbounded random base supplies
every prescribed finite nonempty-word seed in some finite cap, almost surely. -/
theorem random_base_sprinkling_seed_ae (μ : Measure InfiniteSplitEnvironment)
    [SFinite μ] (seed : Finset (List Bool)) (hseed : ∀ w ∈ seed, 0 < w.length)
    (a : I) (ha : 0 < (a : ℝ)) :
    ∀ᵐ p ∂μ.prod (infiniteStaticMeasure a), ReversibleUnbounded 2 p.1 →
      ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N 2 (unionSplitField p.1 p.2) w := by
  have hall : ∀ᵐ p ∂μ.prod (infiniteStaticMeasure a),
      ∀ w : seed, ReversibleUnbounded 2 p.1 →
        InfiniteReversibleGenerated 2 (unionSplitField p.1 p.2) w.val := by
    rw [ae_all_iff]
    intro w
    exact random_base_sprinkling_target_ae μ w.val (hseed w.val w.property) a ha
  filter_upwards [hall] with p hp
  intro hbase
  apply (finite_seed_common_cap seed).mp
  intro w hw
  exact hp ⟨w, hw⟩ hbase

end HordijkSteelThreshold
