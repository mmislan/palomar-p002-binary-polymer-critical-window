module

public import proofs.HordijkSteelThreshold.InfiniteSprinklingLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval Filter
open scoped ENNReal

noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

/-- Survival below the final openness pays for every fixed rich seed at the
sprinkled parameter; no prescribed all-open seed cost is lost. -/
theorem staticSurvival_le_sprinkled_seed (a b : I) (hb : 0 < (b : ℝ))
    (seed : Finset (List Bool)) (hseed : ∀ w ∈ seed, 0 < w.length) :
    staticSurvival a ≤ infiniteStaticMeasure (sprinklingParameter a b)
      {field | ∀ w ∈ seed, InfiniteReversibleGenerated 2 field w} := by
  have hm : MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, InfiniteReversibleGenerated 2 field w} := by
    have he : {field : InfiniteSplitEnvironment | ∀ w ∈ seed, InfiniteReversibleGenerated 2 field w} =
        ⋂ w ∈ seed, {field | InfiniteReversibleGenerated 2 field w} := by ext field; simp
    rw [he]
    exact MeasurableSet.biInter seed.countable_toSet
      (fun w _ => measurableSet_infiniteReversibleGenerated 2 w)
  rw [← infiniteStatic_union_map a b, Measure.map_apply measurable_unionSplitField hm]
  have he : staticSurvival a = ((infiniteStaticMeasure a).prod (infiniteStaticMeasure b))
      {p | ReversibleUnbounded 2 p.1} := by
    have hs : {p : InfiniteSplitEnvironment × InfiniteSplitEnvironment | ReversibleUnbounded 2 p.1} =
        {field | ReversibleUnbounded 2 field} ×ˢ Set.univ := by ext p; simp
    rw [hs, Measure.prod_prod, measure_univ, mul_one]
    rfl
  rw [he]
  apply measure_mono_ae
  filter_upwards [random_base_sprinkling_seed_ae (infiniteStaticMeasure a) seed hseed b hb] with p hp
  intro hbase
  exact (finite_seed_common_cap seed).mpr (hp hbase)

end HordijkSteelThreshold
