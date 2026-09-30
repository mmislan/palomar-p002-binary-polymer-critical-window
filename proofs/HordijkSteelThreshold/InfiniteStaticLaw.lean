module

public import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  intro r s he
  have hp := moleculeWord_injective (congrArg Prod.fst he)
  have hk := congrArg Prod.snd he
  rcases r with ⟨kr, cr, sr⟩
  rcases s with ⟨ks, cs, ss⟩
  have hidx : kr = ks := congrArg Sigma.fst hp
  subst ks
  have hc : cr = cs := by
    have h := congrArg (fun x : Molecule N => x.2.val) hp
    exact Fin.ext h
  subst cs
  have hs : sr = ss := Fin.ext (by change sr.val + 1 = ss.val + 1 at hk; omega)
  subst ss
  rfl

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply (w,k)

noncomputable def infiniteSplitPi (a : I) : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability (a : I) : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

noncomputable instance infiniteStaticMeasure_probability (a : I) : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  unfold infiniteStaticMeasure
  infer_instance

/-- The infinite iid environment restricts to the exact finite static source
law, with each product/split pair a distinct coordinate. -/
theorem infiniteStatic_restriction_map (N : ℕ) (a : I) :
    (infiniteStaticMeasure a).map
      (fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) =
      staticReactionMeasure N a := by
  have hi : iIndepFun (fun z (ω : (List Bool × ℕ) → Prop) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (literalSplitCoordinate_injective N)
  have hm : Measurable (fun field : InfiniteSplitEnvironment =>
      fun r : Reaction N => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) := by
    apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  rw [infiniteStaticMeasure, Measure.map_map hm measurable_currySplitField]
  change (infiniteSplitPi a).map (fun ω r => ω (literalSplitCoordinate r)) = _
  rw [hs.map_fun_eq_pi_map (fun r => (measurable_pi_apply (literalSplitCoordinate r)).aemeasurable)]
  have he (r : Reaction N) : (infiniteSplitPi a).map (fun ω => ω (literalSplitCoordinate r)) =
      ambientCoordLaw a := by rw [infiniteSplitPi, Measure.infinitePi_map_eval]
  simp_rw [he]
  exact (Measure.infinitePi_eq_pi _).symm

theorem finite_static_seed_measure_eq (N L : ℕ) (a : I) (seed : Finset (List Bool)) :
    staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w} =
    infiniteStaticMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
  rw [← infiniteStatic_restriction_map N a, Measure.map_apply]
  · congr 1
    ext field
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    apply forall_congr'
    intro w
    apply forall_congr'
    intro _
    exact (finiteReversible_iff_literalClosure field w).symm
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)

/-- Actual finite static-source seed probabilities converge to the infinite
reversible seed probability at fixed openness. -/
theorem finite_static_seed_probability_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w})
      Filter.atTop (nhds (infiniteStaticMeasure a
        {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  simp_rw [finite_static_seed_measure_eq]
  exact finite_seed_probability_tendsto (infiniteStaticMeasure a) L seed

end HordijkSteelThreshold
