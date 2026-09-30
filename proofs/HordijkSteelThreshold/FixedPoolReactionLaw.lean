module

public import proofs.HordijkSteelThreshold.ColumnEventProduct
public import proofs.HordijkSteelThreshold.FamilyOpenProbability
public import proofs.HordijkSteelThreshold.SourceStaticBarrier
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

@[simp] theorem fixedPoolParameter_coe (p : I) (k : ℕ) :
    (fixedPoolParameter p k : ℝ) = 1-(1-(p : ℝ))^k := by
  simp [fixedPoolParameter]

theorem fixedPoolParameter_ennreal (p : I) (k : ℕ) :
    (toNNReal (fixedPoolParameter p k) : ENNReal) =
      1-(toNNReal (σ p) : ENNReal)^k := by
  have hpow : toNNReal ((σ p)^k) = (toNNReal (σ p))^k := by
    apply NNReal.eq
    simp
  apply ENNReal.eq_sub_of_add_eq (by simp)
  rw [← ENNReal.coe_pow, ← hpow, ← ENNReal.coe_add]
  simp [fixedPoolParameter]

theorem fixedPool_iIndep {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n)) :
    iIndepFun (fun r (ω : AmbientCoord n → Prop) => catalystPoolOpen ω C r)
      (ambientPiMeasure n lambda) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _hsets
  have hh := measure_columnEvents lambda
    (fun r col => (∃ x ∈ C, col x) ∈ sets r) S
  have he : (⋂ r ∈ S, (fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r) ⁻¹' sets r) =
      {ω | ∀ r ∈ S, (∃ x ∈ C, ω (x,r)) ∈ sets r} := by
    ext ω
    simp [catalystPoolOpen]
  rw [he]
  exact hh

theorem fixedPool_open_measure {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (r : Reaction n) :
    ambientPiMeasure n lambda {ω | catalystPoolOpen ω C r} =
      (toNNReal (fixedPoolParameter (catalysisP n lambda) C.card) : ENNReal) := by
  rw [fixedPoolParameter_ennreal]
  simpa [catalystPoolFamilyOpen] using measure_catalystPoolFamilyOpen_card lambda C {r}

theorem probability_prop_eq_of_true (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {True} = ν {True}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro q
  by_cases hq : q
  · have he : q = True := propext (iff_true_intro hq)
    simpa only [he] using h
  · have he : q = False := propext (iff_false_intro hq)
    have hs : ({False} : Set Prop) = {True}ᶜ := by ext t; simp
    rw [he, hs, measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),
      measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _), measure_univ, measure_univ, h]

theorem fixedPool_column_map {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (r : Reaction n) :
    (ambientPiMeasure n lambda).map (fun ω => catalystPoolOpen ω C r) =
      ambientCoordLaw (fixedPoolParameter (catalysisP n lambda) C.card) := by
  have hm := measurable_of_finite (fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r)
  apply probability_prop_eq_of_true
  rw [Measure.map_apply hm (MeasurableSet.singleton _)]
  have he : (fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r) ⁻¹' {True} =
      {ω | catalystPoolOpen ω C r} := by ext ω; simp
  rw [he, fixedPool_open_measure]
  simp [ambientCoordLaw]

/-- Exact full iid law of the field supported by a deterministic catalyst pool.
This does not assert independence for a pool selected from the same sample. -/
theorem fixedPool_reaction_map {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n)) :
    (ambientPiMeasure n lambda).map (fun ω r => catalystPoolOpen ω C r) =
      staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda) C.card) := by
  rw [(fixedPool_iIndep lambda C).map_fun_eq_pi_map
    (fun r => (measurable_of_finite _).aemeasurable)]
  simp_rw [fixedPool_column_map]
  exact (Measure.infinitePi_eq_pi _).symm

theorem fixedPool_closure_statistic {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (closure : Finset (Reaction n) → Finset (Molecule n)) (P : Finset (Molecule n) → Prop) :
    ambientPiMeasure n lambda {ω | P (closure (catalystActive ω C))} =
      staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda) C.card)
        {ω | P (closure (staticOpenReactions ω))} := by
  rw [← fixedPool_reaction_map lambda C, Measure.map_apply (measurable_of_finite _)
    (Set.Finite.measurableSet (Set.toFinite _))]
  rfl

theorem source_mass_ge_iid_static {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k T : ℕ) :
    staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) k).card) {ω | k ≤ (closure (staticOpenReactions ω)).card} ≤
    ambientPiMeasure n lambda {ω | k ≤ (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
  rw [← fixedPool_closure_statistic lambda (finiteInitialSegment (Molecule n) k)
    closure (fun S => k ≤ S.card)]
  exact measure_source_mass_ge_static lambda closure hclosure k T

end HordijkSteelThreshold
