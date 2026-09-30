module

public import proofs.HordijkSteelThreshold.ColumnEventProduct

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory

def detourFailed {R Ω : Type*} (field : R → Ω → Prop) (B : Finset R) (ω : Ω) : Prop :=
  ¬ ∀ r ∈ B, field r ω

theorem measure_detourOpen {R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (a : ENNReal)
    (hmarg : ∀ r, μ {ω | field r ω} = a) (B : Finset R) :
    μ {ω | ∀ r ∈ B, field r ω} = a^B.card := by
  have hprod := hind.measure_inter_preimage_eq_mul B
    (sets := fun _ : R => ({True} : Set Prop)) (fun _ _ => MeasurableSet.singleton True)
  have he : {ω | ∀ r ∈ B, field r ω} = ⋂ r ∈ B, (field r) ⁻¹' {True} := by
    ext ω
    simp
  rw [he, hprod]
  have hsingle (r : R) : μ ((field r) ⁻¹' {True}) = a := by
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using hmarg r
  simp only [hsingle, Finset.prod_const]

theorem measure_detourFailed {R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r)) (a : ENNReal)
    (hmarg : ∀ r, μ {ω | field r ω} = a) (B : Finset R) :
    μ {ω | detourFailed field B ω} = 1-a^B.card := by
  have hm : MeasurableSet {ω | ∀ r ∈ B, field r ω} := by
    have he : {ω | ∀ r ∈ B, field r ω} = ⋂ r ∈ B, (field r) ⁻¹' {True} := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter (fun r => MeasurableSet.iInter (fun _ =>
      (MeasurableSet.singleton True).preimage (hmeas r)))
  change μ ({ω | ∀ r ∈ B, field r ω}ᶜ) = _
  rw [measure_compl hm (measure_ne_top _ _), measure_univ,
    measure_detourOpen μ field hind a hmarg B]

theorem detourFailed_indep_remaining {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) (field : R → Ω → Prop) (hind : iIndepFun field μ)
    (hmeas : ∀ r, Measurable (field r)) (support : I → Finset R)
    (i : I) (T : Finset I) (hdis : ∀ j ∈ T, Disjoint (support i) (support j)) :
    IndepFun (detourFailed field (support i))
      (fun ω => ∀ j ∈ T, detourFailed field (support j) ω) μ := by
  classical
  let D := T.biUnion support
  have hBD : Disjoint (support i) D := by
    apply Finset.disjoint_left.mpr
    intro r hri hrD
    obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hrD
    exact Finset.disjoint_left.mp (hdis j hj) hri hrj
  have ht := hind.indepFun_finset (support i) D hBD hmeas
  let f : (support i → Prop) → Prop := fun v => ¬ ∀ r, ∀ hr : r ∈ support i, v ⟨r,hr⟩
  let g : (D → Prop) → Prop := fun v => ∀ j, ∀ hj : j ∈ T,
    ¬ ∀ r, ∀ hr : r ∈ support j, v ⟨r, Finset.mem_biUnion.mpr ⟨j,hj,hr⟩⟩
  exact ht.comp (measurable_of_finite f) (measurable_of_finite g)

/-- Full product formula for disjoint fixed reaction supports. Selection has
already occurred deterministically; no independence of effective basic edges is used. -/
theorem measure_disjoint_detours_failed {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (hmarg : ∀ r, μ {ω | field r ω} = a)
    (support : I → Finset R) (T : Finset I)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) :
    μ {ω | ∀ i ∈ T, detourFailed field (support i) ω} =
      ∏ i ∈ T, (1-a^(support i).card) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hsep : ∀ j ∈ T, Disjoint (support i) (support j) := by
      intro j hj
      exact hdis i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro he; exact hi (he ▸ hj))
    have ht : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → Disjoint (support j) (support k) := by
      intro j hj k hk hne
      exact hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    have hp := (detourFailed_indep_remaining μ field hind hmeas support i T hsep).measure_inter_preimage_eq_mul {True} {True}
        (MeasurableSet.singleton True) (MeasurableSet.singleton True)
    have he : {ω | ∀ j ∈ insert i T, detourFailed field (support j) ω} =
        {ω | detourFailed field (support i) ω} ∩
        {ω | ∀ j ∈ T, detourFailed field (support j) ω} := by ext ω; simp
    rw [he, Finset.prod_insert hi]
    simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
      ih ht, measure_detourFailed μ field hind hmeas a hmarg] using hp

theorem measure_disjoint_detours_failed_le {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (ha : a ≤ 1) (hmarg : ∀ r, μ {ω | field r ω} = a)
    (support : I → Finset R) (T : Finset I)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j))
    (hsize : ∀ i ∈ T, (support i).card ≤ 2) :
    μ {ω | ∀ i ∈ T, detourFailed field (support i) ω} ≤ (1-a^2)^T.card := by
  rw [measure_disjoint_detours_failed μ field hind hmeas a hmarg support T hdis]
  calc
    _ ≤ ∏ _i ∈ T, (1-a^2) := by
      apply Finset.prod_le_prod
      intro i hi
      apply tsub_le_tsub_left
      exact pow_le_pow_of_le_one (zero_le : 0 ≤ a) ha (hsize i hi)
    _ = _ := by simp

end HordijkSteelThreshold
