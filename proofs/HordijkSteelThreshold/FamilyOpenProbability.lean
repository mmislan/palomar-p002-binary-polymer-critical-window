module

public import proofs.HordijkSteelThreshold.CatalystPoolFamilyBlocks

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

@[simp] theorem ambientCoordLaw_false (p : I) :
    ambientCoordLaw p {False} = toNNReal (σ p) := by
  simp [ambientCoordLaw]

/-- Every coordinate in a finite block is closed. -/
def catalystBlockClosed {n : Nat} (ω : AmbientCoord n → Prop)
    (B : Finset (AmbientCoord n)) : Prop :=
  ∀ z ∈ B, ω z = False

/-- Exact finite-cylinder probability of a closed catalysis block. -/
theorem measure_catalystBlockClosed {n : Nat} (lambda : ℝ)
    (B : Finset (AmbientCoord n)) :
    ambientPiMeasure n lambda {ω | catalystBlockClosed ω B} =
      ∏ _z ∈ B, (toNNReal (σ (catalysisP n lambda)) : ENNReal) := by
  have hprod := (ambientCoordinate_iIndep n lambda).measure_inter_preimage_eq_mul B
      (sets := fun _z : AmbientCoord n => ({False} : Set Prop))
      (fun _ _ => MeasurableSet.singleton False)
  rw [show {ω | catalystBlockClosed ω B} =
      ⋂ z ∈ B, (fun ω : AmbientCoord n → Prop => ω z) ⁻¹' {False} by
        ext ω
        simp [catalystBlockClosed]]
  rw [hprod]
  apply Finset.prod_congr rfl
  intro z hz
  rw [ambientPiMeasure, ← Measure.map_apply (measurable_pi_apply z)
    (MeasurableSet.singleton False), Measure.infinitePi_map_eval]
  exact ambientCoordLaw_false (catalysisP n lambda)

theorem measure_catalystBlockClosed_card {n : Nat} (lambda : ℝ)
    (B : Finset (AmbientCoord n)) :
    ambientPiMeasure n lambda {ω | catalystBlockClosed ω B} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ B.card := by
  rw [measure_catalystBlockClosed]
  simp

/-- Exact probability that at least one coordinate in a fixed catalyst-pool
reaction-family block is open. -/
theorem measure_catalystPoolFamilyOpen {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | catalystPoolFamilyOpen ω C R} =
      1 - ∏ _z ∈ catalystPoolFamilyBlock C R,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) := by
  let B := catalystPoolFamilyBlock C R
  have hevent : {ω | catalystPoolFamilyOpen ω C R} =
      ({ω | catalystBlockClosed ω B})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro ⟨r, hr, x, hx, hω⟩ hclosed
      have hz := hclosed (x, r) (by
        simp [B, catalystPoolFamilyBlock, hx, hr])
      exact hz ▸ hω
    · intro hnotClosed
      by_contra hnotOpen
      apply hnotClosed
      intro z hz
      have hzmem := Finset.mem_product.mp hz
      have hfalse : ¬ω (z.1, z.2) := by
        intro hω
        apply hnotOpen
        exact ⟨z.2, hzmem.2, z.1, hzmem.1, hω⟩
      exact propext ⟨fun h => (hfalse h).elim, fun h => h.elim⟩
  have hclosed : MeasurableSet {ω | catalystBlockClosed ω B} := by
    have hpre := (measurable_of_finite
      (fun ω => catalystBlockClosed ω B)) (MeasurableSet.singleton True)
    convert hpre using 1
    ext ω
    simp
  rw [hevent, measure_compl hclosed (by simp), measure_univ,
    measure_catalystBlockClosed]

/-- Cardinality form of the exact family-open law.  This is the expression
used by the shell estimates: a family has `|C| |R|` fresh coordinates. -/
theorem measure_catalystPoolFamilyOpen_card {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | catalystPoolFamilyOpen ω C R} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * R.card) := by
  rw [measure_catalystPoolFamilyOpen]
  simp [catalystPoolFamilyBlock]

/-- Simultaneous failure of all target-indexed reaction families.  This is the
exact closed-coordinate event carried by a fixed first-barrier witness. -/
def catalystPoolFamiliesClosed {n : Nat} {ι : Type*}
    (ω : AmbientCoord n → Prop) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n)) : Prop :=
  ∀ i ∈ T, ¬ catalystPoolFamilyOpen ω C (R i)

/-- Exact probability cost of a fixed first-barrier witness.  No independence
between target histories is assumed: their actual reaction union determines
the number of distinct coordinates that the witness closes. -/
theorem measure_catalystPoolFamiliesClosed {n : Nat} {ι : Type*}
    [DecidableEq ι] (lambda : ℝ) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n)) :
    ambientPiMeasure n lambda
        {ω | catalystPoolFamiliesClosed ω C T R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * (T.biUnion R).card) := by
  classical
  rw [show {ω | catalystPoolFamiliesClosed ω C T R} =
      {ω | catalystBlockClosed ω (C.product (T.biUnion R))} by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro h z hz
          have hzprod := Finset.mem_product.mp hz
          obtain ⟨i, hi, hr⟩ := Finset.mem_biUnion.mp hzprod.2
          have hnot : ¬ω (z.1, z.2) := by
            intro hω
            apply h i hi
            exact ⟨z.2, hr, z.1, hzprod.1, hω⟩
          exact propext ⟨fun hω => (hnot hω).elim, fun hf => hf.elim⟩
        · intro hclosed i hi hopen
          obtain ⟨r, hr, x, hx, hω⟩ := hopen
          have hz : (x, r) ∈ C.product (T.biUnion R) := by
            exact Finset.mem_product.mpr
              ⟨hx, Finset.mem_biUnion.mpr ⟨i, hi, hr⟩⟩
          have hfalse := hclosed (x, r) hz
          exact hfalse ▸ hω]
  rw [measure_catalystBlockClosed_card]
  simp

/-- Exact closed probability for one fixed reaction family. -/
theorem measure_catalystPoolFamilyClosed {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | ¬catalystPoolFamilyOpen ω C R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * R.card) := by
  simpa [catalystPoolFamiliesClosed] using
    (measure_catalystPoolFamiliesClosed (ι := Unit) lambda C
      ({()} : Finset Unit) (fun _ => R))

/-- A lower bound on the number of alternative viable reactions gives the
closed-family pivotality discount used in the cavity expansion. -/
theorem measure_catalystPoolFamilyClosed_le {n d : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n))
    (hcard : d ≤ R.card) :
    ambientPiMeasure n lambda {ω | ¬catalystPoolFamilyOpen ω C R} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * d) := by
  rw [measure_catalystPoolFamilyClosed]
  apply pow_le_pow_right_of_le_one'
  · exact_mod_cast (σ (catalysisP n lambda)).2.2
  · exact Nat.mul_le_mul_left C.card hcard

end HordijkSteelThreshold
