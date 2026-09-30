module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

/-- Any injectively selected ambient coordinates have the literal set-Bernoulli law. -/
theorem ambient_subfield_set_map {n : ℕ} (lambda : ℝ) {J : Type*} [Fintype J]
    (f : J → AmbientCoord n) (hf : Function.Injective f) :
    (ambientPiMeasure n lambda).map (fun ω => {j | ω (f j)}) =
      setBernoulli (Set.univ : Set J) (catalysisP n lambda) := by
  have hi := (ambientCoordinate_iIndep n lambda).precomp hf
  have heval (j : J) : (ambientPiMeasure n lambda).map (fun ω => ω (f j)) =
      ambientCoordLaw (catalysisP n lambda) := by
    rw [ambientPiMeasure, Measure.infinitePi_map_eval]
  have hfield : (ambientPiMeasure n lambda).map (fun ω j => ω (f j)) =
      Measure.infinitePi (fun _ : J => ambientCoordLaw (catalysisP n lambda)) := by
    rw [hi.map_fun_eq_pi_map (fun j => (measurable_pi_apply (f j)).aemeasurable)]
    simp_rw [heval]
    exact (Measure.infinitePi_eq_pi _).symm
  calc
    _ = ((ambientPiMeasure n lambda).map (fun ω j => ω (f j))).map
        (fun v : J → Prop => {j | v j}) := by
      rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
      rfl
    _ = _ := by
      rw [hfield, setBernoulli_eq_map]
      simp only [Set.mem_univ, ambientCoordLaw, bernoulliMeasure_def]

def ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop) : CatalysisSample n :=
  ({z | ω (z.1,z.2.val)}, {z | ω (z.1,z.2.val)})

theorem ambientPartition_indep (n : ℕ) (lambda : ℝ) :
    IndepFun (fun ω : AmbientCoord n → Prop => (ambientPartition ω).1)
      (fun ω => (ambientPartition ω).2) (ambientPiMeasure n lambda) := by
  let B : Finset (AmbientCoord n) := Finset.univ.filter
    (fun z => RevSeedReaction (binaryPolymerCRS n 2) z.2)
  let D : Finset (AmbientCoord n) := Finset.univ.filter
    (fun z => ¬ RevSeedReaction (binaryPolymerCRS n 2) z.2)
  have hd : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro z hb hd
    exact (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hb).2
  have hi := (ambientCoordinate_iIndep n lambda).indepFun_finset B D hd
    (fun z => measurable_pi_apply z)
  let f : (B → Prop) → Set (SeedCoord n) := fun v => {z |
    v ⟨(z.1,z.2.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩}
  let g : (D → Prop) → Set (NonseedCoord n) := fun v => {z |
    v ⟨(z.1,z.2.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩}
  exact hi.comp (measurable_of_finite f) (measurable_of_finite g)

/-- The unpartitioned iid presentation is exactly the canonical seed/nonseed
sample measure. It has the same catalysis parameter and literal reaction IDs. -/
theorem ambientPartition_map (n : ℕ) (lambda : ℝ) :
    (ambientPiMeasure n lambda).map ambientPartition = uniformCatalysisMeasure n lambda := by
  have hs : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).1) =
      setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda) := by
    apply ambient_subfield_set_map lambda
    intro x y h
    exact Prod.ext (congrArg (fun z : AmbientCoord n => z.1) h)
      (Subtype.ext (congrArg (fun z : AmbientCoord n => z.2) h))
  have hn : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).2) =
      setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda) := by
    apply ambient_subfield_set_map lambda
    intro x y h
    exact Prod.ext (congrArg (fun z : AmbientCoord n => z.1) h)
      (Subtype.ext (congrArg (fun z : AmbientCoord n => z.2) h))
  have hi := (ambientPartition_indep n lambda).map_prod_eq_prod_map_map
    (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
  rw [hs,hn] at hi
  exact hi

@[simp] theorem catalysisOf_ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop)
    (x : Molecule n) (r : Reaction n) : catalysisOf (ambientPartition ω) x r ↔ ω (x,r) := by
  by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;>
    simp [catalysisOf, ambientPartition, h]

end HordijkSteelThreshold
