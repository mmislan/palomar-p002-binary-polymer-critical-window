module

public import proofs.HordijkSteelThreshold.AmbientOpen
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

abbrev AmbientCoord (n : Nat) := Molecule n × Reaction n

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

/-- The uncurried product presentation of uniform catalysis coordinates. -/
noncomputable def ambientPiMeasure (n : Nat) (lambda : ℝ) :
    Measure (AmbientCoord n → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw (RAF.Concrete.catalysisP n lambda))

noncomputable instance ambientPiMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  infer_instance

def ambientPiOpen {n : Nat} (ω : AmbientCoord n → Prop) (r : Reaction n) : Prop :=
  ∃ x, ω (x, r)

def reactionBlockFinset {n : Nat} (r : Reaction n) : Finset (AmbientCoord n) :=
  Finset.univ.filter fun z => z.2 = r

theorem reactionBlockFinset_disjoint {n : Nat} {r s : Reaction n} (hrs : r ≠ s) :
    Disjoint (reactionBlockFinset r) (reactionBlockFinset s) := by
  rw [Finset.disjoint_left]
  intro z hzr hzs
  exact hrs ((Finset.mem_filter.mp hzr).2.symm.trans (Finset.mem_filter.mp hzs).2)

theorem ambientCoordinate_iIndep (n : Nat) (lambda : ℝ) :
    iIndepFun (fun z (ω : AmbientCoord n → Prop) => ω z)
      (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem ambientPiOpen_indep {n : Nat} (lambda : ℝ) {r s : Reaction n}
    (hrs : r ≠ s) :
    IndepFun (fun ω => ambientPiOpen ω r) (fun ω => ambientPiOpen ω s)
      (ambientPiMeasure n lambda) := by
  let R := reactionBlockFinset r
  let S := reactionBlockFinset s
  have htuple := (ambientCoordinate_iIndep n lambda).indepFun_finset R S
    (reactionBlockFinset_disjoint hrs) (fun _ => measurable_pi_apply _)
  have hleft : (fun ω => ambientPiOpen ω r) =
      (fun v : R → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    simp [ambientPiOpen, R, reactionBlockFinset]
  have hright : (fun ω => ambientPiOpen ω s) =
      (fun v : S → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    simp [ambientPiOpen, S, reactionBlockFinset]
  rw [hleft, hright]
  exact htuple.comp (measurable_of_finite _) (measurable_of_finite _)

end HordijkSteelThreshold
