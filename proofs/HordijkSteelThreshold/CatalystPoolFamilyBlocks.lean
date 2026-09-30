module

public import proofs.HordijkSteelThreshold.CatalystPoolBlocks

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Coordinate block queried by a finite family of reactions against a fixed
prospective catalyst pool. -/
def catalystPoolFamilyBlock {n : Nat} (C : Finset (Molecule n))
    (R : Finset (Reaction n)) : Finset (AmbientCoord n) :=
  C.product R

/-- At least one reaction in a finite family is catalyzed by the prospective
internal pool. -/
def catalystPoolFamilyOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) : Prop :=
  ∃ r ∈ R, catalystPoolOpen ω C r

theorem catalystPoolFamilyBlock_disjoint {n : Nat}
    (C : Finset (Molecule n)) {R S : Finset (Reaction n)}
    (hRS : Disjoint R S) :
    Disjoint (catalystPoolFamilyBlock C R)
      (catalystPoolFamilyBlock C S) := by
  rw [Finset.disjoint_left]
  intro z hzR hzS
  have hrR := (Finset.mem_product.mp hzR).2
  have hrS := (Finset.mem_product.mp hzS).2
  exact Finset.disjoint_left.mp hRS hrR hrS

/-- Finite reaction families with disjoint reaction identities remain
independent after each family is existentially supported by the same fixed
prospective catalyst pool. -/
theorem catalystPoolFamilyOpen_indep {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {R S : Finset (Reaction n)}
    (hRS : Disjoint R S) :
    IndepFun (fun ω => catalystPoolFamilyOpen ω C R)
      (fun ω => catalystPoolFamilyOpen ω C S) (ambientPiMeasure n lambda) := by
  let RB := catalystPoolFamilyBlock C R
  let SB := catalystPoolFamilyBlock C S
  have htuple := (ambientCoordinate_iIndep n lambda).indepFun_finset RB SB
    (catalystPoolFamilyBlock_disjoint C hRS) (fun _ => measurable_pi_apply _)
  have hleft : (fun ω => catalystPoolFamilyOpen ω C R) =
      (fun v : RB → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨r, hr, x, hx, hω⟩
      refine ⟨⟨(x, r), ?_⟩, hω⟩
      simp [RB, catalystPoolFamilyBlock, hx, hr]
    · rintro ⟨z, hω⟩
      have hz := Finset.mem_product.mp z.property
      exact ⟨z.1.2, hz.2, z.1.1, hz.1, hω⟩
  have hright : (fun ω => catalystPoolFamilyOpen ω C S) =
      (fun v : SB → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨r, hr, x, hx, hω⟩
      refine ⟨⟨(x, r), ?_⟩, hω⟩
      simp [SB, catalystPoolFamilyBlock, hx, hr]
    · rintro ⟨z, hω⟩
      have hz := Finset.mem_product.mp z.property
      exact ⟨z.1.2, hz.2, z.1.1, hz.1, hω⟩
  rw [hleft, hright]
  exact htuple.comp (measurable_of_finite _) (measurable_of_finite _)

/-- Consequently, a pairwise-disjoint collection of target reaction families
has pairwise-independent support indicators.  This is enough for a variance
bound and Chebyshev concentration; full mutual independence is unnecessary. -/
theorem pairwise_catalystPoolFamilyOpen_indep {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {ι : Type*}
    (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j)) :
    Pairwise fun i j =>
      IndepFun (fun ω => catalystPoolFamilyOpen ω C (R i))
        (fun ω => catalystPoolFamilyOpen ω C (R j))
        (ambientPiMeasure n lambda) := by
  intro i j hij
  exact catalystPoolFamilyOpen_indep lambda C (hR hij)

end HordijkSteelThreshold
