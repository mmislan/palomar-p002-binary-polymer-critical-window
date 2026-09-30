module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold

open Filter Topology MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- A reaction is open relative to a specified prospective internal catalyst
pool.  Unlike ambient openness, this predicate retains the catalyst pool that
must eventually lie in the marked core. -/
def catalystPoolOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) : Prop :=
  ∃ x ∈ C, ω (x, r)

/-- Coordinate block queried by one reaction against a fixed catalyst pool. -/
def catalystPoolBlock {n : Nat} (C : Finset (Molecule n)) (r : Reaction n) :
    Finset (AmbientCoord n) :=
  C.product {r}

@[simp] theorem card_catalystPoolBlock {n : Nat}
    (C : Finset (Molecule n)) (r : Reaction n) :
    (catalystPoolBlock C r).card = C.card := by
  simp [catalystPoolBlock]

theorem catalystPoolBlock_disjoint {n : Nat} (C : Finset (Molecule n))
    {r s : Reaction n} (hrs : r ≠ s) :
    Disjoint (catalystPoolBlock C r) (catalystPoolBlock C s) := by
  rw [Finset.disjoint_left]
  intro z hzr hzs
  have hrmem : z.2 ∈ ({r} : Finset (Reaction n)) :=
    (Finset.mem_product.mp hzr).2
  have hsmem : z.2 ∈ ({s} : Finset (Reaction n)) :=
    (Finset.mem_product.mp hzs).2
  have hr : z.2 = r := Finset.mem_singleton.mp hrmem
  have hs : z.2 = s := Finset.mem_singleton.mp hsmem
  exact hrs (hr.symm.trans hs)

/-- For a fixed prospective internal catalyst pool, support indicators of
distinct reactions query disjoint Bernoulli coordinates and are independent. -/
theorem catalystPoolOpen_indep {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {r s : Reaction n} (hrs : r ≠ s) :
    IndepFun (fun ω => catalystPoolOpen ω C r)
      (fun ω => catalystPoolOpen ω C s) (ambientPiMeasure n lambda) := by
  let R := catalystPoolBlock C r
  let S := catalystPoolBlock C s
  have htuple := (ambientCoordinate_iIndep n lambda).indepFun_finset R S
    (catalystPoolBlock_disjoint C hrs) (fun _ => measurable_pi_apply _)
  have hleft : (fun ω => catalystPoolOpen ω C r) =
      (fun v : R → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨x, hx, hω⟩
      refine ⟨⟨(x, r), ?_⟩, hω⟩
      simp [R, catalystPoolBlock, hx]
    · rintro ⟨z, hω⟩
      have hz := Finset.mem_product.mp z.property
      have hr : z.1.2 = r := Finset.mem_singleton.mp hz.2
      have hzpair : z.1 = (z.1.1, r) := Prod.ext rfl hr
      exact ⟨z.1.1, hz.1, by rw [← hzpair]; exact hω⟩
  have hright : (fun ω => catalystPoolOpen ω C s) =
      (fun v : S → Prop => ∃ z, v z) ∘ (fun ω z => ω z) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨x, hx, hω⟩
      refine ⟨⟨(x, s), ?_⟩, hω⟩
      simp [S, catalystPoolBlock, hx]
    · rintro ⟨z, hω⟩
      have hz := Finset.mem_product.mp z.property
      have hs : z.1.2 = s := Finset.mem_singleton.mp hz.2
      have hzpair : z.1 = (z.1.1, s) := Prod.ext rfl hs
      exact ⟨z.1.1, hz.1, by rw [← hzpair]; exact hω⟩
  rw [hleft, hright]
  exact htuple.comp (measurable_of_finite _) (measurable_of_finite _)

/-- Exact closed-block probability expression for a fixed internal catalyst
pool. -/
noncomputable def catalystPoolClosedProbability {n : Nat}
    (C : Finset (Molecule n)) (lambda : ℝ) : ℝ :=
  (1 - (catalysisP n lambda : ℝ)) ^ C.card

noncomputable def catalystPoolOpenProbability {n : Nat}
    (C : Finset (Molecule n)) (lambda : ℝ) : ℝ :=
  1 - catalystPoolClosedProbability C lambda

/-- A prospective pool with limiting catalysis mass `a` gives the exact
Poisson-block limit `exp (-a)` for absence of an internal catalyst. -/
theorem catalystPoolClosedProbability_tendsto_exp
    (C : ∀ n, Finset (Molecule n)) {lambda a : ℝ} (hlambda : 0 < lambda)
    (hmass : Tendsto (fun n => (catalysisP n lambda : ℝ) * (C n).card)
      atTop (nhds a)) :
    Tendsto (fun n => catalystPoolClosedProbability (C n) lambda) atTop
      (nhds (Real.exp (-a))) := by
  have hratio := log_one_sub_catalysisP_div_tendsto hlambda
  have hmul := hmass.mul hratio
  have hlog : Tendsto
      (fun n => ((C n).card : ℝ) *
        Real.log (1 - (catalysisP n lambda : ℝ))) atTop (nhds (-a)) := by
    apply (show Tendsto
        (fun n => ((catalysisP n lambda : ℝ) * (C n).card) *
          (Real.log (1 - (catalysisP n lambda : ℝ)) /
            (catalysisP n lambda : ℝ))) atTop (nhds (-a)) by
      simpa only [mul_neg, mul_one] using hmul).congr'
    filter_upwards [catalysisP_eventually_ne_zero hlambda] with n hp
    field_simp
  have hexp := (Real.continuous_exp.tendsto (-a)).comp hlog
  apply hexp.congr'
  have hp_lt_one : ∀ᶠ n in atTop, (catalysisP n lambda : ℝ) < 1 :=
    (catalysisP_tendsto_zero hlambda).eventually_lt_const zero_lt_one
  filter_upwards [hp_lt_one] with n hp
  rw [catalystPoolClosedProbability]
  have hbase : 0 < 1 - (catalysisP n lambda : ℝ) := sub_pos.mpr hp
  rw [← Real.exp_log hbase, ← Real.exp_nat_mul]
  rfl

theorem catalystPoolOpenProbability_tendsto
    (C : ∀ n, Finset (Molecule n)) {lambda a : ℝ} (hlambda : 0 < lambda)
    (hmass : Tendsto (fun n => (catalysisP n lambda : ℝ) * (C n).card)
      atTop (nhds a)) :
    Tendsto (fun n => catalystPoolOpenProbability (C n) lambda) atTop
      (nhds (1 - Real.exp (-a))) := by
  exact tendsto_const_nhds.sub
    (catalystPoolClosedProbability_tendsto_exp C hlambda hmass)

end HordijkSteelThreshold
