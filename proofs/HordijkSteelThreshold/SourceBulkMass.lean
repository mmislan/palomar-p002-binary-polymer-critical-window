module

public import proofs.HordijkSteelThreshold.HalfPoolAsymptotics
public import proofs.HordijkSteelThreshold.StaticUniformBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Uniform positive half-mass probability at every source peeling time.
The horizon may depend on n; literal RAF extraction remains a separate step. -/
theorem source_peeling_half_mass_positive {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ c : ENNReal, 0 < c ∧ ∀ᶠ n in atTop, ∀ T : ℕ,
      c ≤ ambientPiMeasure n lambda {ω |
        Fintype.card (Molecule n)/2 ≤
          (temporaryReactionClosure 2 (peelingActiveAt (catalystActive ω)
            (temporaryReactionClosure 2) T)).card} := by
  obtain ⟨a,ha,hfloor⟩ := halfPoolParameter_eventually_positive_floor hlambda
  obtain ⟨c,hc,hstatic⟩ := static_food_two_bulk_uniform a ha
  refine ⟨c,hc,?_⟩
  filter_upwards [hfloor, eventually_ge_atTop 1] with n hn hnpos
  intro T
  have hs := hstatic (fixedPoolParameter (catalysisP n lambda) (halfCatalystPool n).card)
    hn n (by omega)
  have hm : Monotone (@temporaryReactionClosure n 2) :=
    fun _ _ h => temporaryReactionClosure_mono h
  have ht := source_mass_ge_iid_static lambda (temporaryReactionClosure 2) hm
    (Fintype.card (Molecule n)/2) T
  exact hs.trans ht

end HordijkSteelThreshold
