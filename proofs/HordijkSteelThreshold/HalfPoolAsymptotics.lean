module

public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

theorem card_molecule_even (n : ℕ) : 2 ∣ Fintype.card (Molecule n) := by
  refine ⟨2^n-1, ?_⟩
  rw [card_molecules_exact, pow_succ]
  have hp : 0 < 2^n := by positivity
  omega

noncomputable def halfCatalystPool (n : ℕ) : Finset (Molecule n) :=
  finiteInitialSegment (Molecule n) (Fintype.card (Molecule n)/2)

@[simp] theorem halfCatalystPool_card (n : ℕ) :
    (halfCatalystPool n).card = Fintype.card (Molecule n)/2 :=
  card_finiteInitialSegment _ _ (Nat.div_le_self _ _)

theorem halfCatalystPool_mass_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (catalysisP n lambda : ℝ)*(halfCatalystPool n).card)
      atTop (𝓝 (lambda/2)) := by
  have ht := (catalysisP_mul_card_molecule_tendsto hlambda).div_const 2
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp only
    rw [halfCatalystPool_card, Nat.cast_div (card_molecule_even n) (by norm_num)]
    ring

theorem halfPoolParameter_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (fixedPoolParameter (catalysisP n lambda) (halfCatalystPool n).card : ℝ))
      atTop (𝓝 (1-Real.exp (-(lambda/2)))) := by
  simp_rw [fixedPoolParameter_coe]
  exact catalystPoolOpenProbability_tendsto halfCatalystPool hlambda
    (halfCatalystPool_mass_tendsto hlambda)

theorem halfPoolParameter_eventually_positive_floor {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ a : I, 0 < (a : ℝ) ∧ ∀ᶠ n in atTop,
      a ≤ fixedPoolParameter (catalysisP n lambda) (halfCatalystPool n).card := by
  have he : Real.exp (-(lambda/2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hep := Real.exp_pos (-(lambda/2))
  let a : I := ⟨(1-Real.exp (-(lambda/2)))/2, by constructor <;> linarith⟩
  have ha : 0 < (a : ℝ) := by dsimp [a]; linarith
  refine ⟨a, ha, ?_⟩
  have hlt : (a : ℝ) < 1-Real.exp (-(lambda/2)) := by dsimp [a]; linarith
  filter_upwards [(halfPoolParameter_tendsto hlambda).eventually_const_lt hlt] with n hn
  exact le_of_lt hn

end HordijkSteelThreshold
