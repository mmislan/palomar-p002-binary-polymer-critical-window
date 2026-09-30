module

public import proofs.HordijkSteelThreshold.HalfPoolAsymptotics

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le (n m : ℕ) : nearFullPoolSize n m ≤ Fintype.card (Molecule n) := by
  have h1 := Nat.mul_le_mul_right (Fintype.card (Molecule n)/m) (Nat.sub_le m 1)
  have h2 := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
  dsimp [nearFullPoolSize]
  nlinarith

noncomputable def nearFullCatalystPool (n m : ℕ) : Finset (Molecule n) :=
  finiteInitialSegment (Molecule n) (nearFullPoolSize n m)

@[simp] theorem nearFullCatalystPool_card (n m : ℕ) :
    (nearFullCatalystPool n m).card = nearFullPoolSize n m :=
  card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)

theorem nearFullPool_mass_tendsto {lambda : ℝ} (hlambda : 0 < lambda)
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => (catalysisP n lambda : ℝ)*(nearFullCatalystPool n m).card)
      atTop (𝓝 (lambda*(1-1/(m : ℝ)))) := by
  have hrem : Tendsto (fun n => (catalysisP n lambda : ℝ)*
      ((Fintype.card (Molecule n)%m : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n => (catalysisP n lambda : ℝ)*(m : ℝ))
    · intro n
      exact mul_nonneg (catalysisP n lambda).property.1 (Nat.cast_nonneg _)
    · intro n
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt (Fintype.card (Molecule n)) hm).le)
        (catalysisP n lambda).property.1
    · simpa using (catalysisP_tendsto_zero hlambda).mul_const (m : ℝ)
  have ht := (((catalysisP_mul_card_molecule_tendsto hlambda).sub hrem).div_const (m : ℝ)).mul_const
    ((m-1 : ℕ) : ℝ)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have he : ((lambda-0)/(m : ℝ))*((m-1 : ℕ) : ℝ) = lambda*(1-1/(m : ℝ)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
    ring
  rw [he] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hdiv : ((Fintype.card (Molecule n)/m : ℕ) : ℝ)*(m : ℝ) +
      (Fintype.card (Molecule n)%m : ℕ) = (Fintype.card (Molecule n) : ℝ) := by
    exact_mod_cast (show (Fintype.card (Molecule n)/m)*m + Fintype.card (Molecule n)%m =
      Fintype.card (Molecule n) from by simpa [Nat.mul_comm] using Nat.div_add_mod (Fintype.card (Molecule n)) m)
  simp only [nearFullCatalystPool_card, nearFullPoolSize, Nat.cast_mul]
  rw [← hdiv]
  field_simp
  ring

theorem nearFullPoolParameter_tendsto {lambda : ℝ} (hlambda : 0 < lambda)
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => (fixedPoolParameter (catalysisP n lambda)
      (nearFullCatalystPool n m).card : ℝ)) atTop
      (𝓝 (1-Real.exp (-(lambda*(1-1/(m : ℝ)))))) := by
  simp_rw [fixedPoolParameter_coe]
  exact catalystPoolOpenProbability_tendsto (fun n => nearFullCatalystPool n m)
    hlambda (nearFullPool_mass_tendsto hlambda m hm)

theorem nearFullPoolSize_eventually_nonfood (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ n in atTop, 6 < nearFullPoolSize n m := by
  filter_upwards [card_molecule_tendsto_atTop.eventually (eventually_ge_atTop (8*m))] with n hn
  have hd : 8 ≤ Fintype.card (Molecule n)/m := (Nat.le_div_iff_mul_le (by omega)).mpr hn
  dsimp [nearFullPoolSize]
  have hm1 : 1 ≤ m-1 := by omega
  nlinarith

end HordijkSteelThreshold
