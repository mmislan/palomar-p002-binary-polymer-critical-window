module

public import proofs.HordijkSteelThreshold.StaticFoodTwoBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem contourBudget_antitone_parameter (a b : I) (hab : a ≤ b) (k : ℕ) :
    contourBudget b k ≤ contourBudget a k := by
  have hh : (toNNReal a : ENNReal) ≤ toNNReal b := by exact_mod_cast hab
  unfold contourBudget
  gcongr

/-- A single lower openness determines the seed and positive constant for
every larger openness. This is the uniform version needed by changing n. -/
theorem static_food_two_bulk_uniform (a : I) (ha : 0 < (a : ℝ)) :
    ∃ c : ENNReal, 0 < c ∧ ∀ b : I, a ≤ b → ∀ N : ℕ, 0 < N →
      c ≤ staticReactionMeasure N b {ω |
        Fintype.card (Molecule N)/2 ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card} := by
  obtain ⟨k,hk,hδ⟩ := exists_positive_contour_amplification a ha (6 : ENNReal)⁻¹ (by norm_num)
  let L := 10*k
  let c : ENNReal := (toNNReal a : ENNReal)^(Fintype.card (Reaction L)) * (2 : ENNReal)⁻¹
  have hpa : (toNNReal a : ENNReal) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  refine ⟨c, pos_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hpa) (by simp)), ?_⟩
  intro b hab N hN
  have hbudget := contourBudget_antitone_parameter a b hab k
  have hδb : contourBudget b k/(1-contourBudget b k) ≤ (6 : ENNReal)⁻¹ := by
    apply le_trans (b := contourBudget a k/(1-contourBudget a k))
    · gcongr
    · exact hδ.le
  let U := Fintype.card (Molecule N)
  let d := U/2+1
  have hd : 0 < d := Nat.succ_pos _
  have hUd : U ≤ 2*d := by dsimp [d]; omega
  have hcast : (U : ENNReal) ≤ 2*d := by exact_mod_cast hUd
  have hratio : (U : ENNReal)*(6 : ENNReal)⁻¹/d ≤ 2*(6 : ENNReal)⁻¹ := by
    calc
      _ ≤ (2*d)*(6 : ENNReal)⁻¹/d := by gcongr
      _ = _ := by rw [mul_right_comm, ENNReal.mul_div_cancel_right
        (by exact_mod_cast Nat.ne_of_gt hd) (by simp)]
  have hbad : staticReactionMeasure N b {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card < U/2} ≤ (2 : ENNReal)⁻¹ := by
    calc
      _ ≤ staticReactionMeasure N b {ω |
          (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := by
        apply measure_mono
        intro ω hω
        change (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U
        dsimp [d]
        change (temporaryReactionClosure L (staticOpenReactions ω)).card < U/2 at hω
        omega
      _ ≤ contourBudget b k/(1-contourBudget b k) +
          (U : ENNReal)*(contourBudget b k/(1-contourBudget b k))/d :=
        measure_temporaryClosure_deficit (w := 5*k) (k := k)
          (by dsimp [L]; omega) (by omega) (by dsimp [L]; omega) hN b d hd
      _ ≤ (6 : ENNReal)⁻¹+(U : ENNReal)*(6 : ENNReal)⁻¹/d := by gcongr
      _ ≤ (6 : ENNReal)⁻¹+2*(6 : ENNReal)⁻¹ := add_le_add le_rfl hratio
      _ = _ := by
        have hf : (2 : ENNReal)*6⁻¹ ≠ ∞ := by simp [ENNReal.mul_eq_top]
        apply (ENNReal.toReal_eq_toReal_iff' (by simp [hf]) (by simp)).mp
        rw [ENNReal.toReal_add (by simp) hf]
        norm_num
  have hgood : (2 : ENNReal)⁻¹ ≤ staticReactionMeasure N b {ω |
      U/2 ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card} := by
    have he : {ω : Reaction N → Prop | U/2 ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card} =
        {ω | (temporaryReactionClosure L (staticOpenReactions ω)).card < U/2}ᶜ := by ext ω; simp
    rw [he, measure_compl (Set.Finite.measurableSet (Set.toFinite _))
      (measure_ne_top _ _), measure_univ]
    calc
      _ = 1-(2 : ENNReal)⁻¹ := by norm_num
      _ ≤ _ := tsub_le_tsub_left hbad 1
  have hab' : (toNNReal a : ENNReal) ≤ toNNReal b := by exact_mod_cast hab
  have hb1 : (toNNReal b : ENNReal) ≤ 1 := by exact_mod_cast b.property.2
  have hcost : (toNNReal a : ENNReal)^(Fintype.card (Reaction L)) ≤
      (toNNReal b : ENNReal)^(lowProductBridge N L).card := by
    calc
      _ ≤ (toNNReal b : ENNReal)^(Fintype.card (Reaction L)) := by gcongr
      _ ≤ _ := pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal b : ENNReal)) hb1
        (lowProductBridge_card_le N L)
  exact (mul_le_mul' hcost hgood).trans (static_food_two_mass_lower N L (U/2) b)

end HordijkSteelThreshold
