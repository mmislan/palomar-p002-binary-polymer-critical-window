module

public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped Topology ENNReal

/-- The effective-component estimate transferred to actual ordinary reversible
closure. The universe cardinality is the literal source molecule count. -/
theorem measure_temporaryClosure_deficit {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
      contourBudget a k/(1-contourBudget a k) +
      (Fintype.card (Molecule N) : ENNReal)*(contourBudget a k/(1-contourBudget a k))/d := by
  have hcard : Fintype.card (Molecule N) = (actualBinaryWords N).card := by
    rw [card_molecules_exact, actualBinaryWords_card]
  rw [hcard]
  calc
    _ ≤ staticReactionMeasure N a {ω | (rootedMolecularWords hL ω).card+d ≤
        (actualBinaryWords N).card} := by
      apply measure_mono
      intro ω hω
      have hh := rootedMolecularWords_card_le_closure hL ω
      exact Nat.le_trans (Nat.add_le_add_right hh d) hω
    _ ≤ _ := measure_rootedMolecularWords_deficit hL hk hfood hN a d hd

theorem contourBudget_tendsto_zero (a : I) (ha : 0 < (a : ℝ)) :
    Tendsto (contourBudget a) atTop (𝓝 0) := by
  have hp : 0 < (toNNReal a : ENNReal) := by exact_mod_cast ha
  have hq : 1-(toNNReal a : ENNReal)^2 < 1 :=
    ENNReal.sub_lt_self (by simp) (by simp) (pow_ne_zero _ (ne_of_gt hp))
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hm := ENNReal.Tendsto.const_mul (a := (molecularContourConstant : ENNReal)) ht
    (Or.inr (by simp))
  change Tendsto (fun k => (molecularContourConstant : ENNReal) *
    (1 - (toNNReal a : ENNReal) ^ 2) ^ k) atTop (𝓝 0)
  simpa only [mul_zero] using hm

theorem contourDeficit_tendsto_zero (a : I) (ha : 0 < (a : ℝ)) :
    Tendsto (fun k => contourBudget a k/(1-contourBudget a k)) atTop (𝓝 0) := by
  have ht := contourBudget_tendsto_zero a ha
  have hs : Tendsto (fun k => 1-contourBudget a k) atTop (𝓝 1) := by
    simpa only [tsub_zero] using ENNReal.Tendsto.sub tendsto_const_nhds ht
      (Or.inl (by simp : (1 : ENNReal) ≠ ∞))
  simpa only [div_one] using ENNReal.Tendsto.div ht
    (Or.inr (by simp : (1 : ENNReal) ≠ 0)) hs (Or.inl (by simp : (1 : ENNReal) ≠ ∞))

theorem exists_positive_contour_amplification (a : I) (ha : 0 < (a : ℝ))
    (η : ENNReal) (hη : 0 < η) :
    ∃ k : ℕ, 0 < k ∧ contourBudget a k/(1-contourBudget a k) < η := by
  have he : ∀ᶠ k in atTop, contourBudget a k/(1-contourBudget a k) < η :=
    (contourDeficit_tendsto_zero a ha).eventually (Iio_mem_nhds hη)
  obtain ⟨k, hk, he⟩ := ((eventually_ge_atTop 1).and he).exists
  exact ⟨k, hk, he⟩

/-- A fixed finite temporary food cutoff makes the literal static closure's
deficit arbitrarily small, uniformly in the ambient cap and integer deficit.
For d proportional to the universe size this is a uniform bulk bound. -/
theorem static_bulk_deficit_bound (a : I) (ha : 0 < (a : ℝ))
    (η : ENNReal) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ, 0 < N → ∀ d : ℕ, 0 < d →
      staticReactionMeasure N a {ω |
        (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
        η + (Fintype.card (Molecule N) : ENNReal)*η/d := by
  obtain ⟨k, hk, hδ⟩ := exists_positive_contour_amplification a ha η hη
  refine ⟨10*k, by omega, ?_⟩
  intro N hN d hd
  have hm := measure_temporaryClosure_deficit (w := 5*k) (k := k)
    (by omega : 2*(5*k) ≤ 10*k) (by omega) (by omega) hN a d hd
  refine hm.trans ?_
  gcongr

end HordijkSteelThreshold
