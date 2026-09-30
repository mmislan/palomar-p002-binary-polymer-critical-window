module

public import proofs.HordijkSteelThreshold.WordCoreCount
public import proofs.HordijkSteelThreshold.WordCutHighBand

@[expose] public section

namespace HordijkSteelThreshold

noncomputable def wordNonfoodSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) :=
  Finset.univ.filter (fun u => f u ≠ f (boundedFoodRoot L N))

/-- Count actual nonfood-side molecules, not the weight-one contracted food vertex. -/
theorem wordNonfoodSide_card_lt {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (k : ℕ) (hM : M ≤ core.length + k) :
    (wordNonfoodSide f).card < 2 ^ (2 * (k + 1)) := by
  let S := (wordNonfoodSide f).image Subtype.val
  have hS : S.card = (wordNonfoodSide f).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [← hS]
  apply core_containing_words_card_lt S core k
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact wordCut_nonfood_side_contains_core f core hcore u (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N)) (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact (wordCut_nonfood_length_le f hLM hcut core hne hcore u
      (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N)) (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2).trans hM

/-- If the food-containing side is the smaller molecular side, a small core envelope
forces the ambient cap itself to be small. Total molecular mass is 2^(N+1)-2. -/
theorem wordFoodSide_minor_cap_bound {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (k : ℕ) (hM : M ≤ core.length + k)
    (hminor : (2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) :
    N ≤ 2 * (k + 1) := by
  have hc := wordNonfoodSide_card_lt f hLM hcut core hne hcore k hM
  have hp : 0 < (2 : ℕ) ^ N := by positivity
  have hb : (2 : ℕ) ^ N ≤ 2 ^ (2 * (k + 1)) := by
    rw [pow_succ] at hminor
    omega
  exact (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hb

end HordijkSteelThreshold
