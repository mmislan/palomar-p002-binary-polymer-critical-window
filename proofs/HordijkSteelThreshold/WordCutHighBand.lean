module

public import proofs.HordijkSteelThreshold.WordHighBand

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def boundedWordLabel {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) : Bool :=
  if hs : s = [] ∨ (L < s.length ∧ s.length ≤ N) then f ⟨s, hs⟩
  else f (boundedFoodRoot L N)

theorem boundedWordLabel_eq {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (u : BoundedFoodWord L N) : boundedWordLabel f u.val = f u := by
  unfold boundedWordLabel; exact dite_eq_left u.property

/-- Above every boundary product, both literal parents preserve the cut label. -/
theorem wordCut_above_boundary_parents {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    boundedWordLabel f s = boundedWordLabel f s.tail ∧
    boundedWordLabel f s = boundedWordLabel f s.dropLast := by
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨by omega, hN⟩⟩
  have hn : u ≠ boundedFoodRoot L N := by
    intro h
    have hh := congrArg (fun v : BoundedFoodWord L N => v.val.length) h
    change s.length = 0 at hh
    omega
  have heq (b : Bool) : f u = f (wordEdgeParent (u, b)) := by
    by_contra h
    have hm : (u, b) ∈ wordGraphCut f := by
      simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, hn, h]
    have hh := hcut (u, b) hm
    change s.length ≤ M at hh
    omega
  have hlong : ¬ s.length ≤ L + 1 := by omega
  constructor
  · calc
      boundedWordLabel f s = f u := boundedWordLabel_eq f u
      _ = f (boundedFoodLeft u) := heq false
      _ = boundedWordLabel f s.tail := by
        rw [← boundedWordLabel_eq f (boundedFoodLeft u)]
        change boundedWordLabel f (foodWordLeft L s) = _
        simp [foodWordLeft, hlong]
  · calc
      boundedWordLabel f s = f u := boundedWordLabel_eq f u
      _ = f (boundedFoodRight u) := heq true
      _ = boundedWordLabel f s.dropLast := by
        rw [← boundedWordLabel_eq f (boundedFoodRight u)]
        change boundedWordLabel f (foodWordRight L s) = _
        simp [foodWordRight, hlong]

/-- All source vertices in the high band have the same cut label. -/
theorem wordCut_high_band_constant {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hMN : M < N)
    (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (u v : BoundedFoodWord L N) (hu : M ≤ u.val.length) (hv : M ≤ v.val.length) :
    f u = f v := by
  have h := highBand_label_constant (boundedWordLabel f) M N hMN
    (wordCut_above_boundary_parents f hLM hcut) u.val v.val
    ⟨hu, boundedFoodWord_length_le u⟩ ⟨hv, boundedFoodWord_length_le v⟩
  simpa only [boundedWordLabel_eq] using h

/-- One core-avoiding high-band vertex places the entire high band on the food side. -/
theorem wordCut_high_band_food {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hMN : M < N)
    (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool)
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N) (hv : M ≤ v.val.length)
    (havoid : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : M ≤ u.val.length) :
    f u = f (boundedFoodRoot L N) :=
  (wordCut_high_band_constant f hLM hMN hcut u v hu hv).trans
    (wordCut_core_avoiding_root f core hcore v havoid)

/-- A constant word opposite to the first core bit avoids every nonempty core. -/
theorem exists_core_avoiding_word {L N M : ℕ} (hLM : L < M) (hMN : M ≤ N)
    (core : List Bool) (hne : core ≠ []) :
    ∃ v : BoundedFoodWord L N, v.val.length = M ∧
      ¬ ∃ l r : List Bool, v.val = l ++ core ++ r := by
  cases core with
  | nil => exact (hne rfl).elim
  | cons a t =>
    let v : BoundedFoodWord L N := ⟨List.replicate M (!a), Or.inr (by simpa using And.intro hLM hMN)⟩
    refine ⟨v, by simp [v], ?_⟩
    rintro ⟨l, r, he⟩
    have hm : a ∈ v.val := by rw [he]; simp
    change a ∈ List.replicate M (!a) at hm
    cases a <;> simp at hm

/-- A nonfood-side word cannot be longer than all boundary products when they share a core. -/
theorem wordCut_nonfood_length_le {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : f u ≠ f (boundedFoodRoot L N)) :
    u.val.length ≤ M := by
  by_contra h
  have hN := boundedFoodWord_length_le u
  have hMN : M < N := by omega
  obtain ⟨v, hv, ha⟩ := exists_core_avoiding_word hLM hMN.le core hne
  exact hu (wordCut_high_band_food f hLM hMN hcut core hcore v (by omega) ha u (by omega))

end HordijkSteelThreshold
