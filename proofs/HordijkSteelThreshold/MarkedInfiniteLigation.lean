module

public import proofs.HordijkSteelThreshold.InfiniteLigation

@[expose] public section

namespace HordijkSteelThreshold

/-- `marks x w k` means that molecule `x` catalyzes the split-position
ligation producing `w` at split `k`. -/
abbrev InfiniteCatalysisMarks := List Bool → List Bool → Nat → Prop

/-- A self-consistent marked ligation language. Food is present, and every
nonfood word has a legal split whose factors and at least one catalyst all lie
in the same language. Factor lengths strictly decrease, so food generation is
retained, while catalyst witnesses may participate in cycles as RAFs allow. -/
def IsMarkedLigationLanguage (foodLength : Nat) (marks : InfiniteCatalysisMarks)
    (C : Set (List Bool)) : Prop :=
  (∀ w, w ≠ [] → w.length ≤ foodLength → w ∈ C) ∧
  ∀ w ∈ C, foodLength < w.length →
    ∃ k, 0 < k ∧ k < w.length ∧
      w.take k ∈ C ∧ w.drop k ∈ C ∧ ∃ x ∈ C, marks x w k

/-- The food-only language is always a marked language. -/
def markedFoodLanguage (foodLength : Nat) : Set (List Bool) :=
  {w | w ≠ [] ∧ w.length ≤ foodLength}

theorem markedFoodLanguage_isMarked (foodLength : Nat)
    (marks : InfiniteCatalysisMarks) :
    IsMarkedLigationLanguage foodLength marks (markedFoodLanguage foodLength) := by
  constructor
  · intro w hne hlen
    exact ⟨hne, hlen⟩
  · intro w hw hnonfood
    exact (Nat.not_lt_of_ge hw.2 hnonfood).elim

/-- The union of all self-consistent marked languages. This is the exact
greatest fixed-point state replacing the lossy ambient-open closure. -/
def maximalMarkedLanguage (foodLength : Nat) (marks : InfiniteCatalysisMarks) :
    Set (List Bool) :=
  {w | ∃ C, IsMarkedLigationLanguage foodLength marks C ∧ w ∈ C}

theorem isMarked_subset_maximal {foodLength : Nat} {marks : InfiniteCatalysisMarks}
    {C : Set (List Bool)} (hC : IsMarkedLigationLanguage foodLength marks C) :
    C ⊆ maximalMarkedLanguage foodLength marks := by
  intro w hw
  exact ⟨C, hC, hw⟩

theorem maximalMarkedLanguage_isMarked (foodLength : Nat)
    (marks : InfiniteCatalysisMarks) :
    IsMarkedLigationLanguage foodLength marks
      (maximalMarkedLanguage foodLength marks) := by
  constructor
  · intro w hne hlen
    exact ⟨markedFoodLanguage foodLength,
      markedFoodLanguage_isMarked foodLength marks, ⟨hne, hlen⟩⟩
  · intro w hw hnonfood
    obtain ⟨C, hC, hwC⟩ := hw
    obtain ⟨k, hk0, hkw, htake, hdrop, x, hxC, hmark⟩ :=
      hC.2 w hwC hnonfood
    exact ⟨k, hk0, hkw,
      ⟨C, hC, htake⟩,
      ⟨C, hC, hdrop⟩,
      x, ⟨C, hC, hxC⟩, hmark⟩

theorem maximalMarkedLanguage_greatest {foodLength : Nat}
    {marks : InfiniteCatalysisMarks} {C : Set (List Bool)}
    (hC : IsMarkedLigationLanguage foodLength marks C) :
    C ⊆ maximalMarkedLanguage foodLength marks :=
  isMarked_subset_maximal hC

end HordijkSteelThreshold
