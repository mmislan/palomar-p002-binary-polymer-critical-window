module

public import proofs.HordijkSteelThreshold.WordParentFibers

@[expose] public section

namespace HordijkSteelThreshold
open Classical

/-- The final index j represents a short factor of length j+1. -/
abbrev WordShortKey (L N w : ℕ) := WordBasicEdge L N × Fin w

/-- Owner (edge,j) uses its own upper short reaction and, when needed,
the parent's short reaction of length j. Food parents need no lower reaction. -/
noncomputable def wordDetourLower {L N w : ℕ} (d : WordShortKey L N w) :
    Option (WordShortKey L N w) :=
  if d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N then none
  else some ((wordEdgeParent d.1, d.1.2),
    ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)

noncomputable def wordDetourKeys {L N w : ℕ} (d : WordShortKey L N w) :
    Finset (WordShortKey L N w) := {d} ∪ (wordDetourLower d).toFinset

theorem wordDetourKeys_card {L N w : ℕ} (d : WordShortKey L N w) :
    (wordDetourKeys d).card ≤ 2 := by
  unfold wordDetourKeys
  have hc : (wordDetourLower d).toFinset.card ≤ 1 := by
    cases wordDetourLower d <;> simp
  exact (Finset.card_union_le _ _).trans (by simp only [Finset.card_singleton]; omega)

theorem wordDetourLower_details {L N w : ℕ} (d r : WordShortKey L N w)
    (h : wordDetourLower d = some r) :
    wordEdgeParent d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧
      d.2.val = r.2.val+1 ∧ r.1.1 ≠ boundedFoodRoot L N := by
  unfold wordDetourLower at h
  by_cases hz : d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N
  · rw [ite_eq_left hz] at h
    contradiction
  · rw [ite_eq_right hz] at h
    have he := Option.some.inj h
    have hp := congrArg (fun x : WordShortKey L N w => x.1.1) he
    have hs := congrArg (fun x : WordShortKey L N w => x.1.2) he
    have hj := congrArg (fun x : WordShortKey L N w => x.2.val) he
    dsimp at hp hs hj
    simp only [not_or] at hz
    exact ⟨hp, hs, by omega, by rw [← hp]; exact hz.2⟩

theorem wordParent_fixedSide_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (side : Bool) (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N =>
      wordEdgeParent (u,side) = v)).card ≤ 2 := by
  cases side
  · simpa only [wordEdgeParent, Bool.false_eq_true, ↓reduceIte] using
      boundedFoodLeft_fiber_card v hv
  · simpa only [wordEdgeParent, ↓reduceIte] using boundedFoodRight_fiber_card v hv

/-- A lower reaction has at most two owners: its product's two children on
its fixed side. The food root is excluded by the definition, not assumed small. -/
theorem wordDetourLower_fiber_card {L N w : ℕ} (r : WordShortKey L N w) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      wordDetourLower d = some r)).card ≤ 2 := by
  by_cases hr : r.1.1 = boundedFoodRoot L N
  · have he : (Finset.univ.filter (fun d : WordShortKey L N w =>
        wordDetourLower d = some r)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      exact (wordDetourLower_details d r (Finset.mem_filter.mp hd).2).2.2.2 hr
    rw [he]
    simp
  · let target := Finset.univ.filter (fun u : BoundedFoodWord L N =>
        wordEdgeParent (u,r.1.2) = r.1.1)
    have hc : (Finset.univ.filter (fun d : WordShortKey L N w =>
        wordDetourLower d = some r)).card ≤ target.card := by
      apply Finset.card_le_card_of_injOn (fun d : WordShortKey L N w => d.1.1)
      · intro d hd
        obtain ⟨hp, hs, _, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa only [← hs, Prod.mk.eta] using hp
      · intro d hd e he hde
        obtain ⟨_, hs, hj, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        obtain ⟨_, ht, hk, _⟩ := wordDetourLower_details e r (Finset.mem_filter.mp he).2
        apply Prod.ext
        · exact Prod.ext hde (hs.trans ht.symm)
        · apply Fin.ext
          omega
    exact hc.trans (wordParent_fixedSide_fiber_card r.1.1 r.1.2 hr)

/-- At most three detours use a normalized short reaction. This counts all
owners, even the unused root owners, and is uniform in cap and width. -/
theorem wordDetourKeys_incidence {L N w : ℕ} (r : WordShortKey L N w) :
    (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)).card ≤ 3 := by
  have hsub : (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)) ⊆
      {r} ∪ (Finset.univ.filter (fun d : WordShortKey L N w => wordDetourLower d = some r)) := by
    intro d hd
    have hm := (Finset.mem_filter.mp hd).2
    simp only [wordDetourKeys, Finset.mem_union, Finset.mem_singleton,
      Option.mem_toFinset] at hm
    rcases hm with hm | hm
    · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hm.symm)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
  calc
    _ ≤ ({r} ∪ (Finset.univ.filter (fun d : WordShortKey L N w =>
      wordDetourLower d = some r))).card := Finset.card_le_card hsub
    _ ≤ 1 + (Finset.univ.filter (fun d : WordShortKey L N w =>
      wordDetourLower d = some r)).card := by simpa using Finset.card_union_le {r} _
    _ ≤ 3 := by have h := wordDetourLower_fiber_card r; omega

end HordijkSteelThreshold
