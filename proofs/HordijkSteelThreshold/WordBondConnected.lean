module

public import proofs.HordijkSteelThreshold.WordDiamondCuts

@[expose] public section

namespace HordijkSteelThreshold
open Classical

/-- Two indexed edges share a finite diamond; loops are harmless for reachability. -/
def wordDiamondAdjacent {L N : ℕ} (e d : WordBasicEdge L N) : Prop :=
  ∃ v i j, wordDiamondSlot v i = e ∧ wordDiamondSlot v j = d

def wordContourReach {L N : ℕ} (C : Finset (WordBasicEdge L N)) :=
  Relation.EqvGen (fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent e d)

/-- A nonempty cut minimal among nonempty cuts is connected through diamonds.
This is the contour theorem used before counting connected edge sets. -/
theorem wordBond_diamond_connected {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e d : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (hd : d ∈ wordGraphCut f) :
    wordContourReach (wordGraphCut f) e d := by
  let F := (wordGraphCut f).filter (fun a => wordContourReach (wordGraphCut f) e a)
  have hsub : F ⊆ wordGraphCut f := Finset.filter_subset _ _
  have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, Relation.EqvGen.refl e⟩
  have hc : ∀ v i j, wordDiamondSlot v i ∈ F →
      wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F := by
    intro v i j hi hj
    obtain ⟨hiC, hiR⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hj, Relation.EqvGen.trans _ _ _ hiR ?_⟩
    exact Relation.EqvGen.rel _ _ ⟨hiC, hj, v, i, j, rfl, rfl⟩
  obtain ⟨g, hg⟩ := wordDiamond_closed_subset_cut f F hsub hc
  have hEq : F = wordGraphCut f := by
    rw [← hg]
    apply hmin g
    · rw [hg]
      exact ⟨e, heF⟩
    · rw [hg]
      exact hsub
  have hdF : d ∈ F := by rw [hEq]; exact hd
  exact (Finset.mem_filter.mp hdF).2

/-- Enabled disconnection in the finite word host yields a disabled,
diamond-connected separating contour. No contour premise is assumed. -/
theorem wordGraph_disabled_connected_contour (L N : ℕ)
    (active : Finset (WordBasicEdge L N)) (u v : BoundedFoodWord L N)
    (h : ¬ indexedEdgeReach active Prod.fst wordEdgeParent u v) :
    ∃ f : BoundedFoodWord L N → Bool, f u ≠ f v ∧
      wordGraphCut f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut f).Nonempty ∧
      ∀ e ∈ wordGraphCut f, ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d := by
  obtain ⟨f, hf, hs, hn, hm⟩ := wordGraph_disabled_bond L N active u v h
  refine ⟨f, hf, hs, hn, ?_⟩
  intro e he d hd
  exact wordBond_diamond_connected f hm e d he hd

end HordijkSteelThreshold
