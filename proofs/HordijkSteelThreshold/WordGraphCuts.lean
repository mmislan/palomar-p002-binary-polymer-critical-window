module

public import proofs.HordijkSteelThreshold.BoundedFoodWords
public import proofs.HordijkSteelThreshold.FiniteBondSeparation

@[expose] public section

namespace HordijkSteelThreshold

open Classical

abbrev WordBasicEdge (L N : ℕ) := BoundedFoodWord L N × Bool

noncomputable def wordBasicEdges (L N : ℕ) : Finset (WordBasicEdge L N) := by
  classical
  exact Finset.univ.filter (fun e => e.1 ≠ boundedFoodRoot L N)

def wordEdgeParent {L N : ℕ} (e : WordBasicEdge L N) : BoundedFoodWord L N :=
  if e.2 then boundedFoodRight e.1 else boundedFoodLeft e.1

theorem wordGraph_reaches_root (L N : ℕ) (v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent v (boundedFoodRoot L N) := by
  classical
  suffices ∀ k (u : BoundedFoodWord L N), foodWordHeight L u.val ≤ k →
      indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u (boundedFoodRoot L N) by
    exact this N v (by have h := boundedFoodWord_length_le v; unfold foodWordHeight; omega)
  intro k
  induction k with
  | zero =>
    intro u hu
    rw [boundedFood_zero_height u (by omega)]
    exact Relation.EqvGen.refl _
  | succ k ih =>
    intro u hu
    by_cases hr : u = boundedFoodRoot L N
    · rw [hr]
      exact Relation.EqvGen.refl _
    · have he : (u, true) ∈ wordBasicEdges L N := by simp [wordBasicEdges, hr]
      have hs : indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u
          (boundedFoodRight u) := Relation.EqvGen.rel _ _ ⟨(u, true), he, rfl, rfl⟩
      have hp : foodWordHeight L (boundedFoodRight u).val ≤ k := by
        have hh := foodWordRight_height L u.val
        change foodWordHeight L (foodWordRight L u.val) ≤ k
        omega
      exact Relation.EqvGen.trans _ _ _ hs (ih _ hp)

theorem wordGraph_connected (L N : ℕ) (u v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u v :=
  Relation.EqvGen.trans _ _ _ (wordGraph_reaches_root L N u)
    (Relation.EqvGen.symm _ _ (wordGraph_reaches_root L N v))

noncomputable def wordGraphCut {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    Finset (WordBasicEdge L N) := booleanEdgeCut (wordBasicEdges L N) Prod.fst wordEdgeParent f

/-- Source-domain host connectivity discharges the premise of the general
disabled-bond theorem. Only enabled disconnection remains as a hypothesis. -/
theorem wordGraph_disabled_bond (L N : ℕ) (active : Finset (WordBasicEdge L N))
    (u v : BoundedFoodWord L N)
    (h : ¬ indexedEdgeReach active Prod.fst wordEdgeParent u v) :
    ∃ f : BoundedFoodWord L N → Bool, f u ≠ f v ∧
      wordGraphCut f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut f).Nonempty ∧
      ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
        wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f := by
  classical
  exact exists_disabled_separating_bond (wordBasicEdges L N) active Prod.fst wordEdgeParent
    u v (wordGraph_connected L N u v) h

end HordijkSteelThreshold
