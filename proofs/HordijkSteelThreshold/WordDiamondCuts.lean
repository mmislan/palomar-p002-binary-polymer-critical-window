module

public import proofs.HordijkSteelThreshold.WordGraphCuts
public import proofs.HordijkSteelThreshold.LocalParityTransfer

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def wordDiamondSlot {L N : ℕ} (v : BoundedFoodWord L N) : Fin 4 → WordBasicEdge L N :=
  ![(v, false), (v, true), (boundedFoodRight v, false), (boundedFoodLeft v, true)]

noncomputable def wordEdgeIndicator {L N : ℕ} (F : Finset (WordBasicEdge L N))
    (e : WordBasicEdge L N) : Bool := decide (e ∈ F)

theorem wordParents_root (L N : ℕ) :
    boundedFoodLeft (boundedFoodRoot L N) = boundedFoodRoot L N ∧
    boundedFoodRight (boundedFoodRoot L N) = boundedFoodRoot L N := by
  constructor <;> apply Subtype.ext <;>
    simp [boundedFoodLeft, boundedFoodRight, boundedFoodRoot, foodWordLeft, foodWordRight]

theorem wordCut_indicator {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) :
    wordEdgeIndicator (wordGraphCut f) e = (f e.1 ^^ f (wordEdgeParent e)) := by
  by_cases hr : e.1 = boundedFoodRoot L N
  · have hp : wordEdgeParent e = e.1 := by
      unfold wordEdgeParent
      rw [hr]
      split
      · exact (wordParents_root L N).2
      · exact (wordParents_root L N).1
    simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, hp]
  · cases ha : f e.1 <;> cases hb : f (wordEdgeParent e) <;>
      simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, ha, hb]

theorem wordCut_diamond_parity {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (v : BoundedFoodWord L N) :
    quadParity (fun i => wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v i)) = false := by
  simp only [quadParity, wordCut_indicator, wordDiamondSlot, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, wordEdgeParent,
    Bool.false_eq_true, ite_false, ite_true]
  rw [boundedFoodParents_commute]
  cases f v <;> cases f (boundedFoodLeft v) <;> cases f (boundedFoodRight v) <;>
    cases f (boundedFoodRight (boundedFoodLeft v)) <;> rfl

/-- An edge subset with even parity in each finite diamond is an actual cut. -/
theorem wordDiamond_integrate {L N : ℕ} (F : Finset (WordBasicEdge L N))
    (hsub : F ⊆ wordBasicEdges L N)
    (hpar : ∀ v, quadParity (fun i => wordEdgeIndicator F (wordDiamondSlot v i)) = false) :
    ∃ f : BoundedFoodWord L N → Bool, wordGraphCut f = F := by
  let le := fun v => wordEdgeIndicator F (v, false)
  let re := fun v => wordEdgeIndicator F (v, true)
  have hr : le (boundedFoodRoot L N) = false ∧ re (boundedFoodRoot L N) = false := by
    have hn (b : Bool) : (boundedFoodRoot L N, b) ∉ F := by
      intro h
      have := hsub h
      simp [wordBasicEdges] at this
    simp [le, re, wordEdgeIndicator, hn]
  have hd : ∀ v, (((le v ^^ re v) ^^ le (boundedFoodRight v)) ^^
      re (boundedFoodLeft v)) = false := by
    intro v
    exact hpar v
  let f := diamondPotential boundedFoodRight re N
  refine ⟨f, ?_⟩
  ext e
  have hp := boundedFood_diamond_cut L N le re hr hd e.1
  have he : (f e.1 ^^ f (wordEdgeParent e)) = wordEdgeIndicator F e := by
    rcases e with ⟨v, b⟩
    cases b
    · exact hp.1
    · exact hp.2
  have hi := wordCut_indicator f e
  rw [he] at hi
  constructor
  · intro h
    have ht : wordEdgeIndicator (wordGraphCut f) e = true := decide_eq_true h
    rw [hi] at ht
    exact of_decide_eq_true ht
  · intro h
    have ht : wordEdgeIndicator F e = true := decide_eq_true h
    rw [← hi] at ht
    exact of_decide_eq_true ht

/-- Sharing a diamond transfers ambient cut parity, hence a closed subset
of a word cut is itself a word cut. -/
theorem wordDiamond_closed_subset_cut {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (F : Finset (WordBasicEdge L N)) (hsub : F ⊆ wordGraphCut f)
    (hclosed : ∀ v i j, wordDiamondSlot v i ∈ F →
      wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F) :
    ∃ g : BoundedFoodWord L N → Bool, wordGraphCut g = F := by
  apply wordDiamond_integrate F
  · exact hsub.trans (Finset.filter_subset _ _)
  · intro v
    apply quadParity_closed_subset _ (fun i => wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v i))
    · intro i hi
      exact decide_eq_true (hsub (of_decide_eq_true hi))
    · intro i j hi hj
      exact decide_eq_true (hclosed v i j (of_decide_eq_true hi) (of_decide_eq_true hj))
    · exact wordCut_diamond_parity f v

end HordijkSteelThreshold
