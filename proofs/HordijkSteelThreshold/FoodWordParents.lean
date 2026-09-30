module

public import proofs.HordijkSteelThreshold.DiamondCutPotential

@[expose] public section

namespace HordijkSteelThreshold

/-- Empty list represents the contracted food root. Nonfood parents remove
one end bit; a parent reaching the food cutoff is sent to that root. -/
def foodWordLeft (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.tail

def foodWordRight (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.dropLast

def foodWordHeight (L : ℕ) (s : List Bool) : ℕ := s.length - L

theorem foodWordParents_commute (L : ℕ) (s : List Bool) :
    foodWordLeft L (foodWordRight L s) = foodWordRight L (foodWordLeft L s) := by
  by_cases h : s.length ≤ L + 1
  · simp [foodWordLeft, foodWordRight, h]
  · simp only [foodWordLeft, foodWordRight, ite_eq_right h, List.length_dropLast,
      List.length_tail]
    split_ifs <;> simp [List.tail_dropLast]

theorem foodWordRight_height (L : ℕ) (s : List Bool) :
    foodWordHeight L (foodWordRight L s) ≤ foodWordHeight L s - 1 := by
  simp only [foodWordHeight, foodWordRight]
  split_ifs <;> simp only [List.length_nil, List.length_dropLast] <;> omega

theorem foodWordLeft_height (L : ℕ) (s : List Bool) :
    foodWordHeight L (foodWordLeft L s) ≤ foodWordHeight L s - 1 := by
  simp only [foodWordHeight, foodWordLeft]
  split_ifs <;> simp only [List.length_nil, List.length_tail] <;> omega

/-- The compiled potential theorem now applies to actual binary end-word
operations. Literal Fin-coded reaction identification is a separate adapter. -/
theorem foodWord_diamond_cut (L N : ℕ)
    (leftEdge rightEdge : List Bool → Bool)
    (hfood : ∀ s, s.length ≤ L → leftEdge s = false ∧ rightEdge s = false)
    (hdiamond : ∀ s,
      (((leftEdge s ^^ rightEdge s) ^^ leftEdge (foodWordRight L s)) ^^
        rightEdge (foodWordLeft L s)) = false)
    (s : List Bool) (hs : s.length ≤ N) :
    ((diamondPotential (foodWordRight L) rightEdge N s ^^
      diamondPotential (foodWordRight L) rightEdge N (foodWordLeft L s)) = leftEdge s) ∧
    ((diamondPotential (foodWordRight L) rightEdge N s ^^
      diamondPotential (foodWordRight L) rightEdge N (foodWordRight L s)) = rightEdge s) := by
  apply diamondPotential_edges (foodWordLeft L) (foodWordRight L) (foodWordHeight L)
    leftEdge rightEdge (foodWordRight_height L) (foodWordParents_commute L)
  · intro v hv
    exact hfood v (by unfold foodWordHeight at hv; omega)
  · exact hdiamond
  · unfold foodWordHeight
    omega

end HordijkSteelThreshold
