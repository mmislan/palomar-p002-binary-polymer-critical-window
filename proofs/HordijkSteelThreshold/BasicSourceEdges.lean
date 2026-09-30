module

public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.HordijkSteelThreshold.FoodWordParents

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

/-- The two basic graph edges retain their literal split-position IDs. -/
def basicFirstReaction {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨0, by unfold molLength at hx; omega⟩⟩

def basicLastReaction {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨x.1.val - 1, by unfold molLength at hx; omega⟩⟩

theorem basicFirstReaction_product {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) :
    reactionProduct (basicFirstReaction x hx) = x := rfl

theorem basicLastReaction_product {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) :
    reactionProduct (basicLastReaction x hx) = x := rfl

theorem basic_reactions_distinct {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) :
    basicFirstReaction x hx ≠ basicLastReaction x hx := by
  intro h
  have he := congrArg reactionLeftLength h
  simp only [basicFirstReaction, basicLastReaction, reactionLeftLength] at he
  unfold molLength at hx
  omega

theorem basicFirstReaction_tail {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) :
    moleculeWord (reactionRight (basicFirstReaction x hx)) = (moleculeWord x).tail := by
  rw [moleculeWord_reactionRight, basicFirstReaction_product]
  simp [basicFirstReaction, reactionLeftLength]

theorem basicLastReaction_dropLast {n : ℕ} (x : Molecule n) (hx : 3 ≤ molLength x) :
    moleculeWord (reactionLeft (basicLastReaction x hx)) = (moleculeWord x).dropLast := by
  rw [moleculeWord_reactionLeft, basicLastReaction_product]
  apply List.take_eq_dropLast
  rw [moleculeWord_length]
  change x.1.val - 1 + 1 + 1 = x.1.val + 1
  have hh : 3 ≤ x.1.val + 1 := hx
  omega

def contractFoodWord (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L then [] else s

theorem contractFoodWord_tail (L : ℕ) (s : List Bool) :
    contractFoodWord L s.tail = foodWordLeft L s := by
  have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
  simp only [contractFoodWord, foodWordLeft, List.length_tail, h]

theorem contractFoodWord_dropLast (L : ℕ) (s : List Bool) :
    contractFoodWord L s.dropLast = foodWordRight L s := by
  have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
  simp only [contractFoodWord, foodWordRight, List.length_dropLast, h]

/-- Actual source edges realize the commuting food-contracted word parents. -/
theorem basic_source_parent_pair {n : ℕ} (L : ℕ)
    (x : Molecule n) (hx : 3 ≤ molLength x) :
    contractFoodWord L (moleculeWord (reactionRight (basicFirstReaction x hx))) =
      foodWordLeft L (moleculeWord x) ∧
    contractFoodWord L (moleculeWord (reactionLeft (basicLastReaction x hx))) =
      foodWordRight L (moleculeWord x) := by
  rw [basicFirstReaction_tail, basicLastReaction_dropLast,
    contractFoodWord_tail, contractFoodWord_dropLast]
  exact ⟨rfl, rfl⟩

end HordijkSteelThreshold
