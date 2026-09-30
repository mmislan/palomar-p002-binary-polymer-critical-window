module

public import proofs.HordijkSteelThreshold.FoodWordParents
public import proofs.HordijkSteelThreshold.BinaryWordCode

@[expose] public section

namespace HordijkSteelThreshold

/-- The actual finite word-graph vertex domain: one food root and only
nonfood words inside the ambient cap. No parity condition above N is needed. -/
def BoundedFoodWord (L N : ℕ) :=
  {s : List Bool // s = [] ∨ (L < s.length ∧ s.length ≤ N)}

theorem boundedFoodWord_length_le {L N : ℕ} (v : BoundedFoodWord L N) :
    v.val.length ≤ N := by
  rcases v.property with h | h
  · simp [h]
  · exact h.2

instance boundedFoodWord_finite (L N : ℕ) : Finite (BoundedFoodWord L N) := by
  let encode : BoundedFoodWord L N → (Σ m : Fin (N + 1), RAF.Polymer.Word m.val) :=
    fun v => ⟨⟨v.val.length, Nat.lt_succ_of_le (boundedFoodWord_length_le v)⟩, listWord v.val⟩
  apply Finite.of_injective encode
  intro u v h
  apply Subtype.ext
  apply binaryWordCode_injective_length
  · exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

noncomputable instance boundedFoodWord_fintype (L N : ℕ) : Fintype (BoundedFoodWord L N) :=
  Fintype.ofFinite _

def boundedFoodRoot (L N : ℕ) : BoundedFoodWord L N := ⟨[], Or.inl rfl⟩

def boundedFoodLeft {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordLeft L v.val, by
    by_cases h : v.val.length ≤ L + 1
    · left
      simp [foodWordLeft, h]
    · right
      have hv := boundedFoodWord_length_le v
      simp only [foodWordLeft, ite_eq_right h, List.length_tail]
      omega⟩

def boundedFoodRight {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordRight L v.val, by
    by_cases h : v.val.length ≤ L + 1
    · left
      simp [foodWordRight, h]
    · right
      have hv := boundedFoodWord_length_le v
      simp only [foodWordRight, ite_eq_right h, List.length_dropLast]
      omega⟩

theorem boundedFoodParents_commute {L N : ℕ} (v : BoundedFoodWord L N) :
    boundedFoodLeft (boundedFoodRight v) = boundedFoodRight (boundedFoodLeft v) := by
  apply Subtype.ext
  exact foodWordParents_commute L v.val

theorem boundedFood_zero_height {L N : ℕ} (v : BoundedFoodWord L N)
    (h : foodWordHeight L v.val = 0) : v = boundedFoodRoot L N := by
  apply Subtype.ext
  rcases v.property with hv | hv
  · exact hv
  · unfold foodWordHeight at h
    omega

/-- Diamond parity only on the finite source domain suffices to integrate
edge labels. This avoids the false zero-extension premise above the cap. -/
theorem boundedFood_diamond_cut (L N : ℕ)
    (leftEdge rightEdge : BoundedFoodWord L N → Bool)
    (hroot : leftEdge (boundedFoodRoot L N) = false ∧
      rightEdge (boundedFoodRoot L N) = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (boundedFoodRight v)) ^^
      rightEdge (boundedFoodLeft v)) = false)
    (v : BoundedFoodWord L N) :
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodLeft v)) = leftEdge v) ∧
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodRight v)) = rightEdge v) := by
  apply diamondPotential_edges boundedFoodLeft boundedFoodRight
    (fun v : BoundedFoodWord L N => foodWordHeight L v.val) leftEdge rightEdge
  · intro u
    exact foodWordRight_height L u.val
  · exact boundedFoodParents_commute
  · intro u hu
    rw [boundedFood_zero_height u hu]
    exact hroot
  · exact hdiamond
  · have hv := boundedFoodWord_length_le v
    unfold foodWordHeight
    omega

end HordijkSteelThreshold
