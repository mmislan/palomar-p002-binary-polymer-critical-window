module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

private theorem xor_pair_cancel (a b c : Bool) :
    ((a ^^ b) ^^ ((b ^^ c) ^^ c)) = a := by
  cases a <;> cases b <;> cases c <;> decide

private theorem xor_diamond_left (a b c d e f : Bool)
    (hcd : (c ^^ d) = e) (hdiamond : (((f ^^ a) ^^ e) ^^ b) = false) :
    ((a ^^ c) ^^ (b ^^ d)) = f := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp_all

/-- Label a vertex by parity along its right-parent path. Root edges carry
zero, so extra recursion depth does not alter the intended path parity. -/
def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) :
    ℕ → V → Bool
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

/-- Local diamond parity integrates to a vertex potential. This gives an
explicit cut certificate, without cycle-space dimensions or linear algebra.
For word truncations, height is nonfood length and the parents commute. -/
theorem diamondPotential_edges {V : Type*}
    (left right : V → V) (height : V → ℕ)
    (leftEdge rightEdge : V → Bool)
    (hheight : ∀ v, height (right v) ≤ height v - 1)
    (hcommute : ∀ v, left (right v) = right (left v))
    (hroot : ∀ v, height v = 0 → leftEdge v = false ∧ rightEdge v = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (right v)) ^^
      rightEdge (left v)) = false)
    (k : ℕ) (v : V) (hv : height v ≤ k) :
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (left v)) = leftEdge v) ∧
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (right v)) = rightEdge v) := by
  induction k generalizing v with
  | zero =>
    obtain ⟨hl, hr⟩ := hroot v (by omega)
    simp [diamondPotential, hl, hr]
  | succ k ih =>
    have hp : height (right v) ≤ k := by
      have hh := hheight v
      omega
    obtain ⟨hil, hir⟩ := ih (right v) hp
    constructor
    · simp only [diamondPotential]
      apply xor_diamond_left _ _ _ _ (leftEdge (right v)) _
      · simpa only [hcommute v] using hil
      · exact hdiamond v
    · simp only [diamondPotential]
      rw [← hir]
      exact xor_pair_cancel _ _ _

end HordijkSteelThreshold
