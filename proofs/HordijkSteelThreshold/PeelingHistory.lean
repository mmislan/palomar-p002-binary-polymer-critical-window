module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

/-- Active reaction history for a deterministic pool-response map. -/
def peelingActiveAt {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) :
    ℕ → Finset R
  | 0 => response Finset.univ
  | t + 1 => response (closure (peelingActiveAt response closure t))

/-- Pools computed from a prescribed active-set history, before testing it
against a random field. These are deterministic when the history is fixed. -/
def prescribedPoolAt {X R : Type*} [Fintype X]
    (closure : Finset R → Finset X) (history : ℕ → Finset R) : ℕ → Finset X
  | 0 => Finset.univ
  | t + 1 => closure (history t)

/-- A history event is exactly the intersection of its fixed-pool response
constraints. There is no extra random closure-consistency condition. -/
theorem peeling_history_iff {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (history : ℕ → Finset R) (T : ℕ) :
    (∀ t ≤ T, peelingActiveAt response closure t = history t) ↔
      ∀ t ≤ T, response (prescribedPoolAt closure history t) = history t := by
  constructor
  · intro h t ht
    cases t with
    | zero => exact h 0 ht
    | succ t =>
      have hp := h t (by omega)
      simpa only [peelingActiveAt, hp, prescribedPoolAt] using h (t + 1) ht
  · intro h t
    induction t with
    | zero => exact h 0
    | succ t ih =>
      intro ht
      have hp := ih (by omega)
      simpa only [peelingActiveAt, hp, prescribedPoolAt] using h (t + 1) ht

theorem peelingActiveAt_antitone {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hresponse : Monotone response) (hclosure : Monotone closure) :
    Antitone (peelingActiveAt response closure) := by
  apply antitone_nat_of_succ_le
  intro t
  induction t with
  | zero => exact hresponse (Finset.subset_univ _)
  | succ t ih => exact hresponse (hclosure ih)

theorem prescribedPoolAt_antitone {X R : Type*} [Fintype X]
    (closure : Finset R → Finset X) (hclosure : Monotone closure)
    (history : ℕ → Finset R) (hhistory : Antitone history) :
    Antitone (prescribedPoolAt closure history) := by
  apply antitone_nat_of_succ_le
  intro t
  cases t with
  | zero => exact Finset.subset_univ _
  | succ t => exact hclosure (hhistory (Nat.le_succ t))

end HordijkSteelThreshold
