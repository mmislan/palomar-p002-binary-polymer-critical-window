module

public import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

theorem unbounded_separated_words {L ell : ℕ} {field : InfiniteSplitEnvironment}
    (h : ReversibleUnbounded L field) (J : ℕ) :
    ∃ W : Finset (List Bool), W.card = J ∧
      (∀ w ∈ W, 0 < w.length ∧ InfiniteReversibleGenerated L field w) ∧
      ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
        u.length + ell ≤ v.length ∨ v.length + ell ≤ u.length := by
  induction J with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ J ih =>
    obtain ⟨W, hc, hg, hs⟩ := ih
    obtain ⟨w, hw, hgen⟩ := h (W.sup List.length + ell)
    have hn : w ∉ W := by
      intro hm
      have hl := Finset.le_sup (f := List.length) hm
      omega
    refine ⟨insert w W, by simp [hn, hc], ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨by omega, hgen⟩
      · exact hg v hv
    · intro u hu v hv hne
      rcases Finset.mem_insert.mp hu with rfl | huW
      · rcases Finset.mem_insert.mp hv with rfl | hvW
        · exact (hne rfl).elim
        · right
          have hl := Finset.le_sup (f := List.length) hvW
          omega
      · rcases Finset.mem_insert.mp hv with rfl | hvW
        · left
          have hl := Finset.le_sup (f := List.length) huW
          omega
        · exact hs u huW v hvW hne

/-- Arbitrarily many separated base words and their derivations fit in one
finite cap, leaving room for every target trial of the prescribed length. -/
theorem unbounded_finite_trials {L ell : ℕ} {field : InfiniteSplitEnvironment}
    (h : ReversibleUnbounded L field) (J : ℕ) :
    ∃ N, ∃ W : Finset (List Bool), W.card = J ∧
      (∀ w ∈ W, 0 < w.length ∧ w.length + ell ≤ N ∧
        FiniteReversibleGenerated N L field w) ∧
      ∀ u ∈ W, ∀ v ∈ W, u ≠ v →
        u.length + ell ≤ v.length ∨ v.length + ell ≤ u.length := by
  obtain ⟨W, hc, hg, hs⟩ := unbounded_separated_words (ell := ell) h J
  obtain ⟨N, hN⟩ := (finite_seed_common_cap W).mp (fun w hw => (hg w hw).2)
  refine ⟨max N (W.sup List.length + ell), W, hc, ?_, hs⟩
  intro w hw
  refine ⟨(hg w hw).1, ?_, finiteReversibleGenerated_mono_cap (Nat.le_max_left _ _) (hN w hw)⟩
  have hl := Finset.le_sup (f := List.length) hw
  omega

end HordijkSteelThreshold
