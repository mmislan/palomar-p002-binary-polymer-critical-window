module

public import proofs.HordijkSteelThreshold.PeelingHistory

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem peelingActiveAt_fixed_persists {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    {t : ℕ} (ht : peelingActiveAt response closure (t+1) = peelingActiveAt response closure t) :
    ∀ j, peelingActiveAt response closure (t+j) = peelingActiveAt response closure t := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      _ = response (closure (peelingActiveAt response closure (t+j))) := by
        rw [Nat.add_succ, peelingActiveAt]
      _ = _ := by rw [ih]; exact ht

/-- A decreasing finite reaction iteration stabilizes by the reaction-cardinality
horizon. This horizon is deterministic and so can be used in a probability bound. -/
theorem peelingActiveAt_stable_card {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hr : Monotone response) (hc : Monotone closure) :
    peelingActiveAt response closure (Fintype.card R+1) =
      peelingActiveAt response closure (Fintype.card R) := by
  have hanti := peelingActiveAt_antitone response closure hr hc
  by_contra hfail
  have hneq : ∀ t ≤ Fintype.card R,
      peelingActiveAt response closure (t+1) ≠ peelingActiveAt response closure t := by
    intro t ht he
    have h1 := peelingActiveAt_fixed_persists response closure he (Fintype.card R+1-t)
    have h0 := peelingActiveAt_fixed_persists response closure he (Fintype.card R-t)
    have he1 : t+(Fintype.card R+1-t) = Fintype.card R+1 := by omega
    have he0 : t+(Fintype.card R-t) = Fintype.card R := by omega
    rw [he1] at h1
    rw [he0] at h0
    exact hfail (h1.trans h0.symm)
  have hbound : ∀ t ≤ Fintype.card R+1,
      (peelingActiveAt response closure t).card+t ≤ Fintype.card R := by
    intro t
    induction t with
    | zero => intro _; simpa using Finset.card_le_univ (peelingActiveAt response closure 0)
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have hs := hanti (Nat.le_succ t)
      have hlt : (peelingActiveAt response closure (t+1)).card <
          (peelingActiveAt response closure t).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hneq t (by omega)⟩)
      omega
  have hh := hbound (Fintype.card R+1) le_rfl
  omega

end HordijkSteelThreshold
