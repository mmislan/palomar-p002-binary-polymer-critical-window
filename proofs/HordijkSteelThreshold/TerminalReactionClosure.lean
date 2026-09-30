module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF RAF.Polymer RAF.Concrete

noncomputable def usableClosureReactions {N : ℕ} (L : ℕ) (A : Finset (Reaction N)) :=
  A.filter (fun r => reactionLeft r ∈ temporaryReactionClosure L A ∧
    reactionRight r ∈ temporaryReactionClosure L A ∧
    reactionProduct r ∈ temporaryReactionClosure L A)

/-- Removing reactions whose endpoints are unavailable does not remove any
actual generation step. Both reversible directions are retained. -/
theorem usableClosureReactions_closure {N L : ℕ} (A : Finset (Reaction N)) :
    temporaryReactionClosure L (usableClosureReactions L A) = temporaryReactionClosure L A := by
  have hsub : usableClosureReactions L A ⊆ A := Finset.filter_subset _ _
  have hm := temporaryReactionClosure_mono (L := L) hsub
  apply Finset.Subset.antisymm hm
  intro x hx
  apply temporaryReactionClosure_induction A
    (fun y => y ∈ temporaryReactionClosure L (usableClosureReactions L A)) ?_ ?_ ?_ x hx
  · exact temporaryReactionClosure_food _
  · intro r hr hl hh
    have hp := temporaryReactionClosure_ligation A r hr (hm hl) (hm hh)
    have hr' : r ∈ usableClosureReactions L A :=
      Finset.mem_filter.mpr ⟨hr,hm hl,hm hh,hp⟩
    exact temporaryReactionClosure_ligation _ r hr' hl hh
  · intro r hr hp
    have hh := temporaryReactionClosure_cleavage A r hr (hm hp)
    have hr' : r ∈ usableClosureReactions L A :=
      Finset.mem_filter.mpr ⟨hr,hh.1,hh.2,hm hp⟩
    exact temporaryReactionClosure_cleavage _ r hr' hp

theorem usableClosureReactions_nonempty {N L : ℕ} (A : Finset (Reaction N))
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    (usableClosureReactions L A).Nonempty := by
  obtain ⟨x,hx,hxl⟩ := hx
  rw [← usableClosureReactions_closure A] at hx
  by_contra he
  have hempty : usableClosureReactions L A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hh : molLength x ≤ L := by
    apply temporaryReactionClosure_induction (usableClosureReactions L A)
      (fun y => molLength y ≤ L) (fun _ h => h) ?_ ?_ x hx
    · intro r hr
      simp [hempty] at hr
    · intro r hr
      simp [hempty] at hr
  omega

/-- Internally catalyzed active reactions yield a literal RAF after removal of
unavailable reactions, provided their closure contains a nonfood molecule. -/
theorem usableClosureReactions_isRAF {N L : ℕ} (A : Finset (Reaction N))
    (Cat : Catalysis (Molecule N) (Reaction N))
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  refine ⟨usableClosureReactions_nonempty A hx, ?_, ?_⟩
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    have he := usableClosureReactions_closure (L := L) A
    have hl : reactionLeft r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.1
    have hr' : reactionRight r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.1
    have hp : reactionProduct r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.2
    obtain ⟨kl,hkl⟩ := (mem_temporaryReactionClosure _ _).mp hl
    obtain ⟨kr,hkr⟩ := (mem_temporaryReactionClosure _ _).mp hr'
    obtain ⟨kp,hkp⟩ := (mem_temporaryReactionClosure _ _).mp hp
    let k := max kl (max kr kp)
    have hlk := revClosureAt_mono_stage _ _ (Nat.le_max_left kl (max kr kp)) hkl
    have hrk := revClosureAt_mono_stage _ _
      ((Nat.le_max_left kr kp).trans (Nat.le_max_right kl (max kr kp))) hkr
    have hpk := revClosureAt_mono_stage _ _
      ((Nat.le_max_right kr kp).trans (Nat.le_max_right kl (max kr kp))) hkp
    refine ⟨k,?_⟩
    intro y hy
    have hmem : y = reactionLeft r ∨ y = reactionRight r ∨ y = reactionProduct r := by
      simpa [binaryPolymerCRS] using hy
    rcases hmem with rfl | rfl | rfl
    · exact hlk
    · exact hrk
    · exact hpk
  · intro r hr
    obtain ⟨x,hx,hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← usableClosureReactions_closure A] at hx
    obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
    exact ⟨x,k,hk,hxr⟩

end HordijkSteelThreshold
