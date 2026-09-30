module

public import proofs.HordijkSteelThreshold.MarkedInfiniteLigation
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- A finite source-level marked molecule core. Every nonfood molecule has an
actual split-position reaction with both shorter factors and a catalyst inside
the same finite molecule set. -/
def IsMarkedMoleculeCore {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n)) (C : Finset (Molecule n)) : Prop :=
  binaryFood n foodLength ⊆ C ∧
  ∀ x ∈ C, foodLength < molLength x →
    ∃ r : Reaction n,
      reactionProduct r = x ∧ reactionLeft r ∈ C ∧ reactionRight r ∈ C ∧
      ∃ y ∈ C, Cat y r

/-- All internally supported split reactions carried by `C`. -/
noncomputable def markedCoreReactions {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n)) (C : Finset (Molecule n)) :
    Finset (Reaction n) := by
  classical
  exact Finset.univ.filter fun r =>
    reactionProduct r ∈ C ∧ reactionLeft r ∈ C ∧ reactionRight r ∈ C ∧
      ∃ y ∈ C, Cat y r

@[simp] theorem mem_markedCoreReactions {n : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)} {C : Finset (Molecule n)}
    {r : Reaction n} :
    r ∈ markedCoreReactions Cat C ↔
      reactionProduct r ∈ C ∧ reactionLeft r ∈ C ∧ reactionRight r ∈ C ∧
        ∃ y ∈ C, Cat y r := by
  classical
  simp [markedCoreReactions]

theorem revClosureAt_subset_succ {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : Nat) :
    revClosureAt Q S k ⊆ revClosureAt Q S (k + 1) := by
  intro x hx
  change x ∈ revClosureStep Q S (revClosureAt Q S k)
  exact Finset.mem_union_left _ hx

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih => exact ih.trans (revClosureAt_subset_succ Q S j)

theorem markedCore_subset_closure {n foodLength : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)} {C : Finset (Molecule n)}
    (hC : IsMarkedMoleculeCore foodLength Cat C) {x : Molecule n} (hx : x ∈ C) :
    ∃ k, x ∈ revClosureAt (binaryPolymerCRS n foodLength)
      (markedCoreReactions Cat C) k := by
  classical
  induction hlen : molLength x using Nat.strong_induction_on generalizing x with
  | h length ih =>
      by_cases hfood : molLength x ≤ foodLength
      · exact ⟨0, by simpa [revClosureAt, binaryPolymerCRS, binaryFood]⟩
      · have hnonfood : foodLength < molLength x := Nat.lt_of_not_ge hfood
        obtain ⟨r, hprod, hleftC, hrightC, y, hyC, hcat⟩ :=
          hC.2 x hx hnonfood
        have hleftLen : molLength (reactionLeft r) < molLength x := by
          rw [← hprod, molLength_reactionLeft, molLength_reactionProduct]
          dsimp [reactionLeftLength, reactionProductLength]
          omega
        have hrightLen : molLength (reactionRight r) < molLength x := by
          rw [← hprod, molLength_reactionRight, molLength_reactionProduct]
          dsimp [reactionRightLength, reactionProductLength]
          omega
        have hleftLen' : molLength (reactionLeft r) < length :=
          hleftLen.trans_le hlen.le
        have hrightLen' : molLength (reactionRight r) < length :=
          hrightLen.trans_le hlen.le
        obtain ⟨kl, hleft⟩ := ih _ hleftLen' hleftC rfl
        obtain ⟨kr, hright⟩ := ih _ hrightLen' hrightC rfl
        let k := max kl kr
        have hleft' := revClosureAt_mono_stage
          (binaryPolymerCRS n foodLength) (markedCoreReactions Cat C)
          (Nat.le_max_left kl kr) hleft
        have hright' := revClosureAt_mono_stage
          (binaryPolymerCRS n foodLength) (markedCoreReactions Cat C)
          (Nat.le_max_right kl kr) hright
        have hrmem : r ∈ markedCoreReactions Cat C := by
          apply mem_markedCoreReactions.mpr
          exact ⟨hprod ▸ hx, hleftC, hrightC, y, hyC, hcat⟩
        refine ⟨k + 1, ?_⟩
        change x ∈ revClosureStep (binaryPolymerCRS n foodLength)
          (markedCoreReactions Cat C)
          (revClosureAt (binaryPolymerCRS n foodLength)
            (markedCoreReactions Cat C) k)
        rw [← hprod]
        simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion]
        right
        refine ⟨r, hrmem, ?_⟩
        left
        have henabled : RevEnabledLhs (binaryPolymerCRS n foodLength)
            (revClosureAt (binaryPolymerCRS n foodLength)
              (markedCoreReactions Cat C) k) r := by
          intro z hz
          simp [binaryPolymerCRS] at hz
          rcases hz with rfl | rfl
          · exact hleft'
          · exact hright'
        rw [ite_eq_left henabled]
        simp [binaryPolymerCRS]

/-- A nontrivial finite marked molecule core yields an ordinary RAF in the
literal split-position reversible polymer source. -/
theorem markedCoreReactions_isRevRAF {n foodLength : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)} {C : Finset (Molecule n)}
    (hC : IsMarkedMoleculeCore foodLength Cat C)
    (hnontrivial : ∃ x ∈ C, foodLength < molLength x) :
    IsRevRAF (binaryPolymerCRS n foodLength) Cat (markedCoreReactions Cat C) := by
  classical
  have hclosure : ∀ x ∈ C, ∃ k, x ∈ revClosureAt
      (binaryPolymerCRS n foodLength) (markedCoreReactions Cat C) k :=
    fun x hx => markedCore_subset_closure hC hx
  obtain ⟨x, hxC, hxlen⟩ := hnontrivial
  obtain ⟨r, hprod, hleftC, hrightC, y, hyC, hcat⟩ := hC.2 x hxC hxlen
  have hrmem : r ∈ markedCoreReactions Cat C := by
    apply mem_markedCoreReactions.mpr
    exact ⟨hprod ▸ hxC, hleftC, hrightC, y, hyC, hcat⟩
  refine ⟨⟨r, hrmem⟩, ?_, ?_⟩
  · intro s hs
    obtain ⟨hprodC, hleftC, hrightC, z, hzC, hzcat⟩ :=
      mem_markedCoreReactions.mp hs
    obtain ⟨kp, hp⟩ := hclosure _ hprodC
    obtain ⟨kl, hl⟩ := hclosure _ hleftC
    obtain ⟨kr, hr⟩ := hclosure _ hrightC
    let k := max kp (max kl kr)
    have hp' := revClosureAt_mono_stage _ _ (Nat.le_max_left kp (max kl kr)) hp
    have hl' := revClosureAt_mono_stage _ _
      ((Nat.le_max_left kl kr).trans (Nat.le_max_right kp (max kl kr))) hl
    have hr' := revClosureAt_mono_stage _ _
      ((Nat.le_max_right kl kr).trans (Nat.le_max_right kp (max kl kr))) hr
    refine ⟨k, ?_⟩
    intro u hu
    simp [binaryPolymerCRS] at hu
    rcases hu with rfl | rfl | rfl
    · exact hl'
    · exact hr'
    · exact hp'
  · intro s hs
    obtain ⟨_, _, _, z, hzC, hzcat⟩ := mem_markedCoreReactions.mp hs
    obtain ⟨k, hk⟩ := hclosure z hzC
    exact ⟨z, k, hk, hzcat⟩

end HordijkSteelThreshold
