module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- Induction over actual reversible generation, including both reaction directions. -/
theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset (Reaction N))
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  have hall : ∀ k, ∀ x ∈ revClosureAt (binaryPolymerCRS N L) S k, P x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact hfood x (by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hx)
    | succ k ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ih x hx
      · obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
        rcases Finset.mem_union.mp hx with hx | hx
        · by_cases hen : RevEnabledLhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have he : x = reactionProduct r := Finset.mem_singleton.mp hx
            subst x
            have hh : reactionLeft r ∈ revClosureAt (binaryPolymerCRS N L) S k ∧
                reactionRight r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff,
                Finset.singleton_subset_iff] using hen
            exact hlig r hr (ih _ hh.1) (ih _ hh.2)
          · simp [hen] at hx
        · by_cases hen : RevEnabledRhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have hp : reactionProduct r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              simpa [RevEnabledRhs, binaryPolymerCRS] using hen
            have hh := hcleave r hr (ih _ hp)
            have he : x = reactionLeft r ∨ x = reactionRight r := by
              simpa [binaryPolymerCRS] using hx
            rcases he with rfl | rfl
            · exact hh.1
            · exact hh.2
          · simp [hen] at hx
  exact hall k x hk

noncomputable def highProductReactions {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :=
  S.filter (fun r => L < molLength (reactionProduct r))

/-- Low-product reactions have no effect when every endpoint is supplied food. -/
theorem temporaryReactionClosure_erase_low {N L : ℕ} (S : Finset (Reaction N)) :
    temporaryReactionClosure L (highProductReactions L S) = temporaryReactionClosure L S := by
  apply Finset.Subset.antisymm
  · exact temporaryReactionClosure_mono (Finset.filter_subset _ _)
  · intro x hx
    apply temporaryReactionClosure_induction S (fun y => y ∈ temporaryReactionClosure L
      (highProductReactions L S)) ?_ ?_ ?_ x hx
    · exact temporaryReactionClosure_food _
    · intro r hr hl hh
      by_cases h : L < molLength (reactionProduct r)
      · exact temporaryReactionClosure_ligation _ r (Finset.mem_filter.mpr ⟨hr,h⟩) hl hh
      · exact temporaryReactionClosure_food _ _ (Nat.le_of_not_gt h)
    · intro r hr hp
      by_cases h : L < molLength (reactionProduct r)
      · exact temporaryReactionClosure_cleavage _ r (Finset.mem_filter.mpr ⟨hr,h⟩) hp
      · have hprod := Nat.le_of_not_gt h
        have hsum := reaction_length_add r
        rw [molLength_reactionProduct] at hprod
        exact ⟨temporaryReactionClosure_food _ _ (by rw [molLength_reactionLeft]; omega),
          temporaryReactionClosure_food _ _ (by rw [molLength_reactionRight]; omega)⟩

/-- Once a smaller-food closure generates the supplied seed, it contains every
generation using that seed and any subset of its reactions. -/
theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset (Reaction N)} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T := by
  intro x hx
  exact temporaryReactionClosure_induction S (fun y => y ∈ temporaryReactionClosure K T)
    hseed (fun r hr => temporaryReactionClosure_ligation T r (hST hr))
    (fun r hr => temporaryReactionClosure_cleavage T r (hST hr)) x hx

noncomputable def lowProductBridge (N L : ℕ) : Finset (Reaction N) :=
  Finset.univ.filter (fun r => molLength (reactionProduct r) ≤ L)

/-- Opening all finitely many low-product reactions generates temporary food
from food two. No catalytic chronology is imposed on this static statement. -/
theorem lowProductBridge_generates {N L : ℕ} {S : Finset (Reaction N)}
    (hB : lowProductBridge N L ⊆ S) (x : Molecule N) (hx : molLength x ≤ L) :
    x ∈ temporaryReactionClosure 2 S := by
  induction hlen : molLength x using Nat.strong_induction_on generalizing x with
  | h len ih =>
    by_cases hf : molLength x ≤ 2
    · exact temporaryReactionClosure_food S x hf
    · have hxpos : 0 < x.1.val := by unfold molLength at hf; omega
      let r : Reaction N := ⟨x.1, x.2, ⟨0,hxpos⟩⟩
      have hp : reactionProduct r = x := by rfl
      have hr : r ∈ S := hB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hp]⟩)
      have hl : molLength (reactionLeft r) < molLength x := by
        rw [molLength_reactionLeft]
        dsimp [reactionLeftLength, r, molLength]
        omega
      have hh : molLength (reactionRight r) < molLength x := by
        rw [molLength_reactionRight]
        dsimp [reactionRightLength, r, molLength]
        omega
      rw [← hp]
      exact temporaryReactionClosure_ligation S r hr
        (ih _ (by omega) _ (by omega) rfl)
        (ih _ (by omega) _ (by omega) rfl)

theorem static_seed_bridge_contains_bulk {N L : ℕ} (S : Finset (Reaction N)) :
    temporaryReactionClosure L S ⊆
      temporaryReactionClosure 2 (S ∪ lowProductBridge N L) := by
  exact temporaryReactionClosure_seed_transfer Finset.subset_union_left
    (lowProductBridge_generates Finset.subset_union_right)

end HordijkSteelThreshold
