module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem source_append_split {N : ℕ} (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN)
  let r := sourceSplitReaction x u.length hu (by simp [x]; omega)
  refine ⟨r, ?_, ?_, ?_⟩
  · simp [r, moleculeWord_reactionLeft, x]
  · simp [r, moleculeWord_reactionRight, x]
  · simp [r, x]

/-- Appending a word needs at most one literal reaction per new letter.
The statement retains its cap and product-length band for disjoint trials. -/
theorem append_trial_support {N : ℕ} (w v : List Bool)
    (hw : 0 < w.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset (Reaction N), S.card ≤ v.length ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset (Reaction N), S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = w ++ v := by
  induction v using List.reverseRecOn with
  | nil =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro T _ x hx he
    exact ⟨x, hx, by simpa using he⟩
  | append_singleton v b ih =>
    have hn : w.length + v.length ≤ N := by
      simp only [List.length_append, List.length_singleton] at hN
      omega
    obtain ⟨S, hcard, hband, hgen⟩ := ih hn
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) (w ++ v) [b]
      (by simp; omega) (by simp) (by simpa [List.length_append, Nat.add_assoc] using hN)
    have hlen : molLength (reactionProduct r) = w.length + v.length + 1 := by
      rw [← moleculeWord_length, hp]
      simp [Nat.add_assoc]
    refine ⟨insert r S, ?_, ?_, ?_⟩
    · have hc := Finset.card_insert_le r S
      simp only [List.length_append, List.length_singleton]
      omega
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · simp only [List.length_append, List.length_singleton]
        omega
      · have hh := hband q hq
        simp only [List.length_append, List.length_singleton]
        omega
    · intro T hST x hx he
      obtain ⟨y, hy, hey⟩ := hgen T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
      have hleft : reactionLeft r = y := moleculeWord_injective (hl.trans hey.symm)
      have hright : molLength (reactionRight r) ≤ 2 := by
        rw [← moleculeWord_length, hr]
        simp
      refine ⟨reactionProduct r, temporaryReactionClosure_ligation T r
        (hST (Finset.mem_insert_self _ _)) (hleft.symm ▸ hy)
        (temporaryReactionClosure_food T _ hright), ?_⟩
      simpa [List.append_assoc] using hp

/-- A long generated word can manufacture any nonempty target by a bounded
append-and-cleave trial, without assuming the target is already food. -/
theorem target_trial_support {N : ℕ} (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset (Reaction N), S.card ≤ v.length + 1 ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset (Reaction N), S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = v := by
  obtain ⟨S, hc, hb, hg⟩ := append_trial_support w v hw hN
  obtain ⟨r, _, hr, hp⟩ := source_append_split (N := N) w v hw hv hN
  have hlen : molLength (reactionProduct r) = w.length + v.length := by
    rw [← moleculeWord_length, hp, List.length_append]
  refine ⟨insert r S, (Finset.card_insert_le r S).trans (by omega), ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · omega
    · exact hb q hq
  · intro T hST x hx he
    obtain ⟨y, hy, hey⟩ := hg T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
    have heq : reactionProduct r = y := moleculeWord_injective (hp.trans hey.symm)
    exact ⟨reactionRight r, (temporaryReactionClosure_cleavage T r
      (hST (Finset.mem_insert_self _ _)) (heq.symm ▸ hy)).2, hr⟩

theorem target_trial_bands_disjoint {N ell k l : ℕ}
    (S T : Finset (Reaction N)) (hgap : k + ell ≤ l)
    (hS : ∀ r ∈ S, molLength (reactionProduct r) ≤ k + ell)
    (hT : ∀ r ∈ T, l < molLength (reactionProduct r)) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have h1 := hS r hr
  have h2 := hT r hs
  omega

end HordijkSteelThreshold
