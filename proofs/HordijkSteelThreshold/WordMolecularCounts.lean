module

public import proofs.HordijkSteelThreshold.WordCoreCount

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem shortBinaryWords_card_exact (n : ℕ) :
    (shortBinaryWords n).card + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [shortBinaryWords]
  | succ n ih =>
    have he : shortBinaryWords (n + 1) = insert []
        (((shortBinaryWords n).image (List.cons true)) ∪
         ((shortBinaryWords n).image (List.cons false))) := by
      ext s
      simp [shortBinaryWords]
    have hd : Disjoint ((shortBinaryWords n).image (List.cons true))
        ((shortBinaryWords n).image (List.cons false)) := by
      apply Finset.disjoint_left.mpr
      intro s hs ht
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ht
      have h := ha.trans hb.symm
      simp at h
    have hn : [] ∉ ((shortBinaryWords n).image (List.cons true)) ∪
        ((shortBinaryWords n).image (List.cons false)) := by simp
    rw [he, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hd]
    rw [Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, pow_succ]
    omega

def actualBinaryWords (N : ℕ) : Finset (List Bool) := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
  simp only [actualBinaryWords, Finset.mem_erase, mem_shortBinaryWords]

theorem actualBinaryWords_card (N : ℕ) : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
  have h := shortBinaryWords_card_exact N
  have hn : [] ∈ shortBinaryWords N := (mem_shortBinaryWords [] N).mpr (by simp)
  simp only [actualBinaryWords, Finset.card_erase_of_mem hn]
  omega

/-- A molecularly smaller side cannot contain a constant-label high band with a spare level.
The proof counts the complement below M, rather than the contracted graph vertices. -/
theorem molecular_minor_side_below_band (N M : ℕ) (hMN : M < N)
    (S : Finset (List Bool)) (hsub : S ⊆ actualBinaryWords N)
    (hminor : S.card ≤ (actualBinaryWords N \ S).card)
    (hconstant : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
      M ≤ u.length → M ≤ v.length → (u ∈ S ↔ v ∈ S))
    (s : List Bool) (hs : s ∈ S) : s.length < M := by
  by_contra h
  have hcomp : actualBinaryWords N \ S ⊆ shortBinaryWords (M - 1) := by
    intro t ht
    obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
    have hlt : t.length < M := by
      by_contra hge
      exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs)
    exact (mem_shortBinaryWords t (M - 1)).mpr (by omega)
  have hM : 0 < M := by
    by_contra hz
    have hc : actualBinaryWords N \ S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
      exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs)
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
    simp only [hc, Finset.card_empty] at hminor
    omega
  have hc : (actualBinaryWords N \ S).card < 2 ^ M := by
    have hx := (Finset.card_le_card hcomp).trans_lt (shortBinaryWords_card_lt (M - 1))
    simpa only [Nat.sub_add_cancel hM] using hx
  have hp : (2 : ℕ) ^ M < 2 ^ N := (pow_lt_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mpr hMN
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  rw [actualBinaryWords_card, pow_succ] at hpartition
  omega

end HordijkSteelThreshold
