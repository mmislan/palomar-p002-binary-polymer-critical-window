module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def shortBinaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => insert [] ((Finset.univ : Finset Bool).biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))

theorem mem_shortBinaryWords (s : List Bool) (k : ℕ) :
    s ∈ shortBinaryWords k ↔ s.length ≤ k := by
  induction k generalizing s with
  | zero => simp [shortBinaryWords]
  | succ k ih =>
    cases s with
    | nil => simp [shortBinaryWords]
    | cons b t => cases b <;> simp [shortBinaryWords, ih]

theorem shortBinaryWords_card_lt (k : ℕ) : (shortBinaryWords k).card < 2 ^ (k + 1) := by
  induction k with
  | zero => simp [shortBinaryWords]
  | succ k ih =>
    have hc : ((Finset.univ : Finset Bool).biUnion
        (fun b => (shortBinaryWords k).image (List.cons b))).card ≤
        2 * (shortBinaryWords k).card := by
      calc
        _ ≤ ∑ b : Bool, ((shortBinaryWords k).image (List.cons b)).card := Finset.card_biUnion_le
        _ ≤ ∑ _b : Bool, (shortBinaryWords k).card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = 2 * (shortBinaryWords k).card := by simp [two_mul]
    have hi := Finset.card_insert_le [] ((Finset.univ : Finset Bool).biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))
    simp only [shortBinaryWords]
    rw [pow_succ]
    omega

/-- A deliberately loose core envelope; counting both paddings separately removes
dependence on the length of the core and on the ambient molecular universe. -/
def coreWordEnvelope (core : List Bool) (k : ℕ) : Finset (List Bool) :=
  ((shortBinaryWords k) ×ˢ (shortBinaryWords k)).image (fun lr => lr.1 ++ core ++ lr.2)

theorem coreWordEnvelope_contains (core s : List Bool) (k : ℕ)
    (hs : ∃ l r : List Bool, s = l ++ core ++ r)
    (hlen : s.length ≤ core.length + k) : s ∈ coreWordEnvelope core k := by
  obtain ⟨l, r, h⟩ := hs
  have hh := congrArg List.length h
  simp only [List.length_append] at hh
  apply Finset.mem_image.mpr
  refine ⟨(l,r), Finset.mem_product.mpr ⟨?_, ?_⟩, h.symm⟩
  · exact (mem_shortBinaryWords l k).mpr (by omega)
  · exact (mem_shortBinaryWords r k).mpr (by omega)

/-- Uniform exponential bound in extra length, not core length. -/
theorem core_containing_words_card_lt (S : Finset (List Bool)) (core : List Bool) (k : ℕ)
    (hc : ∀ s ∈ S, ∃ l r : List Bool, s = l ++ core ++ r)
    (hl : ∀ s ∈ S, s.length ≤ core.length + k) : S.card < 2 ^ (2 * (k + 1)) := by
  have hs : S ⊆ coreWordEnvelope core k := fun s h =>
    coreWordEnvelope_contains core s k (hc s h) (hl s h)
  have hp := shortBinaryWords_card_lt k
  have hprod : (shortBinaryWords k).card * (shortBinaryWords k).card <
      2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_self_lt_mul_self hp
  calc
    S.card ≤ (coreWordEnvelope core k).card := Finset.card_le_card hs
    _ ≤ (shortBinaryWords k).card * (shortBinaryWords k).card := by
      exact Finset.card_image_le.trans (by rw [Finset.card_product])
    _ < 2 ^ (k + 1) * 2 ^ (k + 1) := hprod
    _ = 2 ^ (2 * (k + 1)) := by rw [← pow_add, two_mul]

end HordijkSteelThreshold
