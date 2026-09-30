module

public import proofs.HordijkSteelThreshold.ShortSourceReactions
public import proofs.HordijkSteelThreshold.WordDetourIncidence

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

def sourceWordMolecule {N : ℕ} (s : List Bool) (hs : 0 < s.length)
    (hN : s.length ≤ N) : Molecule N := moleculeOfCode hs hN (listWord s)

@[simp] theorem sourceWordMolecule_length {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    moleculeWord (sourceWordMolecule s hs hN) = s := by
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, sourceWordMolecule_length]
  · rw [binaryWordCode_moleculeWord]
    rfl

theorem boundedFoodWord_nonroot_length {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : L < v.val.length := by
  rcases v.property with h | h
  · exact False.elim (hv (Subtype.ext h))
  · exact h.1

/-- Literal source realization of each nonfood short key. Root keys produce no reaction. -/
noncomputable def wordShortSourceOption {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) : Option (Reaction N) :=
  if hr : r.1.1 = boundedFoodRoot L N then none else
    let x := sourceWordMolecule r.1.1.val
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr; omega)
      (boundedFoodWord_length_le r.1.1)
    some (sourceShortReaction x r.1.2 (r.2.val+1) (by omega)
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr
          have hj := r.2.isLt
          simp only [x, sourceWordMolecule_length]
          omega))

theorem wordShortSourceOption_injective {L N w : ℕ} (hL : 2*w ≤ L)
    (r s : WordShortKey L N w) (a : Reaction N)
    (hr : wordShortSourceOption hL r = some a)
    (hs : wordShortSourceOption hL s = some a) : r = s := by
  have hrn : r.1.1 ≠ boundedFoodRoot L N := by
    intro hn
    simp [wordShortSourceOption, hn] at hr
  have hsn : s.1.1 ≠ boundedFoodRoot L N := by
    intro hn
    simp [wordShortSourceOption, hn] at hs
  unfold wordShortSourceOption at hr hs
  rw [dite_eq_right hrn] at hr
  rw [dite_eq_right hsn] at hs
  have he := (Option.some.inj hr).trans (Option.some.inj hs).symm
  have hrl := boundedFoodWord_nonroot_length r.1.1 hrn
  have hsl := boundedFoodWord_nonroot_length s.1.1 hsn
  obtain ⟨hp, hb, hk⟩ := sourceShortReaction_coordinates (w := w) _ _ r.1.2 s.1.2
    (r.2.val+1) (s.2.val+1) (by omega) (by omega)
    (by omega) (by omega)
    (by simp only [sourceWordMolecule_length]; omega)
    (by simp only [sourceWordMolecule_length]; omega) he
  have hw := congrArg moleculeWord hp
  simp only [sourceWordMolecule_word] at hw
  exact Prod.ext (Prod.ext (Subtype.ext hw) hb) (Fin.ext (by omega))

noncomputable def wordDetourSourceReactions {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : Finset (Reaction N) :=
  (wordDetourKeys d).biUnion (fun r => (wordShortSourceOption hL r).toFinset)

theorem wordDetourSourceReactions_card {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : (wordDetourSourceReactions hL d).card ≤ 2 := by
  unfold wordDetourSourceReactions
  calc
    _ ≤ ∑ r ∈ wordDetourKeys d, (wordShortSourceOption hL r).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ wordDetourKeys d, 1 := by
      apply Finset.sum_le_sum
      intro r _
      cases wordShortSourceOption hL r <;> simp
    _ = (wordDetourKeys d).card := by simp
    _ ≤ 2 := wordDetourKeys_card d

/-- The actual source ID overlap bound, without an independence assumption on
basic edges or a quotient of coincident reaction IDs. -/
theorem wordDetourSourceReactions_incidence {L N w : ℕ} (hL : 2*w ≤ L)
    (a : Reaction N) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      a ∈ wordDetourSourceReactions hL d)).card ≤ 3 := by
  by_cases ha : ∃ r : WordShortKey L N w, wordShortSourceOption hL r = some a
  · obtain ⟨r, hr⟩ := ha
    have hsub : (Finset.univ.filter (fun d : WordShortKey L N w =>
        a ∈ wordDetourSourceReactions hL d)) ⊆
        (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)) := by
      intro d hd
      obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
      have he : wordShortSourceOption hL s = some a := Option.mem_toFinset.mp hsa
      have hsr := wordShortSourceOption_injective hL s r a he hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr ▸ hs⟩
    exact (Finset.card_le_card hsub).trans (wordDetourKeys_incidence r)
  · have he : (Finset.univ.filter (fun d : WordShortKey L N w =>
        a ∈ wordDetourSourceReactions hL d)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
      exact ha ⟨r, Option.mem_toFinset.mp hr⟩
    rw [he]
    simp

end HordijkSteelThreshold
