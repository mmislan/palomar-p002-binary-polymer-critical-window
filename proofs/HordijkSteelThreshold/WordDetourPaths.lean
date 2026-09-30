module

public import proofs.HordijkSteelThreshold.WordDetourIncidence
public import proofs.HordijkSteelThreshold.BasicSourceEdges

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def wordDropShort (s : List Bool) (side : Bool) (k : ℕ) : List Bool :=
  if side then s.take (s.length-k) else s.drop k

theorem wordDropShort_length (s : List Bool) (side : Bool) (k : ℕ) :
    (wordDropShort s side k).length = s.length-k := by
  cases side <;> simp [wordDropShort]

theorem wordDropShort_one (s : List Bool) (side : Bool) :
    wordDropShort s side 1 = if side then s.dropLast else s.tail := by
  cases side <;> simp [wordDropShort, List.dropLast_eq_take]

theorem wordDropShort_comp (s : List Bool) (side : Bool) (j : ℕ) :
    wordDropShort (wordDropShort s side 1) side j =
      wordDropShort s side (j+1) := by
  cases side
  · simp [wordDropShort]
  · simp only [wordDropShort, ↓reduceIte, List.length_take, List.take_take]
    congr 1
    omega

theorem contract_wordDropShort_one {L N : ℕ} (e : WordBasicEdge L N) :
    contractFoodWord L (wordDropShort e.1.val e.2 1) = (wordEdgeParent e).val := by
  rw [wordDropShort_one]
  rcases e with ⟨v, side⟩
  cases side
  · exact contractFoodWord_tail L v.val
  · exact contractFoodWord_dropLast L v.val

theorem wordEdgeParent_nonroot_word {L N : ℕ} (e : WordBasicEdge L N)
    (h : wordEdgeParent e ≠ boundedFoodRoot L N) :
    (wordEdgeParent e).val = wordDropShort e.1.val e.2 1 := by
  have he := contract_wordDropShort_one e
  unfold contractFoodWord at he
  split_ifs at he with hs
  · exact False.elim (h (Subtype.ext he.symm))
  · exact he.symm

theorem wordEdgeParent_root_length {L N : ℕ} (e : WordBasicEdge L N)
    (h : wordEdgeParent e = boundedFoodRoot L N) : e.1.val.length ≤ L+1 := by
  have he := contract_wordDropShort_one e
  rw [h] at he
  change contractFoodWord L (wordDropShort e.1.val e.2 1) = [] at he
  unfold contractFoodWord at he
  by_cases hs : (wordDropShort e.1.val e.2 1).length ≤ L
  · rw [wordDropShort_length] at hs
    omega
  · rw [ite_eq_right hs] at he
    have hz := congrArg List.length he
    simp only [wordDropShort_length, List.length_nil] at hz
    rw [wordDropShort_length] at hs
    omega

def wordShortStart {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L r.1.1.val

def wordShortEnd {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L (wordDropShort r.1.1.val r.1.2 (r.2.val+1))

/-- Every detour is a genuine one- or two-edge path after food contraction.
No assertion of reaction openness or catalytic support is assumed here. -/
theorem wordDetourKeys_reach_parent {L N w : ℕ} (d : WordShortKey L N w) :
    indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordEdgeParent d.1).val := by
  have hd : d ∈ wordDetourKeys d := by simp [wordDetourKeys]
  have upper : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordShortEnd d) :=
    Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩
  by_cases hj : d.2.val = 0
  · have he : wordShortEnd d = (wordEdgeParent d.1).val := by
      simpa only [wordShortEnd, hj, zero_add] using contract_wordDropShort_one d.1
    exact he ▸ upper
  · by_cases hp : wordEdgeParent d.1 = boundedFoodRoot L N
    · have hm := wordEdgeParent_root_length d.1 hp
      have he : wordShortEnd d = (wordEdgeParent d.1).val := by
        rw [hp]
        change contractFoodWord L (wordDropShort d.1.1.val d.1.2 (d.2.val+1)) = []
        apply ite_eq_left
        rw [wordDropShort_length]
        omega
      exact he ▸ upper
    · let r : WordShortKey L N w :=
        ((wordEdgeParent d.1, d.1.2), ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)
      have hlower : wordDetourLower d = some r := by
        simp only [wordDetourLower, hj, hp, or_self, ↓reduceIte]
        rfl
      have hr : r ∈ wordDetourKeys d := by simp [wordDetourKeys, hlower]
      have hrs : wordShortStart r = (wordEdgeParent d.1).val := by
        change contractFoodWord L (wordEdgeParent d.1).val = (wordEdgeParent d.1).val
        apply ite_eq_right
        intro hh
        rcases (wordEdgeParent d.1).property with hnil | hlen
        · exact hp (Subtype.ext hnil)
        · omega
      have hre : wordShortEnd r = wordShortEnd d := by
        have hjr : d.2.val-1+1 = d.2.val := by omega
        change contractFoodWord L (wordDropShort (wordEdgeParent d.1).val d.1.2
          (d.2.val-1+1)) = wordShortEnd d
        rw [hjr, wordEdgeParent_nonroot_word d.1 hp, wordDropShort_comp]
        rfl
      have lower : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
          (wordEdgeParent d.1).val (wordShortEnd d) :=
        Relation.EqvGen.rel _ _ ⟨r, hr, hrs, hre⟩
      exact Relation.EqvGen.trans _ _ _ upper (Relation.EqvGen.symm _ _ lower)

end HordijkSteelThreshold
