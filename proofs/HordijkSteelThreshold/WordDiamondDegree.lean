module

public import proofs.HordijkSteelThreshold.WordParentFibers
public import proofs.HordijkSteelThreshold.WordBondConnected

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordDiamondIncidence {L N : ℕ} (e : WordBasicEdge L N) :=
  Finset.univ.filter (fun v : BoundedFoodWord L N => ∃ i, wordDiamondSlot v i = e)

theorem wordDiamond_incidence_false {L N : ℕ} (u v : BoundedFoodWord L N) :
    (∃ i, wordDiamondSlot v i = (u, false)) ↔ v = u ∨ boundedFoodRight v = u := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [wordDiamondSlot]
  · rintro (h | h)
    · exact ⟨0, by simp [wordDiamondSlot, h]⟩
    · exact ⟨2, by simp [wordDiamondSlot, h]⟩

theorem wordDiamond_incidence_true {L N : ℕ} (u v : BoundedFoodWord L N) :
    (∃ i, wordDiamondSlot v i = (u, true)) ↔ v = u ∨ boundedFoodLeft v = u := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [wordDiamondSlot]
  · rintro (h | h)
    · exact ⟨1, by simp [wordDiamondSlot, h]⟩
    · exact ⟨3, by simp [wordDiamondSlot, h]⟩

theorem wordDiamond_incidence_card {L N : ℕ} (e : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) : (wordDiamondIncidence e).card ≤ 3 := by
  have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using he
  rcases e with ⟨u, b⟩
  cases b
  · have hs : wordDiamondIncidence (u, false) ⊆
        insert u (Finset.univ.filter (fun v => boundedFoodRight v = u)) := by
      intro v hv
      have h := (wordDiamond_incidence_false u v).mp (Finset.mem_filter.mp hv).2
      simpa using h
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hf := boundedFoodRight_fiber_card u hn
    omega
  · have hs : wordDiamondIncidence (u, true) ⊆
        insert u (Finset.univ.filter (fun v => boundedFoodLeft v = u)) := by
      intro v hv
      have h := (wordDiamond_incidence_true u v).mp (Finset.mem_filter.mp hv).2
      simpa using h
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hf := boundedFoodLeft_fiber_card u hn
    omega

noncomputable def wordDiamondEdges {L N : ℕ} (v : BoundedFoodWord L N) :=
  (Finset.univ : Finset (Fin 4)).image (wordDiamondSlot v)

noncomputable def wordDiamondNeighbors {L N : ℕ} (e : WordBasicEdge L N) :=
  (wordDiamondIncidence e).biUnion (fun v => (wordDiamondEdges v).erase e)

theorem wordDiamond_neighbors_card {L N : ℕ} (e : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) : (wordDiamondNeighbors e).card ≤ 9 := by
  have hb : ∀ v ∈ wordDiamondIncidence e, ((wordDiamondEdges v).erase e).card ≤ 3 := by
    intro v hv
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    have hm : e ∈ wordDiamondEdges v := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    have hc : (wordDiamondEdges v).card ≤ 4 := Finset.card_image_le.trans (by decide)
    rw [Finset.card_erase_of_mem hm]
    omega
  have hc := wordDiamond_incidence_card e he
  calc
    (wordDiamondNeighbors e).card ≤ ∑ v ∈ wordDiamondIncidence e, ((wordDiamondEdges v).erase e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ wordDiamondIncidence e, 3 := Finset.sum_le_sum hb
    _ ≤ 9 := by simp; omega

theorem wordDiamond_neighbor_iff {L N : ℕ} (e d : WordBasicEdge L N) :
    d ∈ wordDiamondNeighbors e ↔ d ≠ e ∧ wordDiamondAdjacent e d := by
  simp only [wordDiamondNeighbors, Finset.mem_biUnion, Finset.mem_erase,
    wordDiamondIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
    wordDiamondEdges, Finset.mem_image]
  constructor
  · rintro ⟨v, ⟨i, hi⟩, hd, j, hj⟩
    exact ⟨hd, v, i, j, hi, hj⟩
  · rintro ⟨hd, v, i, j, hi, hj⟩
    exact ⟨v, ⟨i, hi⟩, hd, j, hj⟩

end HordijkSteelThreshold
