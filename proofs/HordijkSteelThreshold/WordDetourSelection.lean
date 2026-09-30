module

public import proofs.HordijkSteelThreshold.DisjointDetourSelection
public import proofs.HordijkSteelThreshold.WordDetourSource

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordContourDetours {L N : ℕ} (w : ℕ)
    (C : Finset (WordBasicEdge L N)) : Finset (WordShortKey L N w) :=
  C.product Finset.univ

@[simp] theorem wordContourDetours_card {L N w : ℕ} (C : Finset (WordBasicEdge L N)) :
    (wordContourDetours w C).card = w*C.card := by
  simp [wordContourDetours, Nat.mul_comm]

theorem wordContour_disjoint_detours {L N w : ℕ} (hL : 2*w ≤ L)
    (C : Finset (WordBasicEdge L N)) :
    ∃ T ⊆ wordContourDetours w C,
      (∀ d ∈ T, ∀ e ∈ T, d ≠ e →
        Disjoint (wordDetourSourceReactions hL d) (wordDetourSourceReactions hL e)) ∧
      w*C.card ≤ 5*T.card := by
  classical
  obtain ⟨T, hT, hd, hc⟩ := exists_disjoint_detours (wordContourDetours w C)
    (wordDetourSourceReactions hL)
    (fun d _ => wordDetourSourceReactions_card hL d) (by
      intro a
      have hsub : ((wordContourDetours w C).filter (fun d =>
          a ∈ wordDetourSourceReactions hL d)) ⊆
          (Finset.univ.filter (fun d => a ∈ wordDetourSourceReactions hL d)) := by
        intro d hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩
      convert (Finset.card_le_card hsub).trans (wordDetourSourceReactions_incidence hL a) using 1
      congr 1
      ext d
      simp)
  exact ⟨T, hT, hd, by simpa only [wordContourDetours_card] using hc⟩

end HordijkSteelThreshold
