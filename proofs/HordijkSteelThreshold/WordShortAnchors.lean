module

public import proofs.HordijkSteelThreshold.WordMolecularCounts
public import proofs.HordijkSteelThreshold.WordLongCoreAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- A cut side counted in actual molecules, including each food word separately. -/
noncomputable def wordMolecularSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) (c : Bool) :=
  (actualBinaryWords N).filter (fun s => boundedWordLabel f s = c)

theorem wordShortAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card)
    (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
  let M := e.1.val.length + 4 * (wordGraphCut f).card
  have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
  have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ M := by
    intro d hd
    obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
    have hh := endWord_walk_length_bound p
    dsimp [M]
    omega
  have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
  have hLM : L < M := by
    rcases e.1.property with h | h
    · exact (hn (Subtype.ext h)).elim
    · dsimp [M]; omega
  have hsU : s ∈ actualBinaryWords N := (Finset.mem_filter.mp hs).1
  have hsN := ((mem_actualBinaryWords s N).mp hsU).2
  have hsM : s.length ≤ M := by
    by_cases hMN : M < N
    · have hc : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
          M ≤ u.length → M ≤ v.length → (u ∈ wordMolecularSide f c ↔ v ∈ wordMolecularSide f c) := by
        intro u hu v hv hMu hMv
        have heq := highBand_label_constant (boundedWordLabel f) M N hMN
          (wordCut_above_boundary_parents f hLM hcut) u v
          ⟨hMu, ((mem_actualBinaryWords u N).mp hu).2⟩
          ⟨hMv, ((mem_actualBinaryWords v N).mp hv).2⟩
        simp only [wordMolecularSide, Finset.mem_filter, hu, hv, true_and]
        rw [heq]
      exact (molecular_minor_side_below_band N M hMN (wordMolecularSide f c)
        (Finset.filter_subset _ _) hminor hc s hs).le
    · omega
  obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val []
    ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
  simp only [List.length_nil, mul_zero, add_zero] at hp
  refine ⟨p, ?_⟩
  dsimp [M] at hsM
  omega

end HordijkSteelThreshold
