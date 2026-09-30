module

public import proofs.HordijkSteelThreshold.ConnectedContourCounting
public import proofs.HordijkSteelThreshold.WordDiamondDegree

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

def wordContourGraph (L N : ℕ) : SimpleGraph (WordBasicEdge L N) where
  Adj e d := e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧
    e ≠ d ∧ wordDiamondAdjacent e d
  symm := ⟨fun _ _ ⟨he, hd, hn, v, i, j, hi, hj⟩ => ⟨hd, he, hn.symm, v, j, i, hj, hi⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem wordContourGraph_degree (L N : ℕ) (e : WordBasicEdge L N) :
    ((wordContourGraph L N).neighborFinset e).card ≤ 9 := by
  by_cases he : e ∈ wordBasicEdges L N
  · have hs : (wordContourGraph L N).neighborFinset e ⊆ wordDiamondNeighbors e := by
      intro d hd
      obtain ⟨_, _, hn, ha⟩ := (mem_neighborFinset _ _ _).mp hd
      exact wordDiamond_neighbor_iff e d |>.mpr ⟨hn.symm, ha⟩
    exact (Finset.card_le_card hs).trans (wordDiamond_neighbors_card e he)
  · have hz : (wordContourGraph L N).neighborFinset e = ∅ := by
      ext d
      simp only [Finset.notMem_empty, iff_false]
      intro hd
      exact he ((mem_neighborFinset _ _ _).mp hd).1
    simp [hz]

theorem wordContour_crossing {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (r : WordBasicEdge L N)
    (hconn : ∀ d ∈ C, wordContourReach C r d)
    (S : Finset (WordBasicEdge L N)) (hs : S ⊆ C) (hr : r ∈ S) (hne : S ≠ C) :
    ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ (wordContourGraph L N).Adj u v := by
  by_contra h
  have closed : ∀ u ∈ C, ∀ v ∈ C, wordDiamondAdjacent u v → u ∈ S → v ∈ S := by
    intro u hu v hv ha huS
    by_contra hvS
    exact h ⟨u, huS, v, hv, hvS, hsub hu, hsub hv,
      (by intro he; subst v; exact hvS huS), ha⟩
  have inv : ∀ u v, wordContourReach C u v → (u ∈ S ↔ v ∈ S) := by
    intro u v hp
    induction hp with
    | rel u v hrel =>
      obtain ⟨hu, hv, ha⟩ := hrel
      constructor
      · exact closed u hu v hv ha
      · obtain ⟨w, i, j, hi, hj⟩ := ha
        exact closed v hv u hu ⟨w, j, i, hj, hi⟩
    | refl u => rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  apply hne
  apply Finset.Subset.antisymm hs
  intro d hd
  exact (inv r d (hconn d hd)).mp hr

noncomputable def wordAnchoredContours (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :=
  (wordBasicEdges L N).powerset.filter (fun C => C.card = b ∧ r ∈ C ∧
    ∀ d ∈ C, wordContourReach C r d)

/-- Literal indexed-edge contour count, uniform in the ambient word cap. -/
theorem wordAnchoredContours_card (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1) := by
  have h := card_connected_contours_le (wordContourGraph L N) 9 b
    (wordContourGraph_degree L N) r (wordAnchoredContours L N r b) (by
      intro C hC
      obtain ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
      exact ⟨hb, hr, wordContour_crossing C (Finset.mem_powerset.mp hpow) r hc⟩)
  simpa [pow_mul] using h

/-- Every nonempty minimal word cut containing the anchor is counted. -/
theorem wordBond_mem_anchored {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (r : WordBasicEdge L N) (hr : r ∈ wordGraphCut f) :
    wordGraphCut f ∈ wordAnchoredContours L N r (wordGraphCut f).card := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, rfl, hr, ?_⟩
  · exact Finset.filter_subset _ _
  · intro d hd
    exact wordBond_diamond_connected f hmin r d hr hd

end HordijkSteelThreshold
