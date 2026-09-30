module

public import proofs.HordijkSteelThreshold.WordShortAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem nonfood_label_preimage {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) (hs : s ∈ actualBinaryWords N)
    (hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N)) :
    ∃ u : BoundedFoodWord L N, u.val = s ∧ f u ≠ f (boundedFoodRoot L N) := by
  obtain ⟨hsnil, hN⟩ := (mem_actualBinaryWords s N).mp hs
  have hL : L < s.length := by
    by_contra h
    exact hn (by simp [boundedWordLabel, hsnil, h])
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨hL, hN⟩⟩
  refine ⟨u, rfl, ?_⟩
  rwa [← boundedWordLabel_eq f u]

/-- The complement of the molecular food side is exactly the list image of the nonfood vertices. -/
theorem molecular_food_complement {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N)) =
      (wordNonfoodSide f).image Subtype.val := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsU, hsF⟩ := Finset.mem_sdiff.mp hs
    have hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N) := by
      intro h
      exact hsF (Finset.mem_filter.mpr ⟨hsU, h⟩)
    obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hsU hn
    exact Finset.mem_image.mpr ⟨u,
      (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N))
        (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _).mpr
          ⟨Finset.mem_univ u, hn⟩, hu⟩
  · intro hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    have hn := (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N))
      (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2
    have hnil : u.val ≠ [] := by
      intro h
      exact hn (congrArg f (show u = boundedFoodRoot L N from Subtype.ext h))
    have hsU : u.val ∈ actualBinaryWords N :=
      (mem_actualBinaryWords u.val N).mpr ⟨hnil, boundedFoodWord_length_le u⟩
    refine Finset.mem_sdiff.mpr ⟨hsU, ?_⟩
    intro h
    have hh := (Finset.mem_filter.mp h).2
    have heq := boundedWordLabel_eq f (show BoundedFoodWord L N from u)
    exact hn (heq.symm.trans hh)

/-- Uniform molecule anchor radius for a molecularly smaller side of a connected word cut. -/
theorem wordMolecular_anchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
  by_cases hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card
  · exact wordShortAnchor_radius f e he hconn hshort c hminor s hs
  have hlong := wordLongAnchor_radius f e he hconn (by omega)
  obtain ⟨hsU, hslabel⟩ := Finset.mem_filter.mp hs
  by_cases hc : c = f (boundedFoodRoot L N)
  · rw [hc] at hminor
    have hcard : (actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N))).card =
        (wordNonfoodSide f).card := by
      rw [molecular_food_complement]
      exact Finset.card_image_of_injective (wordNonfoodSide f)
        (fun _ _ h => Subtype.ext h)
    have hp := Finset.card_sdiff_add_card_eq_card
      (show wordMolecularSide f (f (boundedFoodRoot L N)) ⊆ actualBinaryWords N from Finset.filter_subset _ _)
    rw [hcard, actualBinaryWords_card] at hp
    rw [hcard] at hminor
    exact hlong.2 (by omega) s ((mem_actualBinaryWords s N).mp hsU).2
  · have hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N) := by rw [hslabel]; exact hc
    obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hsU hn
    obtain ⟨p, hp⟩ := hlong.1 u hn
    exact ⟨p.copy hu rfl, by simpa using hp⟩

/-- Minimal word cuts supply the connectedness premise of the complete anchor theorem. -/
theorem wordBond_molecular_anchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card :=
  wordMolecular_anchor_radius f e he (fun d hd => wordBond_diamond_connected f hmin e d he hd)
    c hminor s hs

end HordijkSteelThreshold
