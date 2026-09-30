module

public import proofs.HordijkSteelThreshold.WordEndPaths
public import proofs.HordijkSteelThreshold.WordCoreSideVolume

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- The long-core branch of molecule anchoring, with explicit molecular food-side weight.
Padding r yields a 5r nonfood path or a (12r+4) path when food is the smaller side. -/
theorem wordLongCore_anchors {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (core left right : List Bool) (hne : core ≠ [])
    (ha : e.1.val = left ++ core ++ right) (r : ℕ)
    (hl : left.length = r) (hr : right.length = r)
    (hpad : 4 * ((wordGraphCut f).card - 1) ≤ r) :
    (∀ v : BoundedFoodWord L N, f v ≠ f (boundedFoodRoot L N) →
      ∃ p : endWordGraph.Walk v.val e.1.val, p.length ≤ 5 * r) ∧
    (((2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) →
      ∀ s : List Bool, s.length ≤ N →
        ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 12 * r + 4) := by
  have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
  have hcore : ∀ d ∈ wordGraphCut f, ∃ a b : List Bool, d.1.val = a ++ core ++ b := by
    intro d hd
    exact wordContour_protected_core (wordGraphCut f) hsub e he hconn core left right ha
      (by omega) (by omega) d hd
  have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ e.1.val.length + r := by
    intro d hd
    obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
    have hh := endWord_walk_length_bound p
    omega
  have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
  have hL : L < e.1.val.length := by
    rcases e.1.property with h | h
    · exact (hn (Subtype.ext h)).elim
    · exact h.1
  have hLM : L < e.1.val.length + r := by omega
  have hlen : e.1.val.length = core.length + 2 * r := by
    have h := congrArg List.length ha
    simp only [List.length_append] at h
    omega
  constructor
  · intro v hv
    have hvc := wordCut_nonfood_side_contains_core f core hcore v hv
    have hvl := wordCut_nonfood_length_le f hLM hcut core hne hcore v hv
    obtain ⟨p, hp⟩ := endWord_common_core_walk v.val e.1.val core hvc ⟨left, right, ha⟩
    exact ⟨p, by omega⟩
  · intro hminor s hs
    have hN := wordFoodSide_minor_cap_bound f hLM hcut core hne hcore (3 * r)
      (by omega) hminor
    have heN := boundedFoodWord_length_le e.1
    obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val []
      ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
    simp only [List.length_nil, mul_zero, add_zero] at hp
    exact ⟨p, by omega⟩

theorem word_exists_padded_core (s : List Bool) (r : ℕ) (h : 2 * r < s.length) :
    ∃ core left right : List Bool, core ≠ [] ∧ s = left ++ core ++ right ∧
      left.length = r ∧ right.length = r := by
  let left := s.take r
  let core := (s.drop r).take (s.length - 2 * r)
  let right := (s.drop r).drop (s.length - 2 * r)
  have hc : core.length = s.length - 2 * r := by
    simp only [core, List.length_take, List.length_drop]
    omega
  refine ⟨core, left, right, ?_, ?_, ?_, ?_⟩
  · intro he
    have hh := congrArg List.length he
    simp only [List.length_nil] at hh
    omega
  · simp only [left, core, right, List.append_assoc, List.take_append_drop]
  · simp only [left, List.length_take]
    omega
  · simp only [right, List.length_drop]
    omega

/-- Completed long-anchor branch: both possible smaller-side labels have radius 64b.
The second branch covers actual food molecules through arbitrary lists of length <=N. -/
theorem wordLongAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hlong : 8 * (wordGraphCut f).card < e.1.val.length) :
    (∀ v : BoundedFoodWord L N, f v ≠ f (boundedFoodRoot L N) →
      ∃ p : endWordGraph.Walk v.val e.1.val, p.length ≤ 64 * (wordGraphCut f).card) ∧
    (((2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) →
      ∀ s : List Bool, s.length ≤ N →
        ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card) := by
  obtain ⟨core, left, right, hn, ha, hl, hr⟩ :=
    word_exists_padded_core e.1.val (4 * (wordGraphCut f).card) (by omega)
  have h := wordLongCore_anchors f e he hconn core left right hn ha
    (4 * (wordGraphCut f).card) hl hr (by omega)
  have hb : 0 < (wordGraphCut f).card := Finset.card_pos.mpr ⟨e, he⟩
  constructor
  · intro v hv
    obtain ⟨p, hp⟩ := h.1 v hv
    exact ⟨p, by omega⟩
  · intro hm s hs
    obtain ⟨p, hp⟩ := h.2 hm s hs
    exact ⟨p, by omega⟩

end HordijkSteelThreshold
