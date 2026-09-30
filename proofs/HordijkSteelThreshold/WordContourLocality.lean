module

public import proofs.HordijkSteelThreshold.WordContourCounting

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- End insertion/deletion on uncontracted words, including the empty word. -/
def endWordGraph : SimpleGraph (List Bool) where
  Adj u v := ∃ b : Bool, v = b :: u ∨ u = b :: v ∨
    v = u ++ [b] ∨ u = v ++ [b]
  symm := ⟨by
    rintro u v ⟨b, h | h | h | h⟩
    · exact ⟨b, Or.inr (Or.inl h)⟩
    · exact ⟨b, Or.inl h⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inr h))⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl h))⟩⟩
  loopless := ⟨by
    rintro u ⟨b, h | h | h | h⟩ <;>
      have hh := congrArg List.length h <;> simp at hh⟩

/-- A slot belonging to an actual edge is at most one end edit from its diamond product.
The actual-edge premise prevents a contracted-root jump. -/
theorem wordDiamondSlot_product_walk {L N : ℕ} (v : BoundedFoodWord L N) (i : Fin 4)
    (he : wordDiamondSlot v i ∈ wordBasicEdges L N) :
    ∃ p : endWordGraph.Walk (wordDiamondSlot v i).1.val v.val, p.length ≤ 1 := by
  fin_cases i
  · exact ⟨Walk.nil, Nat.zero_le 1⟩
  · exact ⟨Walk.nil, Nat.zero_le 1⟩
  · have hn : boundedFoodRight v ≠ boundedFoodRoot L N := by
      simpa [wordBasicEdges, wordDiamondSlot] using he
    obtain ⟨b, hb⟩ := boundedFoodRight_preimage v (boundedFoodRight v) hn rfl
    have ha : endWordGraph.Adj (boundedFoodRight v).val v.val :=
      ⟨b, Or.inr (Or.inr (Or.inl hb))⟩
    exact ⟨Walk.cons ha Walk.nil, Nat.le_refl _⟩
  · have hn : boundedFoodLeft v ≠ boundedFoodRoot L N := by
      simpa [wordBasicEdges, wordDiamondSlot] using he
    obtain ⟨b, hb⟩ := boundedFoodLeft_preimage v (boundedFoodLeft v) hn rfl
    have ha : endWordGraph.Adj (boundedFoodLeft v).val v.val := ⟨b, Or.inl hb⟩
    exact ⟨Walk.cons ha Walk.nil, Nat.le_refl _⟩

theorem wordDiamond_products_walk {L N : ℕ} (e d : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) (hd : d ∈ wordBasicEdges L N)
    (ha : wordDiamondAdjacent e d) :
    ∃ p : endWordGraph.Walk e.1.val d.1.val, p.length ≤ 2 := by
  obtain ⟨v, i, j, hi, hj⟩ := ha
  subst e
  subst d
  obtain ⟨p, hp⟩ := wordDiamondSlot_product_walk v i he
  obtain ⟨q, hq⟩ := wordDiamondSlot_product_walk v j hd
  refine ⟨p.append q.reverse, ?_⟩
  simp only [Walk.length_append, Walk.length_reverse]
  omega

/-- Lift a contour walk to literal end edits, paying at most two per diamond step. -/
theorem wordContour_walk_lift {L N : ℕ} {e d : WordBasicEdge L N}
    (p : (wordContourGraph L N).Walk e d) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 2 * p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, by simp⟩
  | @cons u v w huv p ih =>
    obtain ⟨q, hq⟩ := wordDiamond_products_walk u v huv.1 huv.2.1 huv.2.2.2
    obtain ⟨s, hs⟩ := ih
    refine ⟨q.append s, ?_⟩
    simp only [Walk.length_append, Walk.length_cons]
    omega

/-- Every boundary product is within 4(b-1) end edits of any chosen boundary product.
This is contour localization, not yet molecule-to-contour anchoring. -/
theorem wordContour_product_locality {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 4 * (C.card - 1) := by
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour (wordContourGraph L N) C e he
    (wordContour_crossing C hsub e hconn)
  have hdp : d ∈ p.support := by
    apply List.mem_toFinset.mp
    rw [hp]
    exact hd
  obtain ⟨q, hq⟩ := wordContour_walk_lift (p.takeUntil d hdp)
  refine ⟨q, ?_⟩
  have ht := p.length_takeUntil_le_length hdp
  omega

end HordijkSteelThreshold
