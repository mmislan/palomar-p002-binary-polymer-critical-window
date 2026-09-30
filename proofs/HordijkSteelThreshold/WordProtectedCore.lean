module

public import proofs.HordijkSteelThreshold.WordContourLocality

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- One end edit consumes at most one symbol of padding on either side. -/
theorem endWord_padding_step {u v core left right : List Bool} {k : ℕ}
    (hu : u = left ++ core ++ right) (hl : k + 1 ≤ left.length)
    (hr : k + 1 ≤ right.length) (ha : endWordGraph.Adj u v) :
    ∃ l r : List Bool, v = l ++ core ++ r ∧ k ≤ l.length ∧ k ≤ r.length := by
  obtain ⟨b, h | h | h | h⟩ := ha
  · refine ⟨b :: left, right, ?_, ?_, by omega⟩
    · simp [h, hu]
    · simp only [List.length_cons]; omega
  · cases left with
    | nil => simp at hl
    | cons c t =>
      have hv := congrArg List.tail h
      simp [hu] at hv
      refine ⟨t, right, by simpa [List.append_assoc] using hv.symm, ?_, by omega⟩
      simp only [List.length_cons] at hl
      omega
  · refine ⟨left, right ++ [b], ?_, by omega, ?_⟩
    · simp [h, hu, List.append_assoc]
    · simp only [List.length_append, List.length_singleton]; omega
  · have hn : right ≠ [] := by intro he; simp [he] at hr
    have he : right = right.dropLast ++ [right.getLast hn] :=
      (List.dropLast_append_getLast hn).symm
    have hv := congrArg List.dropLast h
    rw [hu, he] at hv
    simp only [← List.append_assoc, List.dropLast_concat] at hv
    refine ⟨left, right.dropLast, hv.symm, by omega, ?_⟩
    simp only [List.length_dropLast]
    omega

/-- A central word with padding at least the walk length cannot be erased by end edits. -/
theorem endWord_walk_protects_core {u v : List Bool} (p : endWordGraph.Walk u v)
    (core left right : List Bool) (hu : u = left ++ core ++ right)
    (hl : p.length ≤ left.length) (hr : p.length ≤ right.length) :
    ∃ l r : List Bool, v = l ++ core ++ r := by
  induction p generalizing left right with
  | nil => exact ⟨left, right, hu⟩
  | @cons u v w ha p ih =>
    obtain ⟨l, r, hv, hpl, hpr⟩ := endWord_padding_step hu hl hr ha
    exact ih l r hv hpl hpr

/-- The protected-core input to contour anchoring, now for actual word contours. -/
theorem wordContour_protected_core {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (core left right : List Bool) (ha : e.1.val = left ++ core ++ right)
    (hl : 4 * (C.card - 1) ≤ left.length) (hr : 4 * (C.card - 1) ≤ right.length)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ l r : List Bool, d.1.val = l ++ core ++ r := by
  obtain ⟨p, hp⟩ := wordContour_product_locality C hsub e he hconn d hd
  exact endWord_walk_protects_core p core left right ha (hp.trans hl) (hp.trans hr)

end HordijkSteelThreshold
