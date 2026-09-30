module

public import proofs.HordijkSteelThreshold.WordContourMarginals

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer

/-- Project an actual molecule to the finite graph, contracting all food words. -/
noncomputable def molecularWordVertex (L N : ℕ) (s : List Bool) : BoundedFoodWord L N :=
  if h : L < s.length ∧ s.length ≤ N then ⟨s, Or.inr h⟩ else boundedFoodRoot L N

theorem molecularWordVertex_label {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) : f (molecularWordVertex L N s) = boundedWordLabel f s := by
  by_cases hs : s = []
  · subst s
    simp [molecularWordVertex, boundedWordLabel, boundedFoodRoot]
  · by_cases h : L < s.length ∧ s.length ≤ N
    · simp [molecularWordVertex, boundedWordLabel, hs, h]
    · simp [molecularWordVertex, boundedWordLabel, hs, h]

noncomputable def wordEffectiveEdges {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (WordBasicEdge L N) :=
  (wordBasicEdges L N).filter (fun e => ∃ j : Fin w,
    ∀ a ∈ wordDetourSourceReactions hL (e,j), ω a)

theorem wordEffective_disabled_cut {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (C : Finset (WordBasicEdge L N))
    (hC : C ⊆ wordBasicEdges L N \ wordEffectiveEdges hL ω) :
    contourDetoursFailed hL C (fun r ω => ω r) ω := by
  intro d hd hopen
  obtain ⟨he, _⟩ := Finset.mem_product.mp hd
  obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp (hC he)
  apply hn
  apply Finset.mem_filter.mpr
  exact ⟨hb, d.2, hopen⟩

theorem wordMolecularSide_complement_of_ne {L N : ℕ}
    (f : BoundedFoodWord L N → Bool) (c d : Bool) (hcd : c ≠ d) :
    actualBinaryWords N \ wordMolecularSide f c = wordMolecularSide f d := by
  ext s
  cases c <;> cases d <;> cases hs : boundedWordLabel f s <;>
    simp_all [wordMolecularSide]

/-- Outside the bad contour envelopes, actual molecules belong to the same
effective component. The proof uses weighted smaller sides, including food. -/
theorem outside_moleculeContourBad_connected {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s t : List Bool)
    (hs : s ∈ actualBinaryWords N) (ht : t ∈ actualBinaryWords N)
    (hsg : ¬ moleculeContourBad hL s ω) (htg : ¬ moleculeContourBad hL t ω) :
    indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
      (molecularWordVertex L N s) (molecularWordVertex L N t) := by
  by_contra hn
  obtain ⟨f, hneq, hcut, hnonempty, hmin⟩ := wordGraph_disabled_bond L N
    (wordEffectiveEdges hL ω) (molecularWordVertex L N s) (molecularWordVertex L N t) hn
  rw [molecularWordVertex_label f s, molecularWordVertex_label f t] at hneq
  have hfailed := wordEffective_disabled_cut hL ω (wordGraphCut f) hcut
  have hsc : s ∈ wordMolecularSide f (boundedWordLabel f s) :=
    Finset.mem_filter.mpr ⟨hs, rfl⟩
  have htc : t ∈ wordMolecularSide f (boundedWordLabel f t) :=
    Finset.mem_filter.mpr ⟨ht, rfl⟩
  have hnotS : ¬ (wordMolecularSide f (boundedWordLabel f s)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f s)).card := by
    intro hminor
    exact hsg (wordBond_smaller_side_bad hL f hmin hnonempty _ hminor s hsc ω hfailed)
  have hnotT : ¬ (wordMolecularSide f (boundedWordLabel f t)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f t)).card := by
    intro hminor
    exact htg (wordBond_smaller_side_bad hL f hmin hnonempty _ hminor t htc ω hfailed)
  rw [wordMolecularSide_complement_of_ne f _ _ hneq] at hnotS
  rw [wordMolecularSide_complement_of_ne f _ _ hneq.symm] at hnotT
  omega

end HordijkSteelThreshold
