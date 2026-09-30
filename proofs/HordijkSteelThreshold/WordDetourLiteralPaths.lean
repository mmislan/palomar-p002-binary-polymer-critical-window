module

public import proofs.HordijkSteelThreshold.WordDetourSource
public import proofs.HordijkSteelThreshold.WordDetourPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- One reversible source step after food contraction, with the other factor
explicitly supplied by food. Reaction IDs remain the literal source IDs. -/
def literalFoodEdge {N : ℕ} (L : ℕ) (S : Finset (Reaction N))
    (u v : List Bool) : Prop :=
  ∃ a ∈ S, contractFoodWord L (moleculeWord (reactionProduct a)) = u ∧
    ((molLength (reactionLeft a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionRight a)) = v) ∨
     (molLength (reactionRight a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionLeft a)) = v))

theorem wordShortSourceOption_spec {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) (hr : r.1.1 ≠ boundedFoodRoot L N) :
    ∃ a, wordShortSourceOption hL r = some a ∧
      contractFoodWord L (moleculeWord (reactionProduct a)) = wordShortStart r ∧
      ((molLength (reactionLeft a) ≤ L ∧
        contractFoodWord L (moleculeWord (reactionRight a)) = wordShortEnd r) ∨
       (molLength (reactionRight a) ≤ L ∧
        contractFoodWord L (moleculeWord (reactionLeft a)) = wordShortEnd r)) := by
  unfold wordShortSourceOption
  rw [dite_eq_right hr]
  dsimp only
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [sourceShortReaction_product, sourceWordMolecule_word, wordShortStart]
  · have hv := boundedFoodWord_nonroot_length r.1.1 hr
    have hj := r.2.isLt
    rcases r with ⟨⟨v, side⟩, j⟩
    cases side
    · left
      constructor
      · simp only [molLength_reactionLeft, sourceShortReaction_leftLength,
          sourceShortSplit, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [moleculeWord_reactionRight, sourceShortReaction_product,
          sourceShortReaction_leftLength, sourceShortSplit, Bool.false_eq_true,
          ↓reduceIte, sourceWordMolecule_word, wordShortEnd, wordDropShort]
    · right
      constructor
      · rw [← moleculeWord_length]
        simp only [moleculeWord_reactionRight, sourceShortReaction_product,
          sourceShortReaction_leftLength, sourceShortSplit, ↓reduceIte,
          sourceWordMolecule_length, sourceWordMolecule_word, List.length_drop]
        omega
      · simp only [moleculeWord_reactionLeft, sourceShortReaction_product,
          sourceShortReaction_leftLength, sourceShortSplit, ↓reduceIte,
          sourceWordMolecule_length, sourceWordMolecule_word, wordShortEnd, wordDropShort]

theorem wordDetourKeys_nonroot {L N w : ℕ} (d r : WordShortKey L N w)
    (hd : d.1.1 ≠ boundedFoodRoot L N) (hr : r ∈ wordDetourKeys d) :
    r.1.1 ≠ boundedFoodRoot L N := by
  simp only [wordDetourKeys, Finset.mem_union, Finset.mem_singleton,
    Option.mem_toFinset] at hr
  rcases hr with hr | hr
  · exact hr ▸ hd
  · exact (wordDetourLower_details d r hr).2.2.2

/-- The detour path is realized entirely by its own literal reversible source
reactions with supplied food factors. No probabilistic assumptions occur. -/
theorem wordDetourSource_reach_parent {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) (hd : d.1.1 ≠ boundedFoodRoot L N) :
    Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d))
      (wordShortStart d) (wordEdgeParent d.1).val := by
  suffices ∀ u v, indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd u v →
      Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d)) u v by
    exact this _ _ (wordDetourKeys_reach_parent d)
  intro u v path
  induction path with
  | rel u v h =>
    obtain ⟨r, hr, hu, hv⟩ := h
    obtain ⟨a, ha, hp, hf⟩ := wordShortSourceOption_spec hL r
      (wordDetourKeys_nonroot d r hd hr)
    apply Relation.EqvGen.rel
    refine ⟨a, ?_, hp.trans hu, ?_⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨r, hr, Option.mem_toFinset.mpr ha⟩
    · rcases hf with hf | hf
      · exact Or.inl ⟨hf.1, hf.2.trans hv⟩
      · exact Or.inr ⟨hf.1, hf.2.trans hv⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end HordijkSteelThreshold
