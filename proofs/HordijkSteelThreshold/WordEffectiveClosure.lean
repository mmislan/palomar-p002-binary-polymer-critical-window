module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure
public import proofs.HordijkSteelThreshold.WordRootedMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem literalFoodEdge_generated_iff {N L : ℕ} (S : Finset (Reaction N))
    {u v : List Bool} (h : literalFoodEdge L S u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v := by
  obtain ⟨r, hr, hp, hf⟩ := h
  rw [← hp, contractedWordGenerated_iff]
  rcases hf with ⟨hl, he⟩ | ⟨hh, he⟩
  · rw [← he, contractedWordGenerated_iff]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S r hr h).2,
      fun h => temporaryReactionClosure_ligation S r hr (temporaryReactionClosure_food S _ hl) h⟩
  · rw [← he, contractedWordGenerated_iff]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S r hr h).1,
      fun h => temporaryReactionClosure_ligation S r hr h (temporaryReactionClosure_food S _ hh)⟩

theorem literalFoodPath_generated_iff {N L : ℕ} (S : Finset (Reaction N))
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v := by
  induction h with
  | rel _ _ h => exact literalFoodEdge_generated_iff S h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem literalFoodPath_mono {N L : ℕ} {S T : Finset (Reaction N)} (hST : S ⊆ T)
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    Relation.EqvGen (literalFoodEdge L T) u v := by
  induction h with
  | rel u v h =>
    obtain ⟨r, hr, hp, hf⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨r, hST hr, hp, hf⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

noncomputable def staticOpenReactions {N : ℕ} (ω : Reaction N → Prop) : Finset (Reaction N) :=
  Finset.univ.filter ω

theorem wordEffective_generated_iff {L N w : ℕ} (hL : 2*w ≤ L) (ω : Reaction N → Prop)
    (e : WordBasicEdge L N) (he : e ∈ wordEffectiveEdges hL ω) :
    contractedWordGenerated L (staticOpenReactions ω) e.1.val ↔
      contractedWordGenerated L (staticOpenReactions ω) (wordEdgeParent e).val := by
  obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
  have hn : e.1 ≠ boundedFoodRoot L N := (Finset.mem_filter.mp hb).2
  have hp := wordDetourSource_reach_parent hL (e,j) hn
  have hsub : wordDetourSourceReactions hL (e,j) ⊆ staticOpenReactions ω := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj r hr⟩
  have hf := literalFoodPath_generated_iff (staticOpenReactions ω) (literalFoodPath_mono hsub hp)
  have hlen := boundedFoodWord_nonroot_length e.1 hn
  simpa only [wordShortStart, contractFoodWord, ite_eq_right (not_le.mpr hlen)] using hf

theorem wordEffective_reach_generated_iff {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) {u v : BoundedFoodWord L N}
    (h : indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent u v) :
    contractedWordGenerated L (staticOpenReactions ω) u.val ↔
      contractedWordGenerated L (staticOpenReactions ω) v.val := by
  induction h with
  | rel u v h =>
    obtain ⟨e, he, hu, hv⟩ := h
    have hi := wordEffective_generated_iff hL ω e he
    rw [hu, hv] at hi
    exact hi
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem molecularWordVertex_val {L N : ℕ} (s : List Bool) (hN : s.length ≤ N) :
    (molecularWordVertex L N s).val = contractFoodWord L s := by
  by_cases hL : s.length ≤ L
  · simp [molecularWordVertex_food s hL, contractFoodWord, hL, boundedFoodRoot]
  · simp [molecularWordVertex, not_le.mp hL, hN, contractFoodWord, hL]

noncomputable def actualWordSource {N : ℕ} (s : ActualBinaryWord N) : Molecule N :=
  sourceWordMolecule s.val (by
    have h := (mem_actualBinaryWords s.val N).mp s.property
    exact List.length_pos_iff.mpr h.1) ((mem_actualBinaryWords s.val N).mp s.property).2

@[simp] theorem actualWordSource_word {N : ℕ} (s : ActualBinaryWord N) :
    moleculeWord (actualWordSource s) = s.val := sourceWordMolecule_word _ _ _

theorem actualWordSource_injective {N : ℕ} : Function.Injective (@actualWordSource N) := by
  intro s t h
  apply Subtype.ext
  have hw := congrArg moleculeWord h
  simpa only [actualWordSource_word] using hw

/-- The rooted effective component really is contained in ordinary reversible
closure from temporary food, using only reactions open in this same field. -/
theorem rootedMolecularWords_source_mem {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s : ActualBinaryWord N) (hs : s ∈ rootedMolecularWords hL ω) :
    actualWordSource s ∈ temporaryReactionClosure L (staticOpenReactions ω) := by
  have hp := (Finset.mem_filter.mp hs).2
  have hi := wordEffective_reach_generated_iff hL ω hp
  have hg : contractedWordGenerated L (staticOpenReactions ω)
      (molecularWordVertex L N s.val).val := hi.mp (contractedWordGenerated_root _)
  rw [molecularWordVertex_val s.val ((mem_actualBinaryWords s.val N).mp s.property).2] at hg
  apply (contractedWordGenerated_iff (staticOpenReactions ω) (actualWordSource s)).mp
  simpa only [actualWordSource_word] using hg

theorem rootedMolecularWords_card_le_closure {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) :
    (rootedMolecularWords hL ω).card ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card := by
  apply Finset.card_le_card_of_injOn actualWordSource
  · exact rootedMolecularWords_source_mem hL ω
  · intro s _ t _ h
    exact actualWordSource_injective h

end HordijkSteelThreshold
