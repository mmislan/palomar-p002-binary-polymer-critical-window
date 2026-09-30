module

public import proofs.HordijkSteelThreshold.ReversibleFiniteCertificates
public import proofs.HordijkSteelThreshold.TargetTrials

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      (fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r))

theorem moleculeWord_nonempty {N : ℕ} (x : Molecule N) : moleculeWord x ≠ [] := by
  have h := moleculeWord_length x
  intro he
  rw [he] at h
  simp only [List.length_nil] at h
  unfold molLength at h
  omega

theorem moleculeWord_cap {N : ℕ} (x : Molecule N) : (moleculeWord x).length ≤ N := by
  rw [moleculeWord_length]
  have h := x.1.isLt
  unfold molLength
  omega

theorem reaction_words_append {N : ℕ} (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) =
      moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]

theorem literalClosure_to_finiteReversible {N L : ℕ} (field : InfiniteSplitEnvironment)
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
  apply temporaryReactionClosure_induction (restrictedSplitReactions N field)
    (fun y => FiniteReversibleGenerated N L field (moleculeWord y)) ?_ ?_ ?_ x hx
  · intro y hy
    exact .food (moleculeWord_nonempty y) (by rwa [moleculeWord_length]) (moleculeWord_cap y)
  · intro r hr hl hh
    have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho ⊢
    apply FiniteReversibleGenerated.ligate hl hh
    · simpa only [moleculeWord_length, molLength_reactionLeft] using ho
    · rw [reaction_words_append]
      exact moleculeWord_cap _
  · intro r hr hp
    have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho hp
    have hf : field (moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r))
        (moleculeWord (reactionLeft r)).length := by
      simpa only [moleculeWord_length, molLength_reactionLeft] using ho
    exact ⟨.left (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf,
      .right (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf⟩

theorem finiteReversible_to_literalClosure {N L : ℕ} {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have split_mem (u v : List Bool) (r : Reaction N)
      (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hk : reactionLeftLength r = u.length := by
      rw [← molLength_reactionLeft, ← moleculeWord_length, hl]
    simpa only [hp, hk] using ho
  induction hw with
  | @food w hn hL hN =>
    let x := sourceWordMolecule w (List.length_pos_iff.mpr hn) hN
    exact ⟨x, temporaryReactionClosure_food S x (by simpa [x] using hL),
      sourceWordMolecule_word _ _ _⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu
    obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr (hxu ▸ moleculeWord_nonempty x))
      (List.length_pos_iff.mpr (hyv ▸ moleculeWord_nonempty y)) (by simpa using hN)
    have heL : reactionLeft r = x := moleculeWord_injective (hl.trans hxu.symm)
    have heR : reactionRight r = y := moleculeWord_injective (hr.trans hyv.symm)
    exact ⟨reactionProduct r, temporaryReactionClosure_ligation S r (split_mem u v r hl hp ho)
      (heL.symm ▸ hx) (heR.symm ▸ hy), hp⟩
  | @left u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, _, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    have he : reactionProduct r = x := moleculeWord_injective (hp.trans hxp.symm)
    exact ⟨reactionLeft r, (temporaryReactionClosure_cleavage S r
      (split_mem u v r hl hp ho) (he.symm ▸ hx)).1, hl⟩
  | @right u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    have he : reactionProduct r = x := moleculeWord_injective (hp.trans hxp.symm)
    exact ⟨reactionRight r, (temporaryReactionClosure_cleavage S r
      (split_mem u v r hl hp ho) (he.symm ▸ hx)).2, hr⟩

theorem finiteReversible_iff_literalClosure {N L : ℕ} (field : InfiniteSplitEnvironment)
    (w : List Bool) : FiniteReversibleGenerated N L field w ↔
      ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w :=
  ⟨finiteReversible_to_literalClosure,
    fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx⟩

end HordijkSteelThreshold
