module

public import proofs.HordijkSteelThreshold.ReversibleRecordWords
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

def splitPrefixCoordinates (M : ℕ) : Finset (List Bool × ℕ) :=
  (shortBinaryWords M).product (Finset.range (M+1))

@[simp] theorem mem_splitPrefixCoordinates (M : ℕ) (z : List Bool × ℕ) :
    z ∈ splitPrefixCoordinates M ↔ z.1.length ≤ M ∧ z.2 ≤ M := by
  simp [splitPrefixCoordinates,mem_shortBinaryWords]

/-- A record word has a literal target support strictly outside its prefix. -/
theorem record_target_support (w v : List Bool) (hw : 0 < w.length) (hv : 0 < v.length) :
    ∃ T : Finset (List Bool × ℕ), T.card ≤ v.length+1 ∧
      Disjoint (splitPrefixCoordinates w.length) T ∧
      ∀ field : InfiniteSplitEnvironment,
        FiniteReversibleGenerated w.length 2 field w →
        (∀ z ∈ T, field z.1 z.2) → InfiniteReversibleGenerated 2 field v := by
  let N := w.length+v.length
  obtain ⟨S,hsize,hband,hgen⟩ := target_trial_support (N := N) w v hw hv le_rfl
  let T := S.image literalSplitCoordinate
  refine ⟨T,(Finset.card_image_le).trans hsize,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    have hl := (mem_splitPrefixCoordinates w.length (literalSplitCoordinate r)).mp hz
    have hb := (hband r hr).1
    change (moleculeWord (reactionProduct r)).length ≤ w.length ∧ _ at hl
    rw [moleculeWord_length] at hl
    omega
  · intro field hrecord hopen
    have hgN := finiteReversibleGenerated_mono_cap (show w.length ≤ N by dsimp [N]; omega) hrecord
    obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgN
    have hs : S ⊆ restrictedSplitReactions N field := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hopen (literalSplitCoordinate r)
        (Finset.mem_image.mpr ⟨r,hr,rfl⟩)⟩
    obtain ⟨y,hy,hev⟩ := hgen (restrictedSplitReactions N field) hs x hx he
    rw [← hev]
    exact finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible field y hy)

end HordijkSteelThreshold
