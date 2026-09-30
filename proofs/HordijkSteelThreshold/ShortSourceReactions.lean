module

public import proofs.HordijkSteelThreshold.BasicSourceEdges

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

/-- Arbitrary literal split, retaining its product and split-position identity. -/
def sourceSplitReaction {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨k - 1, by unfold molLength at hkm; omega⟩⟩

@[simp] theorem sourceSplitReaction_product {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionProduct (sourceSplitReaction x k hk hkm) = x := rfl

@[simp] theorem sourceSplitReaction_leftLength {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceSplitReaction x k hk hkm) = k := by
  change k - 1 + 1 = k
  omega

/-- The side indicates deletion of a short suffix (true) or prefix (false). -/
def sourceShortSplit {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ) : ℕ :=
  if side then molLength x - k else k

def sourceShortReaction {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  sourceSplitReaction x (sourceShortSplit x side k)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)

@[simp] theorem sourceShortReaction_product {n : ℕ} (x : Molecule n)
    (side : Bool) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x) :
    reactionProduct (sourceShortReaction x side k hk hkm) = x := rfl

@[simp] theorem sourceShortReaction_leftLength {n : ℕ} (x : Molecule n)
    (side : Bool) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceShortReaction x side k hk hkm) =
      sourceShortSplit x side k := sourceSplitReaction_leftLength _ _ _ _

/-- A width smaller than half the product separates the two orientations.
Thus the normalized short-edge coordinates do not create fictitious independent IDs. -/
theorem sourceShortReaction_coordinates {n w : ℕ} (x y : Molecule n)
    (sx sy : Bool) (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hkw : k ≤ w) (hlw : l ≤ w) (hx : 2*w < molLength x)
    (hy : 2*w < molLength y)
    (he : sourceShortReaction x sx k hk (by omega) =
      sourceShortReaction y sy l hl (by omega)) :
    x = y ∧ sx = sy ∧ k = l := by
  have hxy := congrArg reactionProduct he
  simp only [sourceShortReaction_product] at hxy
  subst y
  have hs := congrArg reactionLeftLength he
  simp only [sourceShortReaction_leftLength] at hs
  refine ⟨rfl, ?_⟩
  cases sx <;> cases sy <;> simp_all [sourceShortSplit] <;> omega

theorem sourceShortReaction_prefix {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    moleculeWord (reactionLeft (sourceShortReaction x false k hk hkm)) =
      (moleculeWord x).take k ∧
    moleculeWord (reactionRight (sourceShortReaction x false k hk hkm)) =
      (moleculeWord x).drop k := by
  simp only [moleculeWord_reactionLeft, moleculeWord_reactionRight,
    sourceShortReaction_product, sourceShortReaction_leftLength, sourceShortSplit,
    Bool.false_eq_true, ↓reduceIte, and_self]

theorem sourceShortReaction_suffix {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    moleculeWord (reactionLeft (sourceShortReaction x true k hk hkm)) =
      (moleculeWord x).take (molLength x-k) ∧
    moleculeWord (reactionRight (sourceShortReaction x true k hk hkm)) =
      (moleculeWord x).drop (molLength x-k) := by
  simp only [moleculeWord_reactionLeft, moleculeWord_reactionRight,
    sourceShortReaction_product, sourceShortReaction_leftLength, sourceShortSplit,
    ↓reduceIte, and_self]

end HordijkSteelThreshold
