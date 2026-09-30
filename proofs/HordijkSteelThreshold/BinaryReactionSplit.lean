module

public import proofs.HordijkSteelThreshold.BinaryWordCode
public import proofs.RAF.Concrete.PolymerCRS

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

noncomputable def moleculeWord {n : ℕ} (x : Molecule n) : List Bool :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

theorem moleculeWord_length {n : ℕ} (x : Molecule n) :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

theorem binaryWordCode_moleculeWord {n : ℕ} (x : Molecule n) :
    binaryWordCode (moleculeWord x) = x.2.val := by
  exact congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

theorem reactionLeft_code_div {n : ℕ} (r : Reaction n) :
    (reactionLeft r).2.val = r.2.1.val / 2 ^ reactionRightLength r := by
  rfl

theorem reactionRight_code_mod {n : ℕ} (r : Reaction n) :
    (reactionRight r).2.val = r.2.1.val % 2 ^ reactionRightLength r := by
  rfl

/-- Decoding a literal source reaction gives exactly its recorded left
substring; split-position identities have not been quotiented. -/
theorem moleculeWord_reactionLeft {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionLeft r) =
      (moleculeWord (reactionProduct r)).take (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hlen : s.length = reactionProductLength r := moleculeWord_length _
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by
    rw [List.length_drop, hlen]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionLeft, List.length_take]
    change reactionLeftLength r = min (reactionLeftLength r) s.length
    rw [hlen, min_eq_left (by have h := reaction_length_add r; omega)]
  · rw [binaryWordCode_moleculeWord, reactionLeft_code_div]
    have hc := binaryWordCode_append_div (s.take (reactionLeftLength r))
      (s.drop (reactionLeftLength r))
    rw [List.take_append_drop, hdrop] at hc
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    exact hc

/-- The right endpoint is exactly the complementary source substring. -/
theorem moleculeWord_reactionRight {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionRight r) =
      (moleculeWord (reactionProduct r)).drop (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by
    rw [List.length_drop, moleculeWord_length, molLength_reactionProduct]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionRight]
    exact hdrop.symm
  · rw [binaryWordCode_moleculeWord, reactionRight_code_mod]
    have hc := binaryWordCode_append_mod (s.take (reactionLeftLength r))
      (s.drop (reactionLeftLength r))
    rw [List.take_append_drop, hdrop] at hc
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    exact hc

end HordijkSteelThreshold
