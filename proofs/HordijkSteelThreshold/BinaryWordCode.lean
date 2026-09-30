module

public import proofs.RAF.Polymer.Words

@[expose] public section

namespace HordijkSteelThreshold

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode : List Bool → ℕ
  | [] => 0
  | b :: s => (if b then 2 ^ s.length else 0) + binaryWordCode s

theorem binaryWordCode_lt (s : List Bool) : binaryWordCode s < 2 ^ s.length := by
  induction s with
  | nil => simp [binaryWordCode]
  | cons b s ih =>
    cases b <;> simp only [binaryWordCode, Bool.false_eq_true, ite_false,
      ite_true, zero_add, List.length_cons, pow_succ] <;> omega

theorem binaryWordCode_append (s t : List Bool) :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  induction s with
  | nil => simp [binaryWordCode]
  | cons b s ih =>
    cases b <;> simp [binaryWordCode, ih, List.length_append, pow_add, Nat.add_mul, Nat.add_assoc]

def listWord (s : List Bool) : RAF.Polymer.Word s.length :=
  ⟨binaryWordCode s, binaryWordCode_lt s⟩

theorem binaryWordCode_append_div (s t : List Bool) :
    binaryWordCode (s ++ t) / 2 ^ t.length = binaryWordCode s := by
  rw [binaryWordCode_append, Nat.mul_comm, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (binaryWordCode_lt t), Nat.add_zero]

theorem binaryWordCode_append_mod (s t : List Bool) :
    binaryWordCode (s ++ t) % 2 ^ t.length = binaryWordCode t := by
  rw [binaryWordCode_append, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (binaryWordCode_lt t)]

/-- Exact agreement with the source mixed-radix operation, before the
length-index cast performed by `concatCode`. -/
theorem binaryWordCode_finProd (s t : List Bool) :
    (finProdFinEquiv (listWord s, listWord t)).val = binaryWordCode (s ++ t) := by
  rw [binaryWordCode_append]
  simp only [finProdFinEquiv, listWord, Equiv.coe_fn_mk]
  ring

/-- Length together with code uniquely determines the binary word. -/
theorem binaryWordCode_injective_length {s t : List Bool}
    (hlen : s.length = t.length) (hcode : binaryWordCode s = binaryWordCode t) : s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons b s ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      have hst : s.length = t.length := by simpa using hlen
      have hs := binaryWordCode_lt s
      have ht := binaryWordCode_lt t
      rw [← hst] at ht
      cases b <;> cases c <;> simp only [binaryWordCode, Bool.false_eq_true,
        ite_false, ite_true, zero_add, ← hst] at hcode
      · exact congrArg (List.cons false) (ih hst hcode)
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hst (by omega))

theorem exists_binaryWordCode (m k : ℕ) (hk : k < 2 ^ m) :
    ∃ s : List Bool, s.length = m ∧ binaryWordCode s = k := by
  induction m generalizing k with
  | zero =>
    have he : k = 0 := by simpa using hk
    exact ⟨[], rfl, he.symm⟩
  | succ m ih =>
    by_cases hlow : k < 2 ^ m
    · obtain ⟨s, hs, hc⟩ := ih k hlow
      refine ⟨false :: s, by simp [hs], ?_⟩
      simpa [binaryWordCode] using hc
    · have ht : k - 2 ^ m < 2 ^ m := by
        rw [pow_succ] at hk
        omega
      obtain ⟨s, hs, hc⟩ := ih (k - 2 ^ m) ht
      refine ⟨true :: s, by simp [hs], ?_⟩
      simp only [binaryWordCode, ite_true, hs, hc]
      omega

/-- A length-preserving bijection with the source's actual fixed-length
word type. This prevents dropping leading zeros or losing source words. -/
noncomputable def binaryListWordEquiv (m : ℕ) :
    {s : List Bool // s.length = m} ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.val, by simpa only [s.property] using binaryWordCode_lt s.val⟩)
    (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact binaryWordCode_injective_length (s.property.trans t.property.symm)
          (congrArg Fin.val h)
      · intro k
        obtain ⟨s, hs, hc⟩ := exists_binaryWordCode m k.val k.isLt
        exact ⟨⟨s, hs⟩, Fin.ext hc⟩)

end HordijkSteelThreshold
