module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction

@[expose] public section

namespace HordijkSteelThreshold
open Classical

/-- If a derivation does not fit in B, some longer word is generated within
its own length cap. This is weaker than own-cap generation for every word. -/
theorem reversible_generated_or_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ FiniteReversibleGenerated v.length L field v := by
  induction h with
  | food hn hL => exact Or.inl (.food hn hL (hL.trans hLB))
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he
    · rcases ihv with hv | he
      · by_cases hlen : (u++v).length ≤ B
        · exact Or.inl (.ligate hu hv ho hlen)
        · have hb : B ≤ (u++v).length := by omega
          exact Or.inr ⟨u++v,by omega,.ligate
            (finiteReversibleGenerated_mono_cap hb hu)
            (finiteReversibleGenerated_mono_cap hb hv) ho le_rfl⟩
      · exact Or.inr he
    · exact Or.inr he
  | left hu hv _ ho ih =>
    rcases ih with hp | he
    · exact Or.inl (.left hu hv hp ho)
    · exact Or.inr he
  | right hu hv _ ho ih =>
    rcases ih with hp | he
    · exact Or.inl (.right hu hv hp ho)
    · exact Or.inr he

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
  induction h with
  | food _ _ hN => exact hN
  | ligate _ _ _ hN _ _ => exact hN
  | left _ _ _ _ ih => simp only [List.length_append] at ih; omega
  | right _ _ _ _ ih => simp only [List.length_append] at ih; omega

theorem unbounded_record_words {L : ℕ} {field : InfiniteSplitEnvironment}
    (h : ReversibleUnbounded L field) (B : ℕ) :
    ∃ w, B < w.length ∧ FiniteReversibleGenerated w.length L field w := by
  obtain ⟨w,hw,hg⟩ := h (max B L)
  rcases reversible_generated_or_record (Nat.le_max_right B L) hg with hf | he
  · have hl := finiteReversibleGenerated_length_le hf
    omega
  · obtain ⟨v,hv,hgen⟩ := he
    exact ⟨v,by omega,hgen⟩

end HordijkSteelThreshold
