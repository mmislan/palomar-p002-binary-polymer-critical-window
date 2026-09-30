module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

/-- If generation ever leaves length K, its first escape fits within cap 2K.
Cleavage cannot create the first longer word. -/
theorem reversible_generated_or_escape {L K : ℕ} (hLK : L ≤ K)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated (2*K) L field w ∨
      ∃ v, K < v.length ∧ FiniteReversibleGenerated (2*K) L field v := by
  induction h with
  | food hn hL => exact Or.inl (.food hn hL (by omega))
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he
    · rcases ihv with hv | he
      · by_cases huk : u.length ≤ K
        · by_cases hvk : v.length ≤ K
          · exact Or.inl (.ligate hu hv ho (by simp only [List.length_append]; omega))
          · exact Or.inr ⟨v, by omega, hv⟩
        · exact Or.inr ⟨u, by omega, hu⟩
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

theorem reversible_escape_iff_cap {L K : ℕ} (hLK : L ≤ K)
    (field : InfiniteSplitEnvironment) :
    (∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w) ↔
      ∃ w, K < w.length ∧ FiniteReversibleGenerated (2*K) L field w := by
  constructor
  · rintro ⟨w, hw, hg⟩
    rcases reversible_generated_or_escape hLK hg with hf | he
    · exact ⟨w, hw, hf⟩
    · exact he
  · rintro ⟨w, hw, hg⟩
    exact ⟨w, hw, finiteReversibleGenerated_to_infinite hg⟩

def reversibleEscapeEvent (L K : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L field w}

theorem reversibleEscapeEvent_iff (L K : ℕ) (field : InfiniteSplitEnvironment) :
    field ∈ reversibleEscapeEvent L K ↔
      ∃ w, K+L < w.length ∧ InfiniteReversibleGenerated L field w :=
  (reversible_escape_iff_cap (by omega : L ≤ K+L) field).symm

theorem reversibleEscapeEvent_antitone (L : ℕ) : Antitone (reversibleEscapeEvent L) := by
  intro K M hKM field h
  obtain ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L M field).mp h
  exact (reversibleEscapeEvent_iff L K field).mpr ⟨w, by omega, hg⟩

theorem reversibleEscapeEvent_inter (L : ℕ) :
    (⋂ K, reversibleEscapeEvent L K) = {field | ReversibleUnbounded L field} := by
  ext field
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h K
    obtain ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L K field).mp (h K)
    exact ⟨w, by omega, hg⟩
  · intro h K
    exact (reversibleEscapeEvent_iff L K field).mpr (h (K+L))

theorem measurableSet_reversibleEscapeEvent (L K : ℕ) :
    MeasurableSet (reversibleEscapeEvent L K) := by
  have he : reversibleEscapeEvent L K = ⋃ w : List Bool,
      ⋃ (_h : K+L < w.length),
        {field | FiniteReversibleGenerated (2*(K+L)) L field w} := by
    ext field
    simp [reversibleEscapeEvent]
  rw [he]
  exact MeasurableSet.iUnion (fun w => MeasurableSet.iUnion
    (fun _ => measurableSet_finiteReversibleGenerated _ _ w))

end HordijkSteelThreshold
