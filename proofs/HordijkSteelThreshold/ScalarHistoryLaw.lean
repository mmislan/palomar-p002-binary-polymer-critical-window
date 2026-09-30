module

public import proofs.HordijkSteelThreshold.HistoryProductLaw
public import proofs.HordijkSteelThreshold.PeelingHistory

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Every decreasing finite Boolean history has a bounded death index. -/
theorem exists_history_death (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    ∃ d ≤ T + 1, ∀ t ≤ T, P t ↔ t < d := by
  classical
  by_cases h : ∃ t, t ≤ T ∧ ¬ P t
  · refine ⟨Nat.find h, (Nat.find_spec h).1.trans (Nat.le_succ T), ?_⟩
    intro t ht
    constructor
    · intro hp
      by_contra hn
      exact (Nat.find_spec h).2 (hP (Nat.find h) t (by omega) hp)
    · intro ht'
      by_contra hn
      exact (Nat.find_min h ht') ⟨ht, hn⟩
  · refine ⟨T + 1, le_rfl, ?_⟩
    intro t ht
    exact ⟨fun _ => by omega, fun _ => by
      by_contra hn
      exact h ⟨t, ht, hn⟩⟩

noncomputable def catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) : Finset (Reaction n) := by
  classical
  exact Finset.univ.filter (catalystPoolOpen ω C)

@[simp] theorem mem_catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) :
    r ∈ catalystActive ω C ↔ catalystPoolOpen ω C r := by
  classical
  simp [catalystActive]

theorem catalystActive_mono {n : ℕ} (ω : AmbientCoord n → Prop) :
    Monotone (catalystActive ω) := by
  intro C D h r hr
  obtain ⟨x, hx, hω⟩ := (mem_catalystActive ω C r).mp hr
  exact (mem_catalystActive ω D r).mpr ⟨x, h hx, hω⟩

/-- Convert a prescribed process history into fixed column constraints.
The transform can be identity (source) or cardinality-indexed prefixes. -/
theorem peeling_event_eq_column_histories {n : ℕ}
    (transform : Finset (Molecule n) → Finset (Molecule n))
    (closure : Finset (Reaction n) → Finset (Molecule n))
    (history : ℕ → Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r t, t ≤ T → (r ∈ history t ↔ t < death r)) :
    {ω : AmbientCoord n → Prop | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (transform C)) closure t = history t} =
    {ω | ∀ r ∈ (Finset.univ : Finset (Reaction n)),
      catalystColumnHistory ω (fun t => transform (prescribedPoolAt closure history t))
        r T (death r)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, peeling_history_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h r t ht
    rw [← hdeath r t ht, ← h t ht, mem_catalystActive]
  · intro h t ht
    apply Finset.ext
    intro r
    rw [mem_catalystActive]
    exact (h r t ht).trans (hdeath r t ht).symm

/-- The source process and its ordered-initialSegment replacement give exactly the
same probability to every prescribed decreasing active-set history.
The initialSegment assumptions are deterministic; adaptive independence is not assumed. -/
theorem peeling_history_probability_eq_prefix {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset (Molecule n)) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card (Molecule n), (initialSegment k).card = k)
    (history : ℕ → Finset (Reaction n)) (hhistory : Antitone history) (T : ℕ) :
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
  classical
  have hd : ∀ r : Reaction n, ∃ d ≤ T + 1,
      ∀ t ≤ T, r ∈ history t ↔ t < d := by
    intro r
    exact exists_history_death (fun t => r ∈ history t) T
      (fun _ _ hab hr => hhistory hab hr)
  choose death hbound hpattern using hd
  have he := peeling_event_eq_column_histories (n := n) id closure history T death hpattern
  have hp := peeling_event_eq_column_histories (n := n)
    (fun C => initialSegment C.card) closure history T death hpattern
  change {ω | ∀ t ≤ T, peelingActiveAt (catalystActive ω) closure t = history t} =
      {ω | ∀ r ∈ (Finset.univ : Finset (Reaction n)),
        catalystColumnHistory ω (prescribedPoolAt closure history) r T (death r)} at he
  rw [he, hp]
  have hc := prescribedPoolAt_antitone closure hclosure history hhistory
  apply measure_catalystHistories_eq_of_card lambda _ _ hc
  · intro a b hab
    exact hprefix (Finset.card_le_card (hc hab))
  · intro t
    exact (hcard _ (Finset.card_le_univ _)).symm
  · intro r _
    exact hbound r

theorem history_clamp_antitone_of_match {R : Type*}
    (A H : ℕ → Finset R) (hA : Antitone A) (T : ℕ)
    (hmatch : ∀ t ≤ T, A t = H t) :
    Antitone (fun t => H (min t T)) := by
  intro a b hab
  change H (min b T) ⊆ H (min a T)
  rw [← hmatch (min b T) (min_le_right _ _),
    ← hmatch (min a T) (min_le_right _ _)]
  exact hA (min_le_min_right T hab)

/-- Equality for arbitrary prescribed histories. Nondecreasing histories on
the finite horizon have probability zero for both processes. -/
theorem peeling_history_probability_eq_prefix_any {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset (Molecule n)) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card (Molecule n), (initialSegment k).card = k)
    (history : ℕ → Finset (Reaction n)) (T : ℕ) :
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
  classical
  by_cases hg : Antitone (fun t => history (min t T))
  · have h := peeling_history_probability_eq_prefix lambda closure hclosure
      initialSegment hprefix hcard (fun t => history (min t T)) hg T
    have he (A : ℕ → Finset (Reaction n)) :
        (∀ t ≤ T, A t = history (min t T)) ↔ (∀ t ≤ T, A t = history t) := by
      constructor <;> intro h t ht <;> simpa only [min_eq_left ht] using h t ht
    simpa only [he] using h
  · have hs : {ω : AmbientCoord n → Prop | ∀ t ≤ T,
        peelingActiveAt (catalystActive ω) closure t = history t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      exact hg (history_clamp_antitone_of_match _ history
        (peelingActiveAt_antitone _ closure (catalystActive_mono ω) hclosure) T h)
    have hp : {ω : AmbientCoord n → Prop | ∀ t ≤ T,
        peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hm : Monotone (fun C : Finset (Molecule n) =>
          catalystActive ω (initialSegment C.card)) := by
        intro C D hCD
        exact catalystActive_mono ω (hprefix (Finset.card_le_card hCD))
      exact hg (history_clamp_antitone_of_match _ history
        (peelingActiveAt_antitone _ closure hm hclosure) T h)
    rw [hs, hp]

end HordijkSteelThreshold
