module

public import proofs.HordijkSteelThreshold.CohortConnectorProbability

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A decreasing Boolean history is on exactly before its death index.
Death zero means initially absent; death T+1 means surviving the horizon. -/
def decreasingHistory (P : ℕ → Prop) (T d : ℕ) : Prop :=
  ∀ t ≤ T, P t ↔ t < d

theorem decreasingHistory_zero_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T 0 ↔ ¬ P 0 := by
  constructor
  · intro h hp
    exact Nat.not_lt_zero 0 ((h 0 (Nat.zero_le T)).mp hp)
  · intro h t _
    constructor
    · intro hp
      exact (h (hP 0 t (Nat.zero_le t) hp)).elim
    · omega

theorem decreasingHistory_survives_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T (T + 1) ↔ P T := by
  constructor
  · intro h
    exact (h T le_rfl).mpr (Nat.lt_succ_self T)
  · intro h t ht
    exact ⟨fun _ => by omega, fun _ => hP t T ht h⟩

theorem decreasingHistory_dies_iff (P : ℕ → Prop) (T d : ℕ)
    (hd : 0 < d) (hdT : d ≤ T)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T d ↔ ¬ P d ∧ P (d - 1) := by
  constructor
  · intro h
    exact ⟨fun hp => (Nat.lt_irrefl d) ((h d hdT).mp hp),
      (h (d - 1) (by omega)).mpr (by omega)⟩
  · rintro ⟨hoff, hon⟩ t _
    constructor
    · intro hp
      by_contra h
      exact hoff (hP d t (by omega) hp)
    · intro ht
      exact hP t (d - 1) (by omega) hon

def catalystColumnHistory {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : ℕ → Finset (Molecule n)) (r : Reaction n) (T d : ℕ) : Prop :=
  decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T d

theorem catalystPoolOpen_of_antitone {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (a b : ℕ) (hab : a ≤ b) :
    catalystPoolOpen ω (C b) r → catalystPoolOpen ω (C a) r := by
  rintro ⟨x, hx, hω⟩
  exact ⟨x, hC hab hx, hω⟩

theorem measure_catalystColumnHistory_zero {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n) (T : ℕ) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T 0} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C 0).card := by
  have he : {ω | catalystColumnHistory ω C r T 0} =
      {ω | ¬ catalystPoolFamilyOpen ω (C 0) {r}} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, catalystColumnHistory,
      catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
      decreasingHistory_zero_iff (fun t => catalystPoolOpen ω (C t) r) T
        (catalystPoolOpen_of_antitone ω C hC r)
  rw [he, measure_catalystPoolFamilyClosed]
  simp

theorem measure_catalystColumnHistory_survives {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n) (T : ℕ) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T (T + 1)} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C T).card := by
  have he : {ω | catalystColumnHistory ω C r T (T + 1)} =
      {ω | catalystPoolFamilyOpen ω (C T) {r}} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, catalystColumnHistory,
      catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
      decreasingHistory_survives_iff (fun t => catalystPoolOpen ω (C t) r) T
        (catalystPoolOpen_of_antitone ω C hC r)
  rw [he, measure_catalystPoolFamilyOpen_card]
  simp

/-- The full nested history imposes only the last positive and first negative
column observations. Its exact probability depends only on those pool sizes. -/
theorem measure_catalystColumnHistory_dies {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (T d : ℕ) (hd : 0 < d) (hdT : d ≤ T) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T d} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C d).card -
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C (d - 1)).card := by
  have he : {ω | catalystColumnHistory ω C r T d} =
      {ω | cohortFamilyLost ω (C d) (C (d - 1)) {r}} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, catalystColumnHistory, cohortFamilyLost,
      catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
      decreasingHistory_dies_iff (fun t => catalystPoolOpen ω (C t) r) T d hd hdT
        (catalystPoolOpen_of_antitone ω C hC r)
  rw [he, measure_cohortFamilyLost,
    Finset.union_eq_right.mpr (hC (by omega : d - 1 ≤ d))]
  simp

end HordijkSteelThreshold
