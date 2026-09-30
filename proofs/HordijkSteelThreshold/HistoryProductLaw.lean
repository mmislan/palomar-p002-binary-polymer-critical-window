module

public import proofs.HordijkSteelThreshold.NestedColumnHistory
public import proofs.HordijkSteelThreshold.ColumnEventProduct

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Exact column weight, including initially absent and horizon-surviving
columns. Only cardinalities of deterministic nested pools enter. -/
noncomputable def columnHistoryWeight (q : ENNReal) (sizes : ℕ → ℕ) (T d : ℕ) : ENNReal :=
  if d = 0 then q ^ sizes 0
  else if T < d then 1 - q ^ sizes T
  else q ^ sizes d - q ^ sizes (d - 1)

theorem measure_catalystColumnHistory {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (T d : ℕ) (hd : d ≤ T + 1) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T d} =
      columnHistoryWeight (toNNReal (σ (catalysisP n lambda)))
        (fun t => (C t).card) T d := by
  by_cases hz : d = 0
  · subst d
    simpa only [columnHistoryWeight, ite_true] using
      measure_catalystColumnHistory_zero lambda C hC r T
  · by_cases hs : T < d
    · have hd' : d = T + 1 := by omega
      subst d
      simpa only [columnHistoryWeight, ite_eq_right hz, ite_eq_left hs] using
        measure_catalystColumnHistory_survives lambda C hC r T
    · simpa only [columnHistoryWeight, ite_eq_right hz, ite_eq_right hs] using
        measure_catalystColumnHistory_dies lambda C hC r T d (by omega) (by omega)

/-- Probability of an entire fixed nested-pool history, with independent
reaction columns but no independence assumption between time steps. -/
theorem measure_catalystHistories {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C)
    (S : Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r ∈ S, death r ≤ T + 1) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ∏ r ∈ S, columnHistoryWeight (toNNReal (σ (catalysisP n lambda)))
        (fun t => (C t).card) T (death r) := by
  have hp := measure_columnEvents lambda
    (fun r v => decreasingHistory (fun t => ∃ x ∈ C t, v x) T (death r)) S
  change ambientPiMeasure n lambda
      {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ∏ r ∈ S, ambientPiMeasure n lambda
        {ω | catalystColumnHistory ω C r T (death r)} at hp
  rw [hp]
  exact Finset.prod_congr rfl (fun r hr =>
    measure_catalystColumnHistory lambda C hC r T (death r) (hdeath r hr))

/-- Cardinality-preserving replacement of deterministic nested pools leaves
every complete column history probability unchanged. This is the source-side
identity required to replace prescribed pools by ordered prefixes. -/
theorem measure_catalystHistories_eq_of_card {n : ℕ} (lambda : ℝ)
    (C D : ℕ → Finset (Molecule n)) (hC : Antitone C) (hD : Antitone D)
    (hcard : ∀ t, (C t).card = (D t).card)
    (S : Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r ∈ S, death r ≤ T + 1) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω D r T (death r)} := by
  rw [measure_catalystHistories lambda C hC S T death hdeath,
    measure_catalystHistories lambda D hD S T death hdeath]
  have hf : (fun t => (C t).card) = (fun t => (D t).card) := funext hcard
  rw [hf]

end HordijkSteelThreshold
