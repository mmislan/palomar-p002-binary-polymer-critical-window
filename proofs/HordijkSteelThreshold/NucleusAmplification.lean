module

public import proofs.HordijkSteelThreshold.AmbientIndependence
public import proofs.RAF.Probability.UniformCatalysis

@[expose] public section

namespace HordijkSteelThreshold

open Filter Topology
open RAF.Polymer

/-- Concatenation codes arising from a pair of finite word languages. The
mixed-radix encoding is injective, so no pair mass is lost at a fixed split. -/
def concatPairCodeImage {i j : Nat} (A : Finset (Word i)) (B : Finset (Word j)) :
    Finset (Fin (2 ^ i * 2 ^ j)) :=
  (A.product B).map finProdFinEquiv.toEmbedding

theorem card_concatPairCodeImage {i j : Nat} (A : Finset (Word i))
    (B : Finset (Word j)) :
    (concatPairCodeImage A B).card = A.card * B.card := by
  simp [concatPairCodeImage]

/-- Probability that at least one of `k` independent reaction candidates is
open when each candidate is Bernoulli(`q`). -/
noncomputable def someSplitOpenProbability (q : ℝ) (k : Nat) : ℝ :=
  1 - RAF.Probability.allAbsentProbability q k

theorem someSplitOpenProbability_eq (q : ℝ) (k : Nat) :
    someSplitOpenProbability q k = 1 - (1 - q) ^ k := by
  simp [someSplitOpenProbability, RAF.Probability.allAbsentProbability_eq_pow]

/-- Any fixed finite ambient nucleus has strictly positive probability. -/
theorem finiteNucleusProbability_pos {q : ℝ} (hq : 0 < q) (k : Nat) :
    0 < q ^ k := by
  positivity

/-- Once a complete layer supplies an unbounded number of independent split
candidates for each next-shell word, its one-shell failure probability tends
to zero at every positive ambient intensity. -/
theorem someSplitOpenProbability_tendsto_one {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    Tendsto (someSplitOpenProbability q) atTop (nhds 1) := by
  rw [show (someSplitOpenProbability q) = fun k => 1 - (1 - q) ^ k by
    funext k
    exact someSplitOpenProbability_eq q k]
  have hbase_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hbase_lt_one : 1 - q < 1 := sub_lt_self 1 hq
  have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa using hone.sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt_one)

end HordijkSteelThreshold
