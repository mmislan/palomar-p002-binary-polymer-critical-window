module

public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace HordijkSteelThreshold

open Filter Topology
open RAF RAF.Polymer RAF.Concrete

/-- A reaction is ambient-open when at least one molecule in the complete
finite molecule universe catalyzes it.  This definition deliberately does not
assert that the catalyst lies in a reaction-set closure. -/
def AmbientOpen {n : Nat} (C : Catalysis (Molecule n) (Reaction n))
    (r : Reaction n) : Prop :=
  ∃ x, C x r

/-- The exact probability that a specified reaction has no ambient catalyst. -/
noncomputable def ambientClosedProbability (n : Nat) (lambda : ℝ) : ℝ :=
  (1 - (catalysisP n lambda : ℝ)) ^ Fintype.card (Molecule n)

noncomputable def ambientOpenProbability (n : Nat) (lambda : ℝ) : ℝ :=
  1 - ambientClosedProbability n lambda

theorem ambientLogExponent_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (Fintype.card (Molecule n) : ℝ) *
      Real.log (1 - (catalysisP n lambda : ℝ))) atTop (nhds (-lambda)) := by
  have hmass := catalysisP_mul_card_molecule_tendsto hlambda
  have hratio := log_one_sub_catalysisP_div_tendsto hlambda
  have hmul := hmass.mul hratio
  have hmul' : Tendsto
      (fun n => ((catalysisP n lambda : ℝ) * Fintype.card (Molecule n)) *
        (Real.log (1 - (catalysisP n lambda : ℝ)) /
          (catalysisP n lambda : ℝ))) atTop (nhds (-lambda)) := by
    simpa only [mul_neg, mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [catalysisP_eventually_ne_zero hlambda] with n hp
  field_simp

theorem ambientClosedProbability_tendsto_exp {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => ambientClosedProbability n lambda) atTop
      (nhds (Real.exp (-lambda))) := by
  have hexp := (Real.continuous_exp.tendsto (-lambda)).comp
    (ambientLogExponent_tendsto hlambda)
  apply hexp.congr'
  have hp_lt_one : ∀ᶠ n in atTop, (catalysisP n lambda : ℝ) < 1 :=
    (catalysisP_tendsto_zero hlambda).eventually_lt_const zero_lt_one
  filter_upwards [hp_lt_one] with n hp
  rw [ambientClosedProbability]
  have hbase : 0 < 1 - (catalysisP n lambda : ℝ) := sub_pos.mpr hp
  rw [← Real.exp_log hbase, ← Real.exp_nat_mul]
  rfl

theorem ambientOpenProbability_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => ambientOpenProbability n lambda) atTop
      (nhds (1 - Real.exp (-lambda))) := by
  exact tendsto_const_nhds.sub (ambientClosedProbability_tendsto_exp hlambda)

/-- Coordinate blocks belonging to distinct reaction identities are disjoint;
this is the finite combinatorial source of independence of ambient-open
indicators under uniform product catalysis. -/
def reactionCoordBlock {n : Nat} (r : Reaction n) :
    Set (Molecule n × Reaction n) :=
  {z | z.2 = r}

theorem reactionCoordBlock_disjoint {n : Nat} {r s : Reaction n} (hrs : r ≠ s) :
    Disjoint (reactionCoordBlock r) (reactionCoordBlock s) := by
  rw [Set.disjoint_left]
  intro z hzr hzs
  exact hrs (hzr.symm.trans hzs)

end HordijkSteelThreshold
