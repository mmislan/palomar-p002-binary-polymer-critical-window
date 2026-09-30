module

public import proofs.HordijkSteelThreshold.WordDetourSelection
public import proofs.HordijkSteelThreshold.DisjointDetourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

/-- All w detours for every edge of the fixed contour fail. -/
def contourDetoursFailed {L N w : ℕ} {Ω : Type*} (hL : 2*w ≤ L)
    (C : Finset (WordBasicEdge L N)) (field : Reaction N → Ω → Prop) (ω : Ω) : Prop :=
  ∀ d ∈ wordContourDetours w C, detourFailed field (wordDetourSourceReactions hL d) ω

/-- Integer amplification k avoids fractional-power rounding: choose w>=5*k.
At w=5*k this is the paper exponent w*|C|/5 exactly. -/
theorem measure_contourDetoursFailed_le {L N w k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hL : 2*w ≤ L) (hk : 5*k ≤ w) (C : Finset (WordBasicEdge L N))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : Reaction N → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (ha : a ≤ 1) (hmarg : ∀ r, μ {ω | field r ω} = a) :
    μ {ω | contourDetoursFailed hL C field ω} ≤ ((1-a^2)^k)^C.card := by
  obtain ⟨T, hT, hd, hc⟩ := wordContour_disjoint_detours hL C
  have hkt : k*C.card ≤ T.card := by
    have hh := Nat.mul_le_mul_right C.card hk
    nlinarith
  calc
    _ ≤ μ {ω | ∀ d ∈ T, detourFailed field (wordDetourSourceReactions hL d) ω} := by
      apply measure_mono
      intro ω h d hdT
      exact h d (hT hdT)
    _ ≤ (1-a^2)^T.card := measure_disjoint_detours_failed_le μ field hind hmeas
      a ha hmarg (wordDetourSourceReactions hL) T hd
      (fun d _ => wordDetourSourceReactions_card hL d)
    _ ≤ (1-a^2)^(k*C.card) := pow_le_pow_of_le_one (zero_le : 0 ≤ 1-a^2)
      (tsub_le_self : 1-a^2 ≤ 1) hkt
    _ = _ := pow_mul _ _ _

/-- The literal iid static reaction field; distinct split-position IDs are coordinates. -/
noncomputable def staticReactionMeasure (N : ℕ) (a : I) : Measure (Reaction N → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable instance staticReactionMeasure_probability (N : ℕ) (a : I) :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure
  infer_instance

theorem staticReactionMeasure_indep (N : ℕ) (a : I) :
    iIndepFun (fun r (ω : Reaction N → Prop) => ω r) (staticReactionMeasure N a) := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem staticReactionMeasure_open {N : ℕ} (a : I) (r : Reaction N) :
    staticReactionMeasure N a {ω | ω r} = (toNNReal a : ENNReal) := by
  have h : staticReactionMeasure N a ((fun ω => ω r) ⁻¹' {True}) =
      (toNNReal a : ENNReal) := by
    rw [staticReactionMeasure, ← Measure.map_apply (measurable_pi_apply r)
      (MeasurableSet.singleton True), Measure.infinitePi_map_eval]
    simp [ambientCoordLaw]
  simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using h

/-- Unconditional fixed-contour failure estimate in the actual iid source field. -/
theorem staticReaction_contour_failure {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (C : Finset (WordBasicEdge L N)) (a : I) :
    staticReactionMeasure N a {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} ≤
      ((1-(toNNReal a : ENNReal)^2)^k)^C.card := by
  apply measure_contourDetoursFailed_le hL hk C (staticReactionMeasure N a)
    (fun r ω => ω r) (staticReactionMeasure_indep N a) (fun r => measurable_pi_apply r)
    (toNNReal a : ENNReal) _ (staticReactionMeasure_open a)
  exact_mod_cast a.property.2

end HordijkSteelThreshold
