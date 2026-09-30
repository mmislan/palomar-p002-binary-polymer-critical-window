module

public import proofs.HordijkSteelThreshold.TransitionConsequences
public import proofs.HordijkSteelThreshold.InfiniteClosureDichotomy

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem rafProbability_mono (n : ℕ) {a b : ℝ} (h : a ≤ b) :
    rafProbability n a ≤ rafProbability n b :=
  ENNReal.toReal_mono (measure_ne_top _ _) (canonical_raf_measure_mono n h)

theorem sublinear_regime {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => rafProbability n (v n)) atTop (𝓝 0) := by
  let l : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hl (k : ℕ) : 0 < l k := by dsimp [l]; positivity
  have ht := transitionLimit_zero hl (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall (fun n => hc.trans_le measureReal_nonneg)
  · intro c hc
    obtain ⟨k,hk⟩ := (ht.eventually_lt_const hc).exists
    filter_upwards [(rafProbability_tendsto_transitionLimit (l k) (hl k)).eventually_lt_const hk,
      hv.eventually_lt_const (hl k)] with n hn hvn
    exact (rafProbability_mono n hvn.le).trans_lt hn

theorem all_open_complete (field : InfiniteSplitEnvironment) (h : ∀ w k, field w k) :
    CompleteReversibleClosure field := by
  intro w
  induction w with
  | nil => simp
  | cons b w ih =>
    intro _
    cases w with
    | nil => exact .food (by simp) (by simp)
    | cons c w =>
      exact InfiniteReversibleGenerated.ligate
        (u := [b]) (.food (by simp) (by simp)) (ih (by simp)) (h _ _)

theorem staticSurvival_one : staticSurvival (1 : I) = 1 := by
  have hcoord (z : List Bool × ℕ) : ∀ᵐ ω ∂infiniteSplitPi 1, ω z := by
    have he : (infiniteSplitPi 1).map (fun ω => ω z) = ambientCoordLaw 1 := by
      exact Measure.infinitePi_map_eval _ _
    have hh : ∀ᵐ p ∂ambientCoordLaw (1 : I), p := by simp [ambientCoordLaw]
    rw [← he] at hh
    exact (ae_map_iff (measurable_pi_apply z).aemeasurable (measurableSet_setOfPred.mpr measurable_id)).mp hh
  have hall : ∀ᵐ ω ∂infiniteSplitPi 1, ∀ z, ω z := ae_all_iff.mpr hcoord
  have hs : ∀ᵐ field ∂infiniteStaticMeasure 1, ReversibleUnbounded 2 field := by
    rw [infiniteStaticMeasure,ae_map_iff measurable_currySplitField.aemeasurable
      (measurableSet_reversibleUnbounded 2)]
    exact hall.mono (fun ω h => completeClosure_unbounded (all_open_complete _ (fun w k => h (w,k))))
  have hz : infiniteStaticMeasure 1 {field | ¬ ReversibleUnbounded 2 field} = 0 := ae_iff.mp hs
  have he := measure_compl (measurableSet_reversibleUnbounded 2) (measure_ne_top (infiniteStaticMeasure 1) _)
  change infiniteStaticMeasure 1 {field | ReversibleUnbounded 2 field} = 1
  have hc : infiniteStaticMeasure 1 {field | ReversibleUnbounded 2 field}ᶜ = 0 := hz
  rw [hc,measure_univ] at he
  exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.mp he.symm)

theorem transitionLimit_infinity {u : ℕ → ℝ} (hu : ∀ n, 0 < u n)
    (ht : Tendsto u atTop atTop) :
    Tendsto (fun n => transitionLimit (u n) (hu n)) atTop (𝓝 1) := by
  have he : Tendsto (fun n => Real.exp (-u n)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
  have hop : Tendsto (fun n => transitionOpenness (u n) (hu n)) atTop (𝓝 (1 : I)) := by
    apply tendsto_subtype_rng.mpr
    simpa [transitionOpenness] using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hs := staticSurvival_tendsto (a := (1 : I)) (by norm_num) hop
  rw [staticSurvival_one] at hs
  change Tendsto (fun n => (staticSurvival (transitionOpenness (u n) (hu n))).toReal)
    atTop (𝓝 1)
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ∞)).comp hs
  change Tendsto (fun n => (staticSurvival (transitionOpenness (u n) (hu n))).toReal)
    atTop (𝓝 ((1 : ENNReal).toReal)) at hreal
  norm_num at hreal
  exact hreal

theorem superlinear_regime {v : ℕ → ℝ} (hv : Tendsto v atTop atTop) :
    Tendsto (fun n => rafProbability n (v n)) atTop (𝓝 1) := by
  let l : ℕ → ℝ := fun k => (k : ℝ)+1
  have hl (k : ℕ) : 0 < l k := by dsimp [l]; positivity
  have ht := transitionLimit_infinity hl (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨k,hk⟩ := (ht.eventually_const_lt hc).exists
    filter_upwards [(rafProbability_tendsto_transitionLimit (l k) (hl k)).eventually_const_lt hk,
      (tendsto_atTop.mp hv) (l k)] with n hn hvn
    exact hn.trans_le (rafProbability_mono n hvn)
  · intro c hc
    exact Eventually.of_forall (fun n => (show rafProbability n (v n) ≤ 1 from measureReal_le_one).trans_lt hc)

end HordijkSteelThreshold
