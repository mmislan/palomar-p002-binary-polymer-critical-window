module

public import proofs.HordijkSteelThreshold.CriticalWindowSource
public import proofs.HordijkSteelThreshold.StaticSurvivalMonotonicity
public import Mathlib.Topology.Sequences

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem transitionLimit_eq_staticSurvival (lambda : ℝ) (h : 0 < lambda) :
    transitionLimit lambda h = (infiniteStaticMeasure (transitionOpenness lambda h)
      {field | ReversibleUnbounded 2 field}).toReal := rfl

theorem transitionLimit_mem_Ioo (lambda : ℝ) (h : 0 < lambda) :
    0 < transitionLimit lambda h ∧ transitionLimit lambda h < 1 :=
  ⟨(corrected_transition lambda h).2.1,(corrected_transition lambda h).2.2.2⟩

theorem transitionLimit_mono {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    transitionLimit x hx ≤ transitionLimit y hy := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply staticSurvival_mono
  change 1-Real.exp (-x) ≤ 1-Real.exp (-y)
  have := Real.exp_le_exp.mpr (show -y ≤ -x by linarith)
  linarith

theorem continuous_transitionLimit :
    Continuous (fun x : {x : ℝ // 0 < x} => transitionLimit x.val x.property) := by
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  have hr := continuous_subtype_val.continuousAt.tendsto.comp hu
  have hop := transitionOpenness_tendsto (fun k => (u k).property) a.property hr
  have ha : 0 < (transitionOpenness a.val a.property : ℝ) := by
    change 0 < 1-Real.exp (-a.val)
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos a.property)
    linarith
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (staticSurvival_tendsto ha hop)

theorem transitionLimit_zero {u : ℕ → ℝ} (hu : ∀ n, 0 < u n)
    (ht : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => transitionLimit (u n) (hu n)) atTop (𝓝 0) := by
  have he : Tendsto (fun n => 1-Real.exp (-36*u n)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul ht) :
        Tendsto (fun n => Real.exp (-36*u n)) atTop (𝓝 (Real.exp (-36*0))))
  exact squeeze_zero (fun n => (transitionLimit_mem_Ioo _ (hu n)).1.le)
    (fun n => (corrected_transition _ (hu n)).2.2.1) he

theorem staticSurvival_pos (a : I) (ha : 0 < (a : ℝ)) : 0 < staticSurvival a := by
  let b : I := ⟨(a : ℝ)/2, by constructor <;> nlinarith [a.property.1,a.property.2]⟩
  let l : ℝ := -Real.log (1-(b : ℝ))
  have hb : 0 < (b : ℝ) ∧ (b : ℝ) < 1 := by dsimp [b]; constructor <;> nlinarith [a.property.2]
  have hl : 0 < l := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  have hop : transitionOpenness l hl = b := by
    apply Subtype.ext
    change 1-Real.exp (-l) = (b : ℝ)
    dsimp [l]
    rw [neg_neg,Real.exp_log (by linarith)]
    ring
  have hp := (transitionLimit_mem_Ioo l hl).1
  change 0 < (staticSurvival (transitionOpenness l hl)).toReal at hp
  rw [hop] at hp
  exact (ENNReal.toReal_pos_iff.mp hp).1.trans_le
    (staticSurvival_mono (show b ≤ a from by change (a : ℝ)/2 ≤ a; linarith))

theorem no_finite_step_threshold :
    ¬ ∃ gamma : ℝ, 0 < gamma ∧
      (∀ l : ℝ, 0 < l → l < gamma → Tendsto (fun n => rafProbability n l) atTop (𝓝 0)) ∧
      (∀ l : ℝ, gamma < l → Tendsto (fun n => rafProbability n l) atTop (𝓝 1)) := by
  rintro ⟨g,hg,hlo,_⟩
  have hh : 0 < g/2 := by positivity
  have he := tendsto_nhds_unique (rafProbability_tendsto_transitionLimit (g/2) hh)
    (hlo (g/2) hh (by linarith))
  exact (ne_of_gt (transitionLimit_mem_Ioo (g/2) hh).1) he

end HordijkSteelThreshold
