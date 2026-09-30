module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory

/-- If every disconnected pair is separated by a closed contour, vertices
outside every selected contour side belong to the same component. The source
geometry must supply the separating-contour hypothesis. -/
theorem outside_contour_sides_connected {X I : Type*}
    (reachable : X → X → Prop) (closed : I → Prop) (side : I → Set X)
    (hsep : ∀ x y, ¬ reachable x y → ∃ i, closed i ∧
      ((x ∈ side i ∧ y ∉ side i) ∨ (y ∈ side i ∧ x ∉ side i)))
    {x y : X} (hx : ∀ i, closed i → x ∉ side i)
    (hy : ∀ i, closed i → y ∉ side i) : reachable x y := by
  by_contra h
  obtain ⟨i, hi, hs⟩ := hsep x y h
  rcases hs with hs | hs
  · exact hx i hi hs.1
  · exact hy i hi hs.1

/-- Outside a bad set, every vertex reaches food; hence all lost mass is
charged to that bad set when food itself is good. Counts use actual vertices. -/
theorem card_le_bad_add_pool {X : Type*} [Fintype X] [DecidableEq X]
    (bad pool : Finset X) (hcover : ∀ x, x ∉ bad → x ∈ pool) :
    Fintype.card X ≤ bad.card + pool.card := by
  have hu : bad ∪ pool = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ bad
    · exact Finset.mem_union_left pool hx
    · exact Finset.mem_union_right bad (hcover x hx)
  calc
    Fintype.card X = (bad ∪ pool).card := by rw [hu, Finset.card_univ]
    _ ≤ bad.card + pool.card := Finset.card_union_le bad pool

/-- Expected bad mass is the sum of individual bad probabilities. No
independence of contour events or vertex indicators is assumed. -/
theorem lintegral_bad_card {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (bad : Ω → Finset X) :
    (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) = ∑ x : X, μ {ω | x ∈ bad ω} := by
  classical
  have he (ω : Ω) : ((bad ω).card : ENNReal) =
      ∑ x : X, if x ∈ bad ω then (1 : ENNReal) else 0 := by simp
  simp_rw [he]
  rw [lintegral_finsetSum Finset.univ (fun _ _ => measurable_of_finite _)]
  apply Finset.sum_congr rfl
  intro x _
  have hf : (fun ω => if x ∈ bad ω then (1 : ENNReal) else 0) =
      Set.indicator {ω | x ∈ bad ω} (fun _ => (1 : ENNReal)) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hf]
  exact lintegral_indicator_one (Set.Finite.measurableSet (Set.toFinite _))

/-- Root failure plus a first-moment mass bound. The deterministic cover
and per-vertex marginal estimates are the exact remaining source inputs. -/
theorem measure_pool_deficit_le {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [DecidableEq X]
    (μ : Measure Ω) (bad pool : Ω → Finset X) (root : X)
    (hcover : ∀ ω, root ∉ bad ω → ∀ x, x ∉ bad ω → x ∈ pool ω)
    (δ : ENNReal) (hbad : ∀ x, μ {ω | x ∈ bad ω} ≤ δ)
    (k : ℕ) (hk : 0 < k) :
    μ {ω | (pool ω).card + k ≤ Fintype.card X} ≤
      δ + (Fintype.card X : ENNReal) * δ / k := by
  have hsub : {ω | (pool ω).card + k ≤ Fintype.card X} ⊆
      {ω | root ∈ bad ω} ∪ {ω | k ≤ (bad ω).card} := by
    intro ω hω
    by_cases hr : root ∈ bad ω
    · exact Or.inl hr
    · right
      change (pool ω).card + k ≤ Fintype.card X at hω
      change k ≤ (bad ω).card
      have hc := card_le_bad_add_pool (bad ω) (pool ω) (hcover ω hr)
      omega
  have hm : μ {ω | k ≤ (bad ω).card} ≤
      (Fintype.card X : ENNReal) * δ / k := by
    have hmark := meas_ge_le_lintegral_div
      (μ := μ) (f := fun ω => ((bad ω).card : ENNReal))
      (measurable_of_finite _).aemeasurable
      (ε := (k : ENNReal)) (by exact_mod_cast Nat.ne_of_gt hk) (by simp)
    have hint : (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) ≤
        (Fintype.card X : ENNReal) * δ := by
      rw [lintegral_bad_card]
      calc
        ∑ x : X, μ {ω | x ∈ bad ω} ≤ ∑ _x : X, δ :=
          Finset.sum_le_sum (fun x _ => hbad x)
        _ = _ := by simp
    have hmark' : μ {ω | k ≤ (bad ω).card} ≤
        (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) / k := by
      simpa only [Nat.cast_le] using hmark
    exact hmark'.trans (ENNReal.div_le_div_right hint _)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hbad root) hm))

end HordijkSteelThreshold
