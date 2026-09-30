module

public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

abbrev SplitField := (List Bool × ℕ) → Prop

def SplitPrefixDetermined (P : Finset (List Bool × ℕ)) (E : Set SplitField) : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

theorem split_coordinate_measure (a : I) (z : List Bool × ℕ) :
    infiniteSplitPi a {ω | ω z} = (toNNReal a : ENNReal) := by
  have he := congrArg (fun μ : Measure Prop => μ {True})
    (Measure.infinitePi_map_eval (fun _ : List Bool × ℕ => ambientCoordLaw a) z)
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at he
  simpa [infiniteSplitPi,ambientCoordLaw] using he

theorem split_support_open_measure (a : I) (T : Finset (List Bool × ℕ)) :
    infiniteSplitPi a {ω | ∀ z ∈ T, ω z} = (toNNReal a : ENNReal)^T.card := by
  have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hp := hi.measure_inter_preimage_eq_mul T
    (sets := fun _ => ({True} : Set Prop)) (fun _ _ => MeasurableSet.singleton True)
  have he : {ω : SplitField | ∀ z ∈ T, ω z} =
      ⋂ z ∈ T, (fun ω : SplitField => ω z) ⁻¹' {True} := by ext ω; simp
  rw [he,hp]
  have hs (z : List Bool × ℕ) :
      infiniteSplitPi a ((fun ω : SplitField => ω z) ⁻¹' {True}) = (toNNReal a : ENNReal) := by
    simpa using split_coordinate_measure a z
  simp only [hs,Finset.prod_const]

theorem split_prefix_event_representation (P : Finset (List Bool × ℕ)) (E : Set SplitField)
    (hE : SplitPrefixDetermined P E) :
    ∃ e : (P → Prop) → Prop, E = {ω | e (fun z => ω z.val)} := by
  let extend : (P → Prop) → SplitField := fun η z => if h : z ∈ P then η ⟨z,h⟩ else False
  refine ⟨fun η => extend η ∈ E, ?_⟩
  ext ω
  apply hE
  intro z hz
  simp [extend,hz]

theorem split_prefix_failure_measure (a : I) (P T : Finset (List Bool × ℕ))
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^T.card) := by
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have ht := hi.indepFun_finset P T hPT (fun z => measurable_pi_apply z)
  let g : (T → Prop) → Prop := fun η => ¬ ∀ z, η z
  have hind := ht.comp (measurable_of_finite e) (measurable_of_finite g)
  have hp := hind.measure_inter_preimage_eq_mul {True} {True}
    (MeasurableSet.singleton True) (MeasurableSet.singleton True)
  have hfail : infiniteSplitPi a {ω | ¬ ∀ z ∈ T, ω z} =
      1-(toNNReal a : ENNReal)^T.card := by
    have hm : MeasurableSet {ω : SplitField | ∀ z ∈ T, ω z} := by
      have hs : {ω : SplitField | ∀ z ∈ T, ω z} =
          ⋂ z ∈ T, (fun ω : SplitField => ω z) ⁻¹' {True} := by ext ω; simp
      rw [hs]
      exact MeasurableSet.iInter (fun z => MeasurableSet.iInter
        (fun _ => (MeasurableSet.singleton True).preimage (measurable_pi_apply z)))
    change infiniteSplitPi a ({ω | ∀ z ∈ T, ω z}ᶜ) = _
    rw [measure_compl hm (measure_ne_top _ _),measure_univ,split_support_open_measure]
  rw [he] at ⊢
  simp only [Function.comp_def,g,Subtype.forall,Set.preimage,
    Set.mem_singleton_iff,eq_iff_iff,iff_true] at hp
  rw [hfail] at hp
  exact hp

end HordijkSteelThreshold
