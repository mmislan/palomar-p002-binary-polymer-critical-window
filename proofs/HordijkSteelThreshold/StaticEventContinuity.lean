module

public import proofs.HordijkSteelThreshold.WordContourProbability

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer unitInterval
open scoped ENNReal

noncomputable def staticAtomWeight (a : I) (P : Prop) : NNReal :=
  if P then toNNReal a else toNNReal (σ a)

theorem continuous_staticAtomWeight (P : Prop) : Continuous (fun a : I => staticAtomWeight a P) := by
  have h : Continuous (fun a : I => toNNReal a) :=
    continuous_subtype_val.subtype_mk _
  by_cases hp : P
  · simpa [staticAtomWeight, hp] using h
  · simpa [staticAtomWeight, hp, Function.comp_def] using h.comp continuous_symm

theorem ambientCoordLaw_atom (a : I) (P : Prop) :
    ambientCoordLaw a {P} = (staticAtomWeight a P : ENNReal) := by
  by_cases hp : P
  · have he : P = True := propext (iff_true_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]
  · have he : P = False := propext (iff_false_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]

theorem staticReactionMeasure_atom (N : ℕ) (a : I) (ω : Reaction N → Prop) :
    staticReactionMeasure N a {ω} = (∏ r, staticAtomWeight a (ω r) : NNReal) := by
  rw [staticReactionMeasure, Measure.infinitePi_eq_pi, Measure.pi_singleton]
  simp only [ambientCoordLaw_atom, ENNReal.ofNNReal_finsetProd]

theorem continuous_static_event_probability (N : ℕ) (E : Set (Reaction N → Prop)) :
    Continuous (fun a : I => staticReactionMeasure N a E) := by
  let F : Finset (Reaction N → Prop) := Finset.univ.filter (fun ω => ω ∈ E)
  have he (a : I) : staticReactionMeasure N a E =
      ((∑ ω ∈ F, ∏ r, staticAtomWeight a (ω r) : NNReal) : ENNReal) := by
    have hF : (F : Set (Reaction N → Prop)) = E := by ext ω; simp [F]
    rw [← hF, ← sum_measure_singleton]
    simp only [staticReactionMeasure_atom, ENNReal.ofNNReal_finsetSum]
  simp_rw [he]
  apply ENNReal.continuous_coe.comp
  apply continuous_finsetSum
  intro ω _
  apply continuous_finsetProd
  intro r _
  exact continuous_staticAtomWeight (ω r)

end HordijkSteelThreshold
