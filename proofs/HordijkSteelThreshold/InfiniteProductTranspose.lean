module

public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace HordijkSteelThreshold
open MeasureTheory MeasureTheory.Measure

/-- Reorganizing independent rows as independent columns preserves the full
product law, including dependence within each eventual paired coordinate. -/
theorem infinitePi_transpose {A B X : Type*} [MeasurableSpace X]
    (μ : A → B → Measure X) [∀ a b, IsProbabilityMeasure (μ a b)] :
    (infinitePi (fun a => infinitePi (μ a))).map (fun f b a => f a b) =
      infinitePi (fun b => infinitePi (fun a => μ a b)) := by
  let U := (MeasurableEquiv.curry A B X).symm
  let S := MeasurableEquiv.piCongrLeft (fun _ : B × A => X) (Equiv.prodComm A B)
  let C := MeasurableEquiv.curry B A X
  have hu : (infinitePi (fun a => infinitePi (μ a))).map U =
      infinitePi (fun p : A × B => μ p.1 p.2) := infinitePi_map_curry_symm μ
  have hs : (infinitePi (fun p : A × B => μ p.1 p.2)).map S =
      infinitePi (fun p : B × A => μ p.2 p.1) :=
    infinitePi_map_piCongrLeft (fun p : B × A => μ p.2 p.1) (Equiv.prodComm A B)
  have hc : (infinitePi (fun p : B × A => μ p.2 p.1)).map C =
      infinitePi (fun b => infinitePi (fun a => μ a b)) :=
    infinitePi_map_curry (fun b a => μ a b)
  calc
    _ = (((infinitePi (fun a => infinitePi (μ a))).map U).map S).map C := by
      rw [map_map C.measurable S.measurable, map_map (C.measurable.comp S.measurable) U.measurable]
      rfl
    _ = _ := by rw [hu, hs, hc]

end HordijkSteelThreshold
