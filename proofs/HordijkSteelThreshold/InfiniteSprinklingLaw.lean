module

public import proofs.HordijkSteelThreshold.BernoulliSprinkling
public import proofs.HordijkSteelThreshold.InfiniteProductTranspose
public import proofs.HordijkSteelThreshold.RandomBaseSprinkling

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval

theorem iid_union_field_map (C : Type*) (a b : I) :
    ((Measure.infinitePi (fun _ : C => ambientCoordLaw a)).prod
      (Measure.infinitePi (fun _ : C => ambientCoordLaw b))).map
      (fun p c => p.1 c ∨ p.2 c) =
        Measure.infinitePi (fun _ : C => ambientCoordLaw (sprinklingParameter a b)) := by
  let law : Fin 2 → Measure Prop := fun i => if i = 0 then ambientCoordLaw a else ambientCoordLaw b
  have : ∀ i, IsProbabilityMeasure (law i) := by intro i; dsimp [law]; split <;> infer_instance
  let rows := Measure.infinitePi (fun i => Measure.infinitePi (fun _ : C => law i))
  have hp : rows.map (fun f => (f 0, f 1)) =
      (Measure.infinitePi (fun _ : C => ambientCoordLaw a)).prod
      (Measure.infinitePi (fun _ : C => ambientCoordLaw b)) := by
    dsimp only [rows]
    rw [Measure.infinitePi_eq_pi]
    simpa [law] using (measurePreserving_piFinTwo
      (fun i => Measure.infinitePi (fun _ : C => law i))).map_eq
  have hsingle : (Measure.infinitePi law).map (fun f => f 0 ∨ f 1) =
      ambientCoordLaw (sprinklingParameter a b) := by
    have hh := (measurePreserving_piFinTwo law).map_eq
    have hpair : (Measure.infinitePi law).map (fun f => (f 0, f 1)) =
        (ambientCoordLaw a).prod (ambientCoordLaw b) := by
      rw [Measure.infinitePi_eq_pi]
      simpa [law] using hh
    rw [← ambientCoordLaw_union a b, ← hpair,
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have ht : rows.map (fun f c i => f i c) =
      Measure.infinitePi (fun _ : C => Measure.infinitePi law) :=
    infinitePi_transpose (fun i (_ : C) => law i)
  rw [← hp, Measure.map_map (by fun_prop) (by fun_prop)]
  change rows.map (fun f c => f 0 c ∨ f 1 c) = _
  calc
    _ = (rows.map (fun f c i => f i c)).map (fun f c => f c 0 ∨ f c 1) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [ht, Measure.infinitePi_map_pi (fun _ : C => Measure.infinitePi law)
        (f := fun (_ : C) (f : Fin 2 → Prop) => f 0 ∨ f 1) (fun _ => measurable_of_finite _)]
      simp_rw [hsingle]

theorem infiniteStatic_union_map (a b : I) :
    ((infiniteStaticMeasure a).prod (infiniteStaticMeasure b)).map
      (fun p => unionSplitField p.1 p.2) =
      infiniteStaticMeasure (sprinklingParameter a b) := by
  rw [infiniteStaticMeasure, infiniteStaticMeasure, Measure.map_prod_map _ _
    measurable_currySplitField measurable_currySplitField,
    Measure.map_map measurable_unionSplitField
      (measurable_currySplitField.prodMap measurable_currySplitField)]
  change ((infiniteSplitPi a).prod (infiniteSplitPi b)).map
    (fun p => currySplitField (fun z => p.1 z ∨ p.2 z)) = _
  calc
    _ = (((infiniteSplitPi a).prod (infiniteSplitPi b)).map
        (fun p z => p.1 z ∨ p.2 z)).map currySplitField := by
      rw [Measure.map_map measurable_currySplitField (by fun_prop)]
      rfl
    _ = _ := by
      rw [infiniteSplitPi, infiniteSplitPi, iid_union_field_map]
      rfl

end HordijkSteelThreshold
