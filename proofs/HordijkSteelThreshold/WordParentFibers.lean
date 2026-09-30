module

public import proofs.HordijkSteelThreshold.WordGraphCuts

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem nonroot_word_ne_nil {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : v.val ≠ [] := by
  intro h
  exact hv (Subtype.ext h)

theorem boundedFoodLeft_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodLeft u = v) :
    ∃ b : Bool, u.val = b :: v.val := by
  have he := congrArg Subtype.val hp
  change foodWordLeft L u.val = v.val at he
  have hs : ¬ u.val.length ≤ L + 1 := by
    intro h
    have hn := nonroot_word_ne_nil v hv
    simp [foodWordLeft, h] at he
    exact hn he
  rw [foodWordLeft, ite_eq_right hs] at he
  cases hu : u.val with
  | nil => simp [hu] at hs
  | cons b t =>
    refine ⟨b, ?_⟩
    simp only [hu, List.tail_cons] at he
    rw [he]

theorem boundedFoodRight_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodRight u = v) :
    ∃ b : Bool, u.val = v.val ++ [b] := by
  have he := congrArg Subtype.val hp
  change foodWordRight L u.val = v.val at he
  have hs : ¬ u.val.length ≤ L + 1 := by
    intro h
    have hn := nonroot_word_ne_nil v hv
    simp [foodWordRight, h] at he
    exact hn he
  rw [foodWordRight, ite_eq_right hs] at he
  have hu : u.val ≠ [] := by intro h; simp [h] at hs
  refine ⟨u.val.getLast hu, ?_⟩
  rw [← he]
  exact (List.dropLast_append_getLast hu).symm

/-- Only nonroot fibers are bounded: contraction gives the food root a large fiber. -/
theorem boundedFoodLeft_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodLeft u = v)).card ≤ 2 := by
  let target := (Finset.univ : Finset Bool).image (fun b => b :: v.val)
  have hc : (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodLeft u = v)).card ≤
      target.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro u hu
      obtain ⟨b, hb⟩ := boundedFoodLeft_preimage u v hv (Finset.mem_filter.mp hu).2
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩
    · intro u _ w _ h
      exact Subtype.ext h
  exact hc.trans ((Finset.card_image_le).trans (by decide))

theorem boundedFoodRight_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodRight u = v)).card ≤ 2 := by
  let target := (Finset.univ : Finset Bool).image (fun b => v.val ++ [b])
  have hc : (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodRight u = v)).card ≤
      target.card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro u hu
      obtain ⟨b, hb⟩ := boundedFoodRight_preimage u v hv (Finset.mem_filter.mp hu).2
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩
    · intro u _ w _ h
      exact Subtype.ext h
  exact hc.trans ((Finset.card_image_le).trans (by decide))

end HordijkSteelThreshold
