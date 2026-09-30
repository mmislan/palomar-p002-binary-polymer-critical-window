module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def detourConflicts {I R : Type*} (S : Finset I)
    (support : I → Finset R) (i : I) : Finset I :=
  (S.erase i).filter (fun j => ¬ Disjoint (support i) (support j))

/-- Two coordinates per support and incidence three give at most four other conflicts. -/
theorem detourConflicts_card {I R : Type*} (S : Finset I) (support : I → Finset R)
    (i : I) (hi : i ∈ S) (hsize : (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    (detourConflicts S support i).card ≤ 4 := by
  classical
  have hsub : detourConflicts S support i ⊆
      (support i).biUnion (fun r => (S.filter (fun j => r ∈ support j)).erase i) := by
    intro j hj
    obtain ⟨hjS, hnot⟩ := Finset.mem_filter.mp hj
    obtain ⟨r, hri, hrj⟩ := Finset.not_disjoint_iff.mp hnot
    exact Finset.mem_biUnion.mpr ⟨r, hri, Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hjS).1, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hjS).2, hrj⟩⟩⟩
  calc
    _ ≤ ((support i).biUnion (fun r => (S.filter (fun j => r ∈ support j)).erase i)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ r ∈ support i, ((S.filter (fun j => r ∈ support j)).erase i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ support i, 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hm : i ∈ S.filter (fun j => r ∈ support j) := Finset.mem_filter.mpr ⟨hi, hr⟩
      have hc := Finset.card_erase_add_one hm
      have hu := huse r
      omega
    _ ≤ 4 := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]; omega

/-- A finite family of supports of size at most two, each coordinate used at
most three times, has a pairwise-disjoint subfamily of at least one fifth its size. -/
theorem exists_disjoint_detours {I R : Type*} (S : Finset I) (support : I → Finset R)
    (hsize : ∀ i ∈ S, (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) ∧
      S.card ≤ 5*T.card := by
  classical
  let family := S.powerset.filter (fun T =>
    decide (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) = true)
  have hempty : ∅ ∈ family := by simp [family]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, hempty⟩
  obtain ⟨hTS, hdisBool⟩ := Finset.mem_filter.mp hT
  have hdis := of_decide_eq_true hdisBool
  have hsub : T ⊆ S := Finset.mem_powerset.mp hTS
  refine ⟨T, hsub, hdis, ?_⟩
  have hcover : S ⊆ T.biUnion (fun j => insert j (detourConflicts S support j)) := by
    intro i hi
    by_cases hiT : i ∈ T
    · exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_insert_self _ _⟩
    · have hex : ∃ j ∈ T, ¬ Disjoint (support i) (support j) := by
        by_contra hn
        push Not at hn
        have hnew : insert i T ∈ family := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), ?_⟩
          apply decide_eq_true
          intro j hj k hk hne
          rcases Finset.mem_insert.mp hj with hji | hjT
          · rcases Finset.mem_insert.mp hk with hki | hkT
            · exact False.elim (hne (hji.trans hki.symm))
            · rw [hji]
              exact hn k hkT
          · rcases Finset.mem_insert.mp hk with hki | hkT
            · rw [hki]
              exact (hn j hjT).symm
            · exact hdis j hjT k hkT hne
        have hc := hmax (insert i T) hnew
        rw [Finset.card_insert_of_notMem hiT] at hc
        omega
      obtain ⟨j, hj, hij⟩ := hex
      apply Finset.mem_biUnion.mpr
      refine ⟨j, hj, Finset.mem_insert_of_mem ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨?_, hi⟩, ?_⟩
      · intro he
        exact hiT (he ▸ hj)
      · intro h
        exact hij h.symm
  calc
    S.card ≤ (T.biUnion (fun j => insert j (detourConflicts S support j))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ j ∈ T, (insert j (detourConflicts S support j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ T, 5 := by
      apply Finset.sum_le_sum
      intro j hj
      have hc := detourConflicts_card S support j (hsub hj) (hsize j (hsub hj)) huse
      exact (Finset.card_insert_le _ _).trans (by omega)
    _ = 5*T.card := by simp [Nat.mul_comm]

end HordijkSteelThreshold
