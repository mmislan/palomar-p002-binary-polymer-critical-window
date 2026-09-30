module

public import proofs.HordijkSteelThreshold.RecordTargetProbability
public import proofs.HordijkSteelThreshold.RecordPrefixAtoms

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory unitInterval
open scoped ENNReal

theorem measurableSet_of_splitPrefixDetermined (P : Finset (List Bool × ℕ))
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
  obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
  rw [he]
  have hm : Measurable (fun ω : SplitField => e (fun z : P => ω z.val)) :=
    (measurable_of_finite e).comp (Measurable.of_eval (fun z => measurable_pi_apply z.val))
  simpa using (MeasurableSet.singleton True).preimage hm

def unboundedMissingTarget (v : List Bool) : Set SplitField :=
  {ω | ReversibleUnbounded 2 (currySplitField ω) ∧
    ¬ InfiniteReversibleGenerated 2 (currySplitField ω) v}

/-- A uniform strict deficit on every finite-prefix cylinder, obtained by
summing disjoint first-record atoms rather than conditioning on survival. -/
theorem record_cylinder_deficit (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (C : Set SplitField) (hC : SplitPrefixDetermined (splitPrefixCoordinates B) C) :
    infiniteSplitPi a (unboundedMissingTarget v ∩ C) ≤
      infiniteSplitPi a C * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let D : RecordPrefixIndex → Set SplitField := fun i => C ∩ recordPrefixAtom B i
  have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
  have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
    hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (recordPrefixAtom_determined B i))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact (recordPrefixAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
  have hpiece (i : RecordPrefixIndex) :
      infiniteSplitPi a (unboundedMissingTarget v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
    by_cases hn : (D i).Nonempty
    · obtain ⟨ω,hω⟩ := hn
      have hBM : B < i.1 := hω.2.1.1
      obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i ⟨ω,hω.2⟩
      have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
        rw [hw]
        intro η ξ he
        apply and_congr
        · apply hC
          intro z hz
          have hz' := (mem_splitPrefixCoordinates B z).mp hz
          exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
        · exact recordPrefixAtom_determined B i η ξ he
      apply (measure_mono (show unboundedMissingTarget v ∩ D i ⊆
        D i ∩ {η | ¬ InfiniteReversibleGenerated 2 (currySplitField η) v}
        from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
      exact record_target_failure_bound a w v (by omega) hv (D i) hd
        (fun η hη => hrecord η hη.2)
    · have he : D i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he]
  have hcover : unboundedMissingTarget v ∩ C ⊆
      ⋃ i : RecordPrefixIndex, unboundedMissingTarget v ∩ D i := by
    intro ω hω
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (unbounded_mem_recordPrefixAtoms hω.1.1 B)
    exact Set.mem_iUnion.mpr ⟨i,hω.1,hω.2,hi⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, unboundedMissingTarget v ∩ D i) :=
      measure_mono hcover
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (unboundedMissingTarget v ∩ D i) :=
      measure_iUnion_le _
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      rw [ENNReal.tsum_mul_right,measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono (Set.iUnion_subset (fun _ => Set.inter_subset_left))) _

end HordijkSteelThreshold
