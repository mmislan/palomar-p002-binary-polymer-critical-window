module

public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import proofs.HordijkSteelThreshold.ReversibleRecordEvents

@[expose] public section

namespace HordijkSteelThreshold
open Classical

abbrev RecordPrefixIndex := Σ M : ℕ, (splitPrefixCoordinates M → Prop)

def recordPrefixAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | currySplitField ω ∈ firstRecordEvent 2 B i.1 ∧
    ∀ z : splitPrefixCoordinates i.1, ω z.val = i.2 z}

theorem recordPrefixAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (recordPrefixAtom B i) := by
  intro ω η he
  have hrec : currySplitField ω ∈ firstRecordEvent 2 B i.1 ↔
      currySplitField η ∈ firstRecordEvent 2 B i.1 := by
    apply firstRecordEvent_congr_prefix
    intro w hw k hk
    exact he (w,k) ((mem_splitPrefixCoordinates _ _).mpr ⟨hw,hk⟩)
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr hrec
  apply forall_congr'
  intro z
  rw [he z.val z.property]

theorem recordPrefixAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (recordPrefixAtom B i) (recordPrefixAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  by_cases hM : i.1 = j.1
  · have he : i = j := by
      rcases i with ⟨M,η⟩
      rcases j with ⟨N,ξ⟩
      dsimp at hM
      subst N
      congr
      funext z
      exact (hi.2 z).symm.trans (hj.2 z)
    exact hij he
  · exact Set.disjoint_left.mp (firstRecordEvent_disjoint 2 B hM) hi.1 hj.1

theorem unbounded_mem_recordPrefixAtoms {ω : SplitField}
    (h : ReversibleUnbounded 2 (currySplitField ω)) (B : ℕ) :
    ω ∈ ⋃ i : RecordPrefixIndex, recordPrefixAtom B i := by
  obtain ⟨M,hM⟩ := Set.mem_iUnion.mp (unbounded_mem_firstRecord_union h B)
  exact Set.mem_iUnion.mpr ⟨⟨M,fun z => ω z.val⟩,hM,fun _ => rfl⟩

/-- Each nonempty atom fixes a usable word, chosen pointwise from one
representative. No random measurable word selector is required. -/
theorem recordPrefixAtom_word (B : ℕ) (i : RecordPrefixIndex)
    (hne : (recordPrefixAtom B i).Nonempty) :
    ∃ w : List Bool, w.length = i.1 ∧ B < w.length ∧
      ∀ ω ∈ recordPrefixAtom B i,
        FiniteReversibleGenerated w.length 2 (currySplitField ω) w := by
  obtain ⟨η,hη⟩ := hne
  obtain ⟨w,hw,hg⟩ := hη.1.2.1
  refine ⟨w,hw,by rw [hw]; exact hη.1.1,?_⟩
  intro ω hω
  rw [hw]
  apply finiteReversibleGenerated_transfer_prefix (M := i.1) le_rfl ?_ hg
  intro v hv k hk
  let z : splitPrefixCoordinates i.1 := ⟨(v,k),(mem_splitPrefixCoordinates _ _).mpr ⟨hv,hk⟩⟩
  exact (hη.2 z).trans (hω.2 z).symm

end HordijkSteelThreshold
