module

public import proofs.HordijkSteelThreshold.ReversibleRecordWords

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

def reversibleRecordEvent (L M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, w.length = M ∧ FiniteReversibleGenerated M L field w}

def firstRecordEvent (L B M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | B < M ∧ field ∈ reversibleRecordEvent L M ∧
    ∀ k, B < k → k < M → field ∉ reversibleRecordEvent L k}

theorem measurableSet_reversibleRecordEvent (L M : ℕ) :
    MeasurableSet (reversibleRecordEvent L M) := by
  have he : reversibleRecordEvent L M = ⋃ w : List Bool,
      ⋃ (_h : w.length = M), {field | FiniteReversibleGenerated M L field w} := by
    ext field
    simp [reversibleRecordEvent]
  rw [he]
  exact MeasurableSet.iUnion (fun w => MeasurableSet.iUnion
    (fun _ => measurableSet_finiteReversibleGenerated M L w))

theorem measurableSet_firstRecordEvent (L B M : ℕ) :
    MeasurableSet (firstRecordEvent L B M) := by
  have he : firstRecordEvent L B M = {field | B < M} ∩ reversibleRecordEvent L M ∩
      ⋂ k : ℕ, ⋂ (_h : B < k), ⋂ (_h' : k < M), (reversibleRecordEvent L k)ᶜ := by
    ext field
    simp [firstRecordEvent, and_assoc]
  rw [he]
  have hc : MeasurableSet {field : InfiniteSplitEnvironment | B < M} := by
    by_cases h : B < M <;> simp [h]
  exact (hc.inter (measurableSet_reversibleRecordEvent L M)).inter
    (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => (measurableSet_reversibleRecordEvent L k).compl))))

theorem firstRecordEvent_disjoint (L B : ℕ) {M N : ℕ} (hMN : M ≠ N) :
    Disjoint (firstRecordEvent L B M) (firstRecordEvent L B N) := by
  apply Set.disjoint_left.mpr
  intro field hM hN
  rcases lt_or_gt_of_ne hMN with hlt | hgt
  · exact hN.2.2 M hM.1 hlt hM.2.1
  · exact hM.2.2 N hN.1 hgt hN.2.1

theorem unbounded_mem_firstRecord_union {L : ℕ} {field : InfiniteSplitEnvironment}
    (h : ReversibleUnbounded L field) (B : ℕ) :
    field ∈ ⋃ M, firstRecordEvent L B M := by
  have hex : ∃ M, B < M ∧ field ∈ reversibleRecordEvent L M := by
    obtain ⟨w,hw,hg⟩ := unbounded_record_words h B
    exact ⟨w.length,hw,w,rfl,hg⟩
  refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_⟩
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro k hBk hk hrec
  exact Nat.find_min hex hk ⟨hBk,hrec⟩

/-- Agreement on a finite rectangular prefix suffices. Including unused
split indices is harmless and leaves every later product layer unexposed. -/
theorem finiteReversibleGenerated_transfer_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k)
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L other w := by
  induction h with
  | food hn hL hN => exact .food hn hL hN
  | @ligate u v _ _ ho hN ihu ihv =>
    apply FiniteReversibleGenerated.ligate ihu ihv _ hN
    have hk : u.length ≤ M := by simp only [List.length_append] at hN; omega
    exact (he (u++v) (hN.trans hNM) u.length hk) ▸ ho
  | @left u v hu hv hp ho ih =>
    apply FiniteReversibleGenerated.left hu hv ih
    have hlen := finiteReversibleGenerated_length_le hp
    have hk : u.length ≤ M := by simp only [List.length_append] at hlen; omega
    exact (he (u++v) (hlen.trans hNM) u.length hk) ▸ ho
  | @right u v hu hv hp ho ih =>
    apply FiniteReversibleGenerated.right hu hv ih
    have hlen := finiteReversibleGenerated_length_le hp
    have hk : u.length ≤ M := by simp only [List.length_append] at hlen; omega
    exact (he (u++v) (hlen.trans hNM) u.length hk) ▸ ho

theorem reversibleRecordEvent_congr_prefix {L N M : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ reversibleRecordEvent L N ↔ other ∈ reversibleRecordEvent L N := by
  constructor
  · rintro ⟨w,hw,hg⟩
    exact ⟨w,hw,finiteReversibleGenerated_transfer_prefix hNM he hg⟩
  · rintro ⟨w,hw,hg⟩
    exact ⟨w,hw,finiteReversibleGenerated_transfer_prefix hNM
      (fun w hw k hk => (he w hw k hk).symm) hg⟩

theorem firstRecordEvent_congr_prefix {L B M : ℕ}
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ firstRecordEvent L B M ↔ other ∈ firstRecordEvent L B M := by
  have hr (N : ℕ) (hN : N ≤ M) := reversibleRecordEvent_congr_prefix (L := L) hN he
  constructor
  · rintro ⟨hB,hM,hprev⟩
    refine ⟨hB,(hr M le_rfl).mp hM,?_⟩
    intro k hBk hk hrec
    exact hprev k hBk hk ((hr k hk.le).mpr hrec)
  · rintro ⟨hB,hM,hprev⟩
    refine ⟨hB,(hr M le_rfl).mpr hM,?_⟩
    intro k hBk hk hrec
    exact hprev k hBk hk ((hr k hk.le).mp hrec)

end HordijkSteelThreshold
