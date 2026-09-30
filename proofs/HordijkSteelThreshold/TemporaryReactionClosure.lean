module

public import proofs.HordijkSteelThreshold.MarkedCoreAdapter
public import proofs.HordijkSteelThreshold.WordDetourLiteralPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

@[simp] theorem mem_temporaryReactionClosure {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset (Reaction N)}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  exact (mem_temporaryReactionClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S := by
  apply (mem_temporaryReactionClosure S x).mpr
  exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem temporaryReactionClosure_ligation {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hl : reactionLeft r ∈ temporaryReactionClosure L S)
    (hh : reactionRight r ∈ temporaryReactionClosure L S) :
    reactionProduct r ∈ temporaryReactionClosure L S := by
  obtain ⟨kl, hkl⟩ := (mem_temporaryReactionClosure S _).mp hl
  obtain ⟨kr, hkr⟩ := (mem_temporaryReactionClosure S _).mp hh
  have hl' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_left kl kr) hkl
  have hr' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_right kl kr) hkr
  apply (mem_temporaryReactionClosure S _).mpr
  refine ⟨max kl kr+1, ?_⟩
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_union_left _ ?_⟩
  have hen : RevEnabledLhs (binaryPolymerCRS N L)
      (revClosureAt (binaryPolymerCRS N L) S (max kl kr)) r := by
    simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hl' hr'
  rw [ite_eq_left hen]
  exact Finset.mem_singleton_self _

theorem temporaryReactionClosure_cleavage {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hp : reactionProduct r ∈ temporaryReactionClosure L S) :
    reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S _).mp hp
  have hen : RevEnabledRhs (binaryPolymerCRS N L) (revClosureAt (binaryPolymerCRS N L) S k) r := by
    simpa [RevEnabledRhs, binaryPolymerCRS] using hk
  have hadd : {reactionLeft r, reactionRight r} ⊆
      revClosureAt (binaryPolymerCRS N L) S (k+1) := by
    intro x hx
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, Finset.mem_union_right _ ?_⟩
    rw [ite_eq_left hen]
    exact hx
  exact ⟨(mem_temporaryReactionClosure S _).mpr ⟨k+1,hadd (by simp)⟩,
    (mem_temporaryReactionClosure S _).mpr ⟨k+1,hadd (by simp)⟩⟩

theorem moleculeWord_injective {N : ℕ} : Function.Injective (@moleculeWord N) := by
  intro x y h
  obtain ⟨kx, vx⟩ := x
  obtain ⟨ky, vy⟩ := y
  have hh := congrArg List.length h
  rw [moleculeWord_length, moleculeWord_length] at hh
  have hidx : kx = ky := Fin.ext (by unfold molLength at hh; dsimp at hh; omega)
  subst ky
  have hc := congrArg binaryWordCode h
  rw [binaryWordCode_moleculeWord, binaryWordCode_moleculeWord] at hc
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hc))

/-- Generability is well defined on contracted words: every representative of
food is generated, while a nonfood word has a unique source molecule. -/
def contractedWordGenerated {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) (s : List Bool) : Prop :=
  ∀ x : Molecule N, contractFoodWord L (moleculeWord x) = s → x ∈ temporaryReactionClosure L S

theorem contractedWordGenerated_root {N L : ℕ} (S : Finset (Reaction N)) :
    contractedWordGenerated L S [] := by
  intro x hx
  by_cases hlen : (moleculeWord x).length ≤ L
  · exact temporaryReactionClosure_food S x (by rwa [moleculeWord_length] at hlen)
  · rw [contractFoodWord, ite_eq_right hlen] at hx
    have he := congrArg List.length hx
    rw [moleculeWord_length] at he
    simp only [List.length_nil] at he
    unfold molLength at he
    omega

theorem contractedWordGenerated_iff {N L : ℕ} (S : Finset (Reaction N)) (x : Molecule N) :
    contractedWordGenerated L S (contractFoodWord L (moleculeWord x)) ↔
      x ∈ temporaryReactionClosure L S := by
  constructor
  · intro h
    exact h x rfl
  · intro hx y hy
    by_cases hyl : (moleculeWord y).length ≤ L
    · exact temporaryReactionClosure_food S y (by rwa [moleculeWord_length] at hyl)
    · by_cases hxl : (moleculeWord x).length ≤ L
      · rw [contractFoodWord, ite_eq_right hyl, contractFoodWord, ite_eq_left hxl] at hy
        have he := congrArg List.length hy
        simp only [moleculeWord_length, List.length_nil] at he
        unfold molLength at he
        omega
      · rw [contractFoodWord, ite_eq_right hyl, contractFoodWord, ite_eq_right hxl] at hy
        exact moleculeWord_injective hy ▸ hx

end HordijkSteelThreshold
