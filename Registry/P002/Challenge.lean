module

public import Mathlib

@[expose] public section

/-!
# Nontrivial critical window in the binary-polymer RAF model
Literature question 3, split-position reaction convention. Food consists of all
words of length at most two. Catalysis coordinates are independent Bernoulli
bits, one per molecule and reversible channel; a bit catalyzes both orientations.
For every asymptotically linear intensity f(n), the RAF probability converges
strictly between zero and one, with a continuous monotone dependence on f(n)/n.
The finite-n probability clamp is included explicitly below.
-/

namespace RAF
def Catalysis (M R : Type*) := M → R → Prop
end RAF
namespace RAF.Polymer
abbrev Word (length : Nat) := Fin (2 ^ length)

abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val

end RAF.Polymer

namespace RAF.Concrete

open RAF.Polymer

/-- Length of an ambient binary polymer. -/
def molLength {n : Nat} (x : Molecule n) : Nat := x.1.val + 1

theorem moleculeOfCode_index_lt {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n) :
    L - 1 < n :=
  Nat.lt_of_lt_of_le (Nat.sub_lt hL (Nat.zero_lt_succ 0)) hLn

theorem moleculeOfCode_pow_eq {L : Nat} (hL : 1 ≤ L) :
    2 ^ L = 2 ^ (L - 1 + 1) :=
  congrArg (fun k : Nat => 2 ^ k) (Nat.sub_add_cancel hL).symm

/-- A length-indexed word viewed as an ambient molecule. -/
def moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : Molecule n :=
  ⟨⟨L - 1, moleculeOfCode_index_lt hL hLn⟩,
    Fin.cast (moleculeOfCode_pow_eq hL) x⟩

/-- Concatenate the bit patterns of two molecules.  `finProdFinEquiv` is the
standard mixed-radix bijection, here with radices `2^|u|` and `2^|v|`. -/
def concatCode {n : Nat} (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))

def concatMolecule {n : Nat} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (by simp [molLength]; omega) h (concatCode u v)

@[simp] theorem molLength_moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : molLength (moleculeOfCode hL hLn x) = L := by
  simp [molLength, moleculeOfCode]
  omega

def reactionProductLength {n : Nat} (r : Reaction n) : Nat := r.1.val + 1
def reactionLeftLength {n : Nat} (r : Reaction n) : Nat := r.2.2.val + 1
def reactionRightLength {n : Nat} (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  exact Eq.trans
    (Nat.add_right_comm r.2.2.val 1 (r.1.val - r.2.2.val))
    (congrArg (fun k : Nat => k + 1)
      (Eq.trans (Nat.add_comm r.2.2.val (r.1.val - r.2.2.val))
        (Nat.sub_add_cancel (Nat.le_of_lt r.2.2.isLt))))

theorem reaction_left_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionLeftLength r := by
  exact Nat.succ_pos r.2.2.val

theorem reaction_right_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionRightLength r := by
  exact Nat.sub_pos_of_lt r.2.2.isLt

theorem reaction_product_le {n : Nat} (r : Reaction n) :
    reactionProductLength r ≤ n := by
  exact r.1.isLt

theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]
  rfl

/-- Split the encoded product at its recorded split position. -/
def splitCodes {n : Nat} (r : Reaction n) :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)

def reactionLeft {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1

def reactionRight {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2

def reactionProduct {n : Nat} (r : Reaction n) : Molecule n :=
  ⟨r.1, r.2.1⟩

@[simp] theorem molLength_reactionLeft {n : Nat} (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r := by
  simp [reactionLeft]

@[simp] theorem molLength_reactionRight {n : Nat} (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r := by
  simp [reactionRight]

@[simp] theorem molLength_reactionProduct {n : Nat} (r : Reaction n) :
    molLength (reactionProduct r) = reactionProductLength r := rfl

/-- The splitting code is inverse to binary concatenation at the code level. -/
theorem split_concat_code {n : Nat} (r : Reaction n) :
    finProdFinEquiv (splitCodes r) =
      Fin.cast (reaction_pow_split r) r.2.1 := by
  exact Equiv.apply_symm_apply finProdFinEquiv _

/-- A reversible CRS records the two sides of each base reaction. Catalysis is
indexed by the base reaction, so one sampled coordinate catalyzes both
directions, exactly as in the paper's reaction convention. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M

def RevEnabledLhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.lhs r ⊆ available

def RevEnabledRhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.rhs r ⊆ available

instance revEnabledLhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance

instance revEnabledRhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance

def revClosureStep {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))

def revClosureAt {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt Q S k)

def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)

/-- The concrete split-position, bidirectional binary-polymer CRS. -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t

end RAF.Concrete
namespace RAF.Concrete
open RAF RAF.Polymer
variable {M R : Type*} [DecidableEq M]
def RevFoodGenerated (Q : ReversibleCRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

def RevReflexivelyAutocatalytic (Q : ReversibleCRS M R)
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

end RAF.Concrete
namespace RAF.Concrete
open RAF RAF.Polymer MeasureTheory ProbabilityTheory unitInterval
variable {M R : Type*} [DecidableEq M]
def RevSeedReaction (Q : ReversibleCRS M R) (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

theorem seed_product_length_le_four {n : Nat} (r : Reaction n)
    (hseed : RevSeedReaction (binaryPolymerCRS n 2) r) :
    reactionProductLength r ≤ 4 := by
  rcases hseed with hl | hr
  · have hleft : reactionLeft r ∈ binaryFood n 2 := by
      apply hl
      simp [binaryPolymerCRS]
    have hright : reactionRight r ∈ binaryFood n 2 := by
      apply hl
      simp [binaryPolymerCRS]
    simp [binaryFood] at hleft hright
    rw [← reaction_length_add r]
    linarith
  · have hp : reactionProduct r ∈ binaryFood n 2 := by
      apply hr
      simp [binaryPolymerCRS]
    have hp2 : reactionProductLength r ≤ 2 := by
      simpa [binaryFood] using hp
    exact hp2.trans (by norm_num)

def seedToReactionFour {n : Nat} (r : PolymerSeedReaction n 2) :
    Reaction 4 :=
  ⟨⟨r.1.1.val, by
      have := seed_product_length_le_four r.1 r.2
      dsimp [reactionProductLength] at this
      omega⟩, r.1.2⟩

theorem seedToReactionFour_injective {n : Nat} :
    Function.Injective (seedToReactionFour (n := n)) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : Reaction 4 => z.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [seedToReactionFour]

abbrev SeedCoord (n : Nat) := Molecule n × PolymerSeedReaction n 2

abbrev NonseedReaction (n : Nat) :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}

abbrev NonseedCoord (n : Nat) := Molecule n × NonseedReaction n

abbrev CatalysisSample (n : Nat) := Set (SeedCoord n) × Set (NonseedCoord n)

noncomputable def rawCatalysisP (n : Nat) (lambda : ℝ) : ℝ :=
  lambda * n / Fintype.card (Reaction n)

noncomputable def catalysisP (n : Nat) (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩

noncomputable def uniformCatalysisMeasure (n : Nat) (lambda : ℝ) :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)).prod
    (setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))

def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

noncomputable def rafProbability (n : Nat) (lambda : ℝ) : ℝ :=
  (uniformCatalysisMeasure n lambda).real (HasRAFEvent n)

end RAF.Concrete

namespace HordijkSteelThreshold
open RAF.Concrete Filter Topology

/-- A continuous monotone, strictly interior limiting law for every sequence
of mean catalysis intensities with a positive finite linear-scale limit. -/
theorem palomar_critical_window_variable_intensity :
    ∃ L : {lambda : ℝ // 0 < lambda} → ℝ,
      Continuous L ∧ Monotone L ∧
      ∀ lambda : {lambda : ℝ // 0 < lambda},
        0 < L lambda ∧ L lambda ≤ 1-Real.exp (-36*lambda.val) ∧ L lambda < 1 ∧
        ∀ f : ℕ → ℝ,
          Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda.val) →
          Tendsto (fun n => rafProbability n (f n/(n : ℝ))) atTop (𝓝 (L lambda)) := by
  sorry
end HordijkSteelThreshold
