module

public import proofs.HordijkSteelThreshold.WordEndBalls

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordBallEdgeAnchors (L N : ℕ) (s : List Bool) (r : ℕ) :=
  (wordBasicEdges L N).filter (fun e => e.1.val ∈ endWordBall r s)

theorem wordBallEdgeAnchors_card (L N : ℕ) (s : List Bool) (r : ℕ) :
    (wordBallEdgeAnchors L N s r).card ≤ 2 * 7 ^ r := by
  have hc : (wordBallEdgeAnchors L N s r).card ≤
      ((endWordBall r s) ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun e : WordBasicEdge L N => (e.1.val, e.2))
    · intro e he
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2, Finset.mem_univ _⟩
    · intro e _ d _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg (fun x : List Bool × Bool => x.1) h)
      · exact congrArg (fun x : List Bool × Bool => x.2) h
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
  have hb := endWordBall_card r s
  omega

/-- A finite envelope for all size-b contours whose smaller side contains molecule s. -/
noncomputable def wordMoleculeContourEnvelope (L N : ℕ) (s : List Bool) (b : ℕ) :=
  (wordBallEdgeAnchors L N s (64 * b)).biUnion (fun e => wordAnchoredContours L N e b)

theorem wordMoleculeContourEnvelope_card_raw (L N : ℕ) (s : List Bool) (b : ℕ) :
    (wordMoleculeContourEnvelope L N s b).card ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := by
  calc
    _ ≤ ∑ e ∈ wordBallEdgeAnchors L N s (64 * b), (wordAnchoredContours L N e b).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ wordBallEdgeAnchors L N s (64 * b), 81 ^ (b - 1) :=
      Finset.sum_le_sum (fun e _ => wordAnchoredContours_card L N e b)
    _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := by
      simp only [Finset.sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (wordBallEdgeAnchors_card L N s (64 * b))

def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

/-- Uniform per-molecule exponential contour count with an explicit safe constant. -/
theorem wordMoleculeContourEnvelope_card (L N : ℕ) (s : List Bool) (b : ℕ) (hb : 0 < b) :
    (wordMoleculeContourEnvelope L N s b).card ≤ molecularContourConstant ^ b := by
  have h2 : (2 : ℕ) ≤ 2 ^ b := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (show 1 ≤ b by omega)
    simpa using h
  have h81 : (81 : ℕ) ^ (b - 1) ≤ 81 ^ b :=
    pow_le_pow_right₀ (by decide) (Nat.sub_le b 1)
  calc
    _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := wordMoleculeContourEnvelope_card_raw L N s b
    _ ≤ 2 ^ b * 7 ^ (64 * b) * 81 ^ b :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h81
    _ = molecularContourConstant ^ b := by simp only [molecularContourConstant, mul_pow, pow_mul]

/-- Every relevant literal minimal cut lies in the finite counted envelope. -/
theorem wordBond_mem_molecule_envelope {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    wordGraphCut f ∈ wordMoleculeContourEnvelope L N s (wordGraphCut f).card := by
  obtain ⟨e, he⟩ := hn
  obtain ⟨p, hp⟩ := wordBond_molecular_anchor_radius f hmin e he c hminor s hs
  have heB : e ∈ wordBallEdgeAnchors L N s (64 * (wordGraphCut f).card) := by
    refine Finset.mem_filter.mpr ⟨?_, endWord_walk_mem_ball p _ hp⟩
    exact (Finset.filter_subset _ _ : wordGraphCut f ⊆ wordBasicEdges L N) he
  exact Finset.mem_biUnion.mpr ⟨e, heB, wordBond_mem_anchored f hmin e he⟩

end HordijkSteelThreshold
