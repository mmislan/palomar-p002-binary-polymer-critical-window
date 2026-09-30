module

public import proofs.HordijkSteelThreshold.StaticSeedClosure
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- The seed event and any temporary-food closure statistic use disjoint
literal reaction coordinates. -/
theorem static_seed_bulk_indep (N L : ℕ) (a : I) (P : Finset (Molecule N) → Prop) :
    IndepFun (fun ω : Reaction N → Prop => ∀ r ∈ lowProductBridge N L, ω r)
      (fun ω => P (temporaryReactionClosure L (staticOpenReactions ω)))
      (staticReactionMeasure N a) := by
  let B := lowProductBridge N L
  let D : Finset (Reaction N) := Finset.univ.filter (fun r => L < molLength (reactionProduct r))
  have hdis : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro r hr hd
    have hb : molLength (reactionProduct r) ≤ L := (Finset.mem_filter.mp hr).2
    exact (Nat.not_lt_of_ge hb) (Finset.mem_filter.mp hd).2
  have hi := (staticReactionMeasure_indep N a).indepFun_finset B D hdis
    (fun r => measurable_pi_apply r)
  let f : (B → Prop) → Prop := fun v => ∀ r, ∀ hr : r ∈ B, v ⟨r,hr⟩
  let g : (D → Prop) → Prop := fun v => P (temporaryReactionClosure L
    (D.filter (fun r => ∃ hr : r ∈ D, v ⟨r,hr⟩)))
  have hf : (fun ω : Reaction N → Prop => f (fun r : B => ω r)) =
      (fun ω => ∀ r ∈ lowProductBridge N L, ω r) := rfl
  have hg : (fun ω : Reaction N → Prop => g (fun r : D => ω r)) =
      (fun ω => P (temporaryReactionClosure L (staticOpenReactions ω))) := by
    funext ω
    apply congrArg P
    have he : D.filter (fun r => ∃ hr : r ∈ D, ω r) =
        highProductReactions L (staticOpenReactions ω) := by
      dsimp only [D]
      unfold highProductReactions staticOpenReactions
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      aesop
    change temporaryReactionClosure L (D.filter _) = _
    rw [he, temporaryReactionClosure_erase_low]
  rw [← hf, ← hg]
  exact hi.comp (measurable_of_finite f) (measurable_of_finite g)

theorem static_seed_bulk_probability (N L : ℕ) (a : I)
    (P : Finset (Molecule N) → Prop) :
    staticReactionMeasure N a {ω | (∀ r ∈ lowProductBridge N L, ω r) ∧
      P (temporaryReactionClosure L (staticOpenReactions ω))} =
      (toNNReal a : ENNReal)^(lowProductBridge N L).card *
        staticReactionMeasure N a {ω | P (temporaryReactionClosure L (staticOpenReactions ω))} := by
  have hi := (static_seed_bulk_indep N L a P).measure_inter_preimage_eq_mul
    {True} {True} (MeasurableSet.singleton True) (MeasurableSet.singleton True)
  have hb := measure_detourOpen (staticReactionMeasure N a) (fun r ω => ω r)
    (staticReactionMeasure_indep N a) (toNNReal a : ENNReal)
    (staticReactionMeasure_open a) (lowProductBridge N L)
  simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
    Set.ofPred_inter_eq_sep, Set.mem_ofPred_eq, and_comm, hb] using hi

/-- A positive seed cost multiplies the unconditional static bulk probability.
There is no conditioning on an adaptively selected catalyst pool. -/
theorem static_food_two_mass_lower (N L k : ℕ) (a : I) :
    (toNNReal a : ENNReal)^(lowProductBridge N L).card *
      staticReactionMeasure N a {ω | k ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card} ≤
    staticReactionMeasure N a {ω | k ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card} := by
  rw [← static_seed_bulk_probability N L a (fun C => k ≤ C.card)]
  apply measure_mono
  intro ω hω
  have hB : lowProductBridge N L ⊆ staticOpenReactions ω := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hω.1 r hr⟩
  have hs : temporaryReactionClosure L (staticOpenReactions ω) ⊆
      temporaryReactionClosure 2 (staticOpenReactions ω) :=
    temporaryReactionClosure_seed_transfer Finset.Subset.rfl (lowProductBridge_generates hB)
  exact hω.2.trans (Finset.card_le_card hs)

end HordijkSteelThreshold
