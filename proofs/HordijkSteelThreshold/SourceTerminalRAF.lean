module

public import proofs.HordijkSteelThreshold.PeelingStabilization
public import proofs.HordijkSteelThreshold.TerminalReactionClosure
public import proofs.HordijkSteelThreshold.SourceBulkMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f : ↥(binaryFood n L) → Molecule L := fun x =>
    ⟨⟨x.val.1.val, by
      have h := (Finset.mem_filter.mp x.property).2
      dsimp [molLength] at h
      omega⟩, x.val.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨ai,aw⟩,ha⟩ ⟨⟨bi,bw⟩,hb⟩ h
    apply Subtype.ext
    have hi : ai = bi := Fin.ext (congrArg (fun z : Molecule L => z.1.val) h)
    subst bi
    congr
    apply Fin.ext
    exact congrArg (fun z : Molecule L => z.2.val) h
  simpa using Fintype.card_le_of_injective f hf

theorem source_terminal_hasRAF {n : ℕ} (ω : AmbientCoord n → Prop)
    (hmass : 6 < (temporaryReactionClosure 2 (peelingActiveAt (catalystActive ω)
      (temporaryReactionClosure 2) (Fintype.card (Reaction n)))).card) :
    ∃ S : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S := by
  let A := peelingActiveAt (catalystActive ω) (temporaryReactionClosure 2) (Fintype.card (Reaction n))
  have hm : Monotone (@temporaryReactionClosure n 2) := fun _ _ h => temporaryReactionClosure_mono h
  have hstable : catalystActive ω (temporaryReactionClosure 2 A) = A :=
    peelingActiveAt_stable_card (catalystActive ω) (temporaryReactionClosure 2)
      (catalystActive_mono ω) hm
  have hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure 2 A, ω (x,r) := by
    intro r hr
    apply (mem_catalystActive ω _ r).mp
    rwa [hstable]
  have hx : ∃ x ∈ temporaryReactionClosure 2 A, 2 < molLength x := by
    by_contra h
    have hs : temporaryReactionClosure 2 A ⊆ binaryFood n 2 := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hlen
      exact h ⟨x,hx,Nat.lt_of_not_ge hlen⟩
    have hb : (binaryFood n 2).card ≤ 6 := by
      simpa only [show Fintype.card (Molecule 2) = 6 from by decide] using binaryFood_card_le_cutoff n 2
    have hh := (Finset.card_le_card hs).trans hb
    exact (Nat.not_lt_of_ge hh) hmass
  exact ⟨usableClosureReactions 2 A, usableClosureReactions_isRAF A (fun x r => ω (x,r)) hcat hx⟩

theorem ambient_raf_probability_eventually_positive {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ c : ENNReal, 0 < c ∧ ∀ᶠ n in atTop,
      c ≤ ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} := by
  obtain ⟨c,hc,hsource⟩ := source_peeling_half_mass_positive hlambda
  refine ⟨c,hc,?_⟩
  filter_upwards [hsource,eventually_ge_atTop 3] with n hn hn3
  apply (hn (Fintype.card (Reaction n))).trans
  apply measure_mono
  intro ω hω
  apply source_terminal_hasRAF ω
  have hsize : 6 < Fintype.card (Molecule n)/2 := by
    rw [card_molecules_exact]
    have hp : 2^4 ≤ 2^(n+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    norm_num at hp
    omega
  exact hsize.trans_le hω

end HordijkSteelThreshold
