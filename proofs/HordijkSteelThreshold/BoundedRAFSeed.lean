module

public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF RAF.Polymer RAF.Concrete

/-- A RAF in a bounded ambient closure has a bounded catalyst for a seed
reaction. This is deterministic and uses no conditional independence. -/
theorem bounded_raf_has_seed_catalyst {n K : ℕ} (ω : AmbientCoord n → Prop)
    (hbounded : ∀ x ∈ temporaryReactionClosure 2 (catalystActive ω Finset.univ),
      molLength x ≤ K)
    (hraf : ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S) :
    ∃ x : Molecule n, ∃ r : Reaction n,
      molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r) := by
  obtain ⟨S, hne, hfg, hcat⟩ := hraf
  have hsub : S ⊆ catalystActive ω Finset.univ := by
    intro r hr
    obtain ⟨x, _, _, hx⟩ := hcat r hr
    exact (mem_catalystActive ω Finset.univ r).mpr ⟨x, Finset.mem_univ _, hx⟩
  obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated _ S hne hfg
  obtain ⟨x, k, hx, hxr⟩ := hcat r hr
  have hxS : x ∈ temporaryReactionClosure 2 S :=
    (mem_temporaryReactionClosure S x).mpr ⟨k, hx⟩
  exact ⟨x, r, hbounded x (temporaryReactionClosure_mono hsub hxS), hseed, hxr⟩

end HordijkSteelThreshold
