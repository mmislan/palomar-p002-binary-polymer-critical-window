module

public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- Low-product reaction coordinates inject into the fixed cutoff universe,
even when the ambient cap is larger or smaller than the cutoff. -/
def lowProductBridgeRestrict (N L : ℕ) (r : ↥(lowProductBridge N L)) : Reaction L :=
  ⟨⟨r.val.1.val, by
    have h := (Finset.mem_filter.mp r.property).2
    change r.val.1.val+1 ≤ L at h
    omega⟩, r.val.2⟩

theorem lowProductBridgeRestrict_injective (N L : ℕ) :
    Function.Injective (lowProductBridgeRestrict N L) := by
  intro r s he
  apply Subtype.ext
  obtain ⟨⟨kr, wr, jr⟩, hr⟩ := r
  obtain ⟨⟨ks, ws, js⟩, hs⟩ := s
  have hk : kr = ks := Fin.ext (congrArg (fun t : Reaction L => t.1.val) he)
  subst ks
  have hp : (wr,jr) = (ws,js) := by
    simpa only [lowProductBridgeRestrict, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  cases hp
  rfl

theorem lowProductBridge_card_le (N L : ℕ) :
    (lowProductBridge N L).card ≤ Fintype.card (Reaction L) := by
  simpa using Fintype.card_le_of_injective _ (lowProductBridgeRestrict_injective N L)

end HordijkSteelThreshold
