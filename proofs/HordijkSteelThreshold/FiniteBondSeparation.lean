module

public import proofs.HordijkSteelThreshold.BooleanEdgeCuts

@[expose] public section

namespace HordijkSteelThreshold

def indexedEdgeStep {V E : Type*} (active : Finset E) (a b : E → V) (x y : V) : Prop :=
  ∃ e ∈ active, a e = x ∧ b e = y

def indexedEdgeReach {V E : Type*} (active : Finset E) (a b : E → V) : V → V → Prop :=
  Relation.EqvGen (indexedEdgeStep active a b)

theorem indexedEdgeReach_label {V E : Type*}
    (active : Finset E) (a b : E → V) (label : V → Bool)
    (hedge : ∀ e ∈ active, label (a e) = label (b e))
    {x y : V} (h : indexedEdgeReach active a b x y) : label x = label y := by
  induction h with
  | rel x y h =>
    obtain ⟨e, he, ha, hb⟩ := h
    rw [← ha, ← hb]
    exact hedge e he
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem closed_cut_of_unreachable {V E : Type*} [DecidableEq E]
    (edges active : Finset E) (a b : E → V) (x y : V)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    ∃ label : V → Bool, label x ≠ label y ∧
      booleanEdgeCut edges a b label ⊆ edges \ active := by
  classical
  let f : V → Bool := fun v => decide (indexedEdgeReach active a b x v)
  refine ⟨f, ?_, ?_⟩
  · have hx : indexedEdgeReach active a b x x := Relation.EqvGen.refl x
    simp [f, hx, hxy]
  · intro e he
    obtain ⟨heE, hdiff⟩ := Finset.mem_filter.mp he
    refine Finset.mem_sdiff.mpr ⟨heE, ?_⟩
    intro heA
    have hab : indexedEdgeReach active a b (a e) (b e) :=
      Relation.EqvGen.rel _ _ ⟨e, heA, rfl, rfl⟩
    have hi : indexedEdgeReach active a b x (a e) ↔ indexedEdgeReach active a b x (b e) :=
      ⟨fun h => Relation.EqvGen.trans _ _ _ h hab,
       fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hab)⟩
    exact hdiff (by simp only [f, hi])

theorem exists_minimum_separating_cut {V E : Type*}
    (edges : Finset E) (a b : E → V) (closed : Finset E) (x y : V)
    (hex : ∃ f : V → Bool, f x ≠ f y ∧ booleanEdgeCut edges a b f ⊆ closed) :
    ∃ f : V → Bool, f x ≠ f y ∧ booleanEdgeCut edges a b f ⊆ closed ∧
      ∀ g : V → Bool, g x ≠ g y → booleanEdgeCut edges a b g ⊆ closed →
        (booleanEdgeCut edges a b f).card ≤ (booleanEdgeCut edges a b g).card := by
  classical
  have hn : ∃ k : ℕ, ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ closed ∧ (booleanEdgeCut edges a b f).card = k := by
    obtain ⟨f, hf, hc⟩ := hex
    exact ⟨_, f, hf, hc, rfl⟩
  obtain ⟨f, hf, hc, hcard⟩ := Nat.find_spec hn
  refine ⟨f, hf, hc, ?_⟩
  intro g hg hgc
  rw [hcard]
  exact Nat.find_min' hn ⟨g, hg, hgc, rfl⟩

/-- Any pair connected in the host but disconnected by the enabled edges
has a disabled separating bond. The conclusion gives global cut minimality,
which is what the diamond-potential argument requires. -/
theorem exists_disabled_separating_bond {V E : Type*} [DecidableEq E]
    (edges active : Finset E) (a b : E → V) (x y : V)
    (hhost : indexedEdgeReach edges a b x y)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ edges \ active ∧
      (booleanEdgeCut edges a b f).Nonempty ∧
      ∀ g : V → Bool, (booleanEdgeCut edges a b g).Nonempty →
        booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f →
        booleanEdgeCut edges a b g = booleanEdgeCut edges a b f := by
  classical
  obtain ⟨f, hf, hc, hmin⟩ := exists_minimum_separating_cut edges a b (edges \ active) x y
    (closed_cut_of_unreachable edges active a b x y hxy)
  refine ⟨f, hf, hc, ?_, ?_⟩
  · by_contra hn
    have hedge : ∀ e ∈ edges, f (a e) = f (b e) := by
      intro e he
      by_contra hd
      exact hn ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩
    exact hf (indexedEdgeReach_label edges a b f hedge hhost)
  · exact minimal_separating_cut_is_bond edges a b (edges \ active) x y f hf hc hmin

end HordijkSteelThreshold
