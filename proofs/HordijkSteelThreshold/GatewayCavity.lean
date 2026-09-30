module

public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Restrict an arbitrary catalysis relation to the gateway and bulk
coordinates of the concrete binary-polymer model. -/
def sampleOfCatalysis {n : Nat} (C : Catalysis (Molecule n) (Reaction n)) :
    CatalysisSample n :=
  (
    {z | C z.1 z.2.1},
    {z | C z.1 z.2.1}
  )

theorem catalysisOf_sampleOfCatalysis {n : Nat}
    (C : Catalysis (Molecule n) (Reaction n)) :
    catalysisOf (sampleOfCatalysis C) = C := by
  funext x r
  by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;>
    simp [catalysisOf, sampleOfCatalysis, h]

theorem sampleOfCatalysis_catalysisOf {n : Nat} (omega : CatalysisSample n) :
    sampleOfCatalysis (catalysisOf omega) = omega := by
  apply Prod.ext
  · ext z
    simp [sampleOfCatalysis, catalysisOf, z.2.2]
  · ext z
    simp [sampleOfCatalysis, catalysisOf, z.2.2]

/-- The gateway/bulk split is lossless: it is an equivalence, not merely a
coupling or a probability-space presentation. -/
def catalysisSampleEquiv (n : Nat) :
    CatalysisSample n ≃ Catalysis (Molecule n) (Reaction n) where
  toFun := catalysisOf
  invFun := sampleOfCatalysis
  left_inv := sampleOfCatalysis_catalysisOf
  right_inv := catalysisOf_sampleOfCatalysis

/-- The catalysis relation obtained from bulk coordinates alone.  Every edge
whose target is a gateway reaction is deleted. -/
def bulkCatalysis {n : Nat} (bulk : Set (NonseedCoord n)) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then False
  else (x, ⟨r, h⟩) ∈ bulk

def GatewayForced {n : Nat} (J : Finset (PolymerSeedReaction n 2))
    (r : Reaction n) : Prop :=
  ∃ h : RevSeedReaction (binaryPolymerCRS n 2) r, (⟨r, h⟩ : PolymerSeedReaction n 2) ∈ J

/-- A `J`-seeded RAF uses a private external catalyst exactly for reactions
in `J`; every other catalytic witness must come from the internally generated
closure and a nongateway coordinate.  Encoding the external catalyst as the
`GatewayForced` disjunct avoids changing the molecule universe. -/
def IsGatewaySeededRAF {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) (S : Finset (Reaction n)) : Prop :=
  S.Nonempty ∧
    RevFoodGenerated (binaryPolymerCRS n 2) S ∧
    ∀ r ∈ S, GatewayForced J r ∨
      ∃ x k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k ∧ bulkCatalysis bulk x r

noncomputable def gatewaySeededRAFFamily {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Finset (Reaction n)) := by
  classical
  exact Finset.univ.filter (IsGatewaySeededRAF bulk J)

@[simp] theorem mem_gatewaySeededRAFFamily {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) (S : Finset (Reaction n)) :
    S ∈ gatewaySeededRAFFamily bulk J ↔ IsGatewaySeededRAF bulk J S := by
  classical
  simp [gatewaySeededRAFFamily]

/-- The union of every RAF admitted by the `J`-seeded cavity system. -/
noncomputable def gatewaySeededMaxRAF {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Reaction n) := by
  classical
  exact (gatewaySeededRAFFamily bulk J).biUnion id

theorem subset_gatewaySeededMaxRAF_of_isRAF {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) {S : Finset (Reaction n)}
    (hS : IsGatewaySeededRAF bulk J S) : S ⊆ gatewaySeededMaxRAF bulk J := by
  classical
  intro r hr
  simp only [gatewaySeededMaxRAF, Finset.mem_biUnion]
  exact ⟨S, (mem_gatewaySeededRAFFamily bulk J S).2 hS, hr⟩

/-- Gateway reactions used by a concrete reaction set, retaining their proof
that they lie on the food boundary. -/
noncomputable def gatewayPart {n : Nat} (S : Finset (Reaction n)) :
    Finset (PolymerSeedReaction n 2) := by
  classical
  exact Finset.univ.filter fun r => r.1 ∈ S

@[simp] theorem mem_gatewayPart {n : Nat} (S : Finset (Reaction n))
    (r : PolymerSeedReaction n 2) : r ∈ gatewayPart S ↔ r.1 ∈ S := by
  classical
  simp [gatewayPart]

theorem gatewayPart_nonempty_of_revRAF {n : Nat} (C : Catalysis (Molecule n) (Reaction n))
    {S : Finset (Reaction n)}
    (hS : IsRevRAF (binaryPolymerCRS n 2) C S) : (gatewayPart S).Nonempty := by
  obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated
    (binaryPolymerCRS n 2) S hS.1 hS.2.1
  exact ⟨⟨r, hseed⟩, by simp [hr]⟩

theorem actualRAF_isGatewaySeededRAF {n : Nat} (omega : CatalysisSample n)
    {S : Finset (Reaction n)}
    (hS : IsRevRAF (binaryPolymerCRS n 2) (catalysisOf omega) S) :
    IsGatewaySeededRAF omega.2 (gatewayPart S) S := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro r hr
  by_cases hseed : RevSeedReaction (binaryPolymerCRS n 2) r
  · exact Or.inl ⟨hseed, by simp [hr]⟩
  · right
    obtain ⟨x, k, hx, hcat⟩ := hS.2.2 r hr
    refine ⟨x, k, hx, ?_⟩
    simpa [bulkCatalysis, hseed] using
      (catalysisOf_nonseed_iff omega x r hseed).mp hcat

/-- Forward half of the exact cavity theorem: every actual RAF determines a
nonempty gateway seed set which is viable in the system retaining only the
sample's bulk coordinates. -/
theorem actualRAF_implies_seededBulkWitness {n : Nat} (omega : CatalysisSample n)
    {S : Finset (Reaction n)}
    (hS : IsRevRAF (binaryPolymerCRS n 2) (catalysisOf omega) S) :
    ∃ J : Finset (PolymerSeedReaction n 2),
      J.Nonempty ∧ IsGatewaySeededRAF omega.2 J S ∧
        ∀ r ∈ J, r.1 ∈ gatewaySeededMaxRAF omega.2 J := by
  let J := gatewayPart S
  have hseeded : IsGatewaySeededRAF omega.2 J S := actualRAF_isGatewaySeededRAF omega hS
  refine ⟨J, gatewayPart_nonempty_of_revRAF _ hS, hseeded, ?_⟩
  intro r hr
  exact subset_gatewaySeededMaxRAF_of_isRAF omega.2 J hseeded ((mem_gatewayPart S r).mp hr)

/-- Reverse cavity implication for a specified seeded witness.  Real gateway
hits from the same closure replace the private external supports, while every
nongateway catalytic witness is unchanged. -/
theorem seededBulkWitness_implies_actualRAF {n : Nat} (omega : CatalysisSample n)
    (J : Finset (PolymerSeedReaction n 2)) {S : Finset (Reaction n)}
    (hS : IsGatewaySeededRAF omega.2 J S)
    (hhit : ∀ r ∈ J, ∃ x k,
      x ∈ revClosureAt (binaryPolymerCRS n 2) S k ∧ (x, r) ∈ omega.1) :
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf omega) S := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro r hr
  rcases hS.2.2 r hr with hforced | hbulk
  · obtain ⟨hseed, hmem⟩ := hforced
    obtain ⟨x, k, hx, hcat⟩ := hhit ⟨r, hseed⟩ hmem
    exact ⟨x, k, hx, (catalysisOf_seed_iff omega x r hseed).mpr hcat⟩
  · obtain ⟨x, k, hx, hcat⟩ := hbulk
    have hnonseed : ¬ RevSeedReaction (binaryPolymerCRS n 2) r := by
      intro hseed
      simp [bulkCatalysis, hseed] at hcat
    have hcat' : (x, ⟨r, hnonseed⟩) ∈ omega.2 := by
      simpa [bulkCatalysis, hnonseed] using hcat
    exact ⟨x, k, hx, (catalysisOf_nonseed_iff omega x r hnonseed).mpr hcat'⟩

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  intro x hx
  simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with hxA | ⟨r, hrS, hx⟩
  · exact Or.inl (hAB hxA)
  · right
    refine ⟨r, hST hrS, ?_⟩
    rcases hx with hx | hx
    · by_cases hEnabled : RevEnabledLhs Q A r
      · have hEnabled' : RevEnabledLhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx
    · by_cases hEnabled : RevEnabledRhs Q A r
      · have hEnabled' : RevEnabledRhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact revClosureStep_mono Q hST ih

theorem IsGatewaySeededRAF.union {n : Nat} {bulk : Set (NonseedCoord n)}
    {J : Finset (PolymerSeedReaction n 2)} {S T : Finset (Reaction n)}
    (hS : IsGatewaySeededRAF bulk J S) (hT : IsGatewaySeededRAF bulk J T) :
    IsGatewaySeededRAF bulk J (S ∪ T) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hS.1
    exact ⟨r, Finset.mem_union_left T hr⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hrS | hrT
    · obtain ⟨k, hk⟩ := hS.2.1 r hrS
      exact ⟨k, fun x hx => revClosureAt_mono_reactions _
        (Finset.subset_union_left (s₁ := S) (s₂ := T)) k (hk hx)⟩
    · obtain ⟨k, hk⟩ := hT.2.1 r hrT
      exact ⟨k, fun x hx => revClosureAt_mono_reactions _
        (Finset.subset_union_right (s₁ := S) (s₂ := T)) k (hk hx)⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hrS | hrT
    · rcases hS.2.2 r hrS with hforced | ⟨x, k, hx, hcat⟩
      · exact Or.inl hforced
      · exact Or.inr ⟨x, k, revClosureAt_mono_reactions _
          (Finset.subset_union_left (s₁ := S) (s₂ := T)) k hx, hcat⟩
    · rcases hT.2.2 r hrT with hforced | ⟨x, k, hx, hcat⟩
      · exact Or.inl hforced
      · exact Or.inr ⟨x, k, revClosureAt_mono_reactions _
          (Finset.subset_union_right (s₁ := S) (s₂ := T)) k hx, hcat⟩

theorem isGatewaySeededRAF_maxRAF {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2))
    (hne : (gatewaySeededRAFFamily bulk J).Nonempty) :
    IsGatewaySeededRAF bulk J (gatewaySeededMaxRAF bulk J) := by
  classical
  obtain ⟨S₀, hS₀⟩ := hne
  have hseed₀ := (mem_gatewaySeededRAFFamily bulk J S₀).mp hS₀
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hseed₀.1
    exact ⟨r, subset_gatewaySeededMaxRAF_of_isRAF bulk J hseed₀ hr⟩
  · intro r hr
    simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hr
    obtain ⟨S, hSF, hrS⟩ := hr
    have hseed := (mem_gatewaySeededRAFFamily bulk J S).mp hSF
    obtain ⟨k, hk⟩ := hseed.2.1 r hrS
    exact ⟨k, fun x hx => revClosureAt_mono_reactions _
      (subset_gatewaySeededMaxRAF_of_isRAF bulk J hseed) k (hk hx)⟩
  · intro r hr
    simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hr
    obtain ⟨S, hSF, hrS⟩ := hr
    have hseed := (mem_gatewaySeededRAFFamily bulk J S).mp hSF
    rcases hseed.2.2 r hrS with hforced | ⟨x, k, hx, hcat⟩
    · exact Or.inl hforced
    · exact Or.inr ⟨x, k, revClosureAt_mono_reactions _
        (subset_gatewaySeededMaxRAF_of_isRAF bulk J hseed) k hx, hcat⟩

/-- Exact finite cavity decomposition, expressed using the seeded maxRAF.
The bulk coordinates determine viability and closure; the boundary coordinates
are consulted only for actual hits on the finitely many forced gateways. -/
theorem hasRAFEvent_iff_exists_seededGatewayTrace {n : Nat} (omega : CatalysisSample n) :
    omega ∈ HasRAFEvent n ↔
      ∃ J : Finset (PolymerSeedReaction n 2),
        J.Nonempty ∧
        (∀ r ∈ J, r.1 ∈ gatewaySeededMaxRAF omega.2 J) ∧
        (∀ r ∈ J, ∃ x k,
          x ∈ revClosureAt (binaryPolymerCRS n 2) (gatewaySeededMaxRAF omega.2 J) k ∧
          (x, r) ∈ omega.1) := by
  constructor
  · rintro ⟨S, hS⟩
    let J := gatewayPart S
    have hseeded : IsGatewaySeededRAF omega.2 J S := actualRAF_isGatewaySeededRAF omega hS
    have hsub : S ⊆ gatewaySeededMaxRAF omega.2 J :=
      subset_gatewaySeededMaxRAF_of_isRAF omega.2 J hseeded
    refine ⟨J, gatewayPart_nonempty_of_revRAF _ hS, ?_, ?_⟩
    · intro r hr
      exact hsub ((mem_gatewayPart S r).mp hr)
    · intro r hr
      have hrS : r.1 ∈ S := (mem_gatewayPart S r).mp hr
      obtain ⟨x, k, hx, hcat⟩ := hS.2.2 r.1 hrS
      refine ⟨x, k, revClosureAt_mono_reactions _ hsub k hx, ?_⟩
      simpa using (catalysisOf_seed_iff omega x r.1 r.2).mp hcat
  · rintro ⟨J, hJne, hviable, hhit⟩
    have hfamily : (gatewaySeededRAFFamily omega.2 J).Nonempty := by
      obtain ⟨r, hrJ⟩ := hJne
      have hrMax := hviable r hrJ
      simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hrMax
      obtain ⟨S, hSF, _hrS⟩ := hrMax
      exact ⟨S, hSF⟩
    have hmax := isGatewaySeededRAF_maxRAF omega.2 J hfamily
    exact ⟨gatewaySeededMaxRAF omega.2 J,
      seededBulkWitness_implies_actualRAF omega J hmax hhit⟩

def GatewayTraceAccepts {n : Nat} (seed : Set (SeedCoord n))
    (bulk : Set (NonseedCoord n)) : Prop :=
  ∃ J : Finset (PolymerSeedReaction n 2),
    J.Nonempty ∧
    (∀ r ∈ J, r.1 ∈ gatewaySeededMaxRAF bulk J) ∧
    (∀ r ∈ J, ∃ x k,
      x ∈ revClosureAt (binaryPolymerCRS n 2) (gatewaySeededMaxRAF bulk J) k ∧
      (x, r) ∈ seed)

theorem gatewayTraceAccepts_iff_hasRAFEvent {n : Nat} (seed : Set (SeedCoord n))
    (bulk : Set (NonseedCoord n)) :
    GatewayTraceAccepts seed bulk ↔ (seed, bulk) ∈ HasRAFEvent n := by
  exact (hasRAFEvent_iff_exists_seededGatewayTrace (seed, bulk)).symm

/-- Conditional RAF probability after fixing all nongateway coordinates. -/
noncomputable def gatewayEvaluator (n : Nat) (lambda : ℝ)
    (bulk : Set (NonseedCoord n)) : ENNReal :=
  setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)
    {seed | GatewayTraceAccepts seed bulk}

/-- Exact expectation identity over the bulk randomness. -/
theorem measure_hasRAFEvent_eq_lintegral_gatewayEvaluator (n : Nat) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      ∫⁻ bulk, gatewayEvaluator n lambda bulk
        ∂(setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda)) := by
  rw [uniformCatalysisMeasure,
    MeasureTheory.Measure.prod_apply_symm (measurableSet_hasRAFEvent n)]
  apply MeasureTheory.lintegral_congr
  intro bulk
  unfold gatewayEvaluator
  congr 1
  ext seed
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq] using
    (gatewayTraceAccepts_iff_hasRAFEvent seed bulk).symm

theorem rafProbability_eq_gatewayExpectation (n : Nat) (lambda : ℝ) :
    rafProbability n lambda = ENNReal.toReal
      (∫⁻ bulk, gatewayEvaluator n lambda bulk
        ∂(setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))) := by
  change ENNReal.toReal (uniformCatalysisMeasure n lambda (HasRAFEvent n)) = _
  rw [measure_hasRAFEvent_eq_lintegral_gatewayEvaluator]

theorem GatewayForced.mono {n : Nat}
    {J K : Finset (PolymerSeedReaction n 2)} (hJK : J ⊆ K)
    {r : Reaction n} (hr : GatewayForced J r) : GatewayForced K r := by
  obtain ⟨hseed, hrJ⟩ := hr
  exact ⟨hseed, hJK hrJ⟩

theorem IsGatewaySeededRAF.mono_forced {n : Nat} {bulk : Set (NonseedCoord n)}
    {J K : Finset (PolymerSeedReaction n 2)} (hJK : J ⊆ K)
    {S : Finset (Reaction n)} (hS : IsGatewaySeededRAF bulk J S) :
    IsGatewaySeededRAF bulk K S := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro r hr
  rcases hS.2.2 r hr with hforced | hbulk
  · exact Or.inl (hforced.mono hJK)
  · exact Or.inr hbulk

theorem gatewaySeededMaxRAF_mono_forced {n : Nat} (bulk : Set (NonseedCoord n))
    {J K : Finset (PolymerSeedReaction n 2)} (hJK : J ⊆ K) :
    gatewaySeededMaxRAF bulk J ⊆ gatewaySeededMaxRAF bulk K := by
  classical
  intro r hr
  simp only [gatewaySeededMaxRAF, Finset.mem_biUnion] at hr ⊢
  obtain ⟨S, hSF, hrS⟩ := hr
  have hS : IsGatewaySeededRAF bulk J S :=
    (mem_gatewaySeededRAFFamily bulk J S).mp hSF
  exact ⟨S, (mem_gatewaySeededRAFFamily bulk K S).mpr (hS.mono_forced hJK), hrS⟩

end HordijkSteelThreshold
