module

public import proofs.HordijkSteelThreshold.NucleusAmplification

@[expose] public section

namespace HordijkSteelThreshold

/-- An infinite split-position environment. `openAt w k` records openness of
the ligation producing `w` at split position `k`. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

/-- Food-rooted ligation closure on finite binary words, with no maximum
polymer length. This is the infinite ambient-open exploration process used by
the block-growth argument. -/
inductive InfiniteGenerated (foodLength : Nat) (openAt : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w : List Bool} (hne : w ≠ []) (hlen : w.length ≤ foodLength) :
      InfiniteGenerated foodLength openAt w
  | ligate {u v : List Bool}
      (hu : InfiniteGenerated foodLength openAt u)
      (hv : InfiniteGenerated foodLength openAt v)
      (ho : openAt (u ++ v) u.length) :
      InfiniteGenerated foodLength openAt (u ++ v)

/-- The same ligation exploration truncated at maximum word length `n`. -/
inductive FiniteGenerated (n foodLength : Nat) (openAt : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w : List Bool} (hne : w ≠ []) (hlen : w.length ≤ foodLength)
      (hcut : w.length ≤ n) : FiniteGenerated n foodLength openAt w
  | ligate {u v : List Bool}
      (hu : FiniteGenerated n foodLength openAt u)
      (hv : FiniteGenerated n foodLength openAt v)
      (ho : openAt (u ++ v) u.length)
      (hcut : (u ++ v).length ≤ n) :
      FiniteGenerated n foodLength openAt (u ++ v)

theorem infiniteGenerated_nonempty {t : Nat} {openAt : InfiniteSplitEnvironment}
    {w : List Bool} (hw : InfiniteGenerated t openAt w) : w ≠ [] := by
  induction hw with
  | food hne _ => exact hne
  | ligate hu hv _ ihu _ =>
      exact List.append_ne_nil_of_left_ne_nil ihu _

theorem infiniteGenerated_mono_open {t : Nat}
    {openAt openAt' : InfiniteSplitEnvironment}
    (hmono : ∀ w k, openAt w k → openAt' w k) {w : List Bool}
    (hw : InfiniteGenerated t openAt w) : InfiniteGenerated t openAt' w := by
  induction hw with
  | food hne hlen => exact .food hne hlen
  | ligate hu hv ho ihu ihv => exact .ligate ihu ihv (hmono _ _ ho)

theorem infiniteGenerated_mono_food {t t' : Nat} (htt' : t ≤ t')
    {openAt : InfiniteSplitEnvironment} {w : List Bool}
    (hw : InfiniteGenerated t openAt w) : InfiniteGenerated t' openAt w := by
  induction hw with
  | food hne hlen => exact .food hne (hlen.trans htt')
  | ligate hu hv ho ihu ihv => exact .ligate ihu ihv ho

theorem finiteGenerated_to_infinite {n t : Nat} {openAt : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteGenerated n t openAt w) :
    InfiniteGenerated t openAt w := by
  induction hw with
  | food hne hlen _ => exact .food hne hlen
  | ligate hu hv ho _ ihu ihv => exact .ligate ihu ihv ho

/-- Ligation derivations never overshoot their target length. Hence, on words
of length at most `n`, the finite truncation is exactly the restriction of the
infinite exploration—not merely an asymptotic approximation. -/
theorem infiniteGenerated_to_finite {n t : Nat} {openAt : InfiniteSplitEnvironment}
    {w : List Bool} (hw : InfiniteGenerated t openAt w) (hcut : w.length ≤ n) :
    FiniteGenerated n t openAt w := by
  induction hw with
  | food hne hlen => exact .food hne hlen hcut
  | @ligate u v hu hv ho ihu ihv =>
      have huCut : u.length ≤ n := by
        rw [List.length_append] at hcut
        omega
      have hvCut : v.length ≤ n := by
        rw [List.length_append] at hcut
        omega
      exact .ligate (ihu huCut) (ihv hvCut) ho hcut

theorem finiteGenerated_iff_infiniteGenerated {n t : Nat}
    {openAt : InfiniteSplitEnvironment} {w : List Bool} (hcut : w.length ≤ n) :
    FiniteGenerated n t openAt w ↔ InfiniteGenerated t openAt w := by
  constructor
  · exact finiteGenerated_to_infinite
  · intro hw
    exact infiniteGenerated_to_finite hw hcut

end HordijkSteelThreshold
