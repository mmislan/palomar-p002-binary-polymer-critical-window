module

public import proofs.HordijkSteelThreshold.InfiniteLigation

@[expose] public section

namespace HordijkSteelThreshold

/-- Ordinary reversible generation in the countable word universe. Unlike
the older ligation-only exploration, this includes recovery of both factors. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v

inductive FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) (hN : w.length ≤ N) :
      FiniteReversibleGenerated N L field w
  | ligate {u v} (hu : FiniteReversibleGenerated N L field u)
      (hv : FiniteReversibleGenerated N L field v) (ho : field (u ++ v) u.length)
      (hN : (u ++ v).length ≤ N) : FiniteReversibleGenerated N L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field v

theorem finiteReversibleGenerated_mono_cap {N M L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} (hNM : N ≤ M)
    (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated M L field w := by
  induction h with
  | food hn hL hN => exact .food hn hL (hN.trans hNM)
  | ligate _ _ ho hN ihu ihv => exact .ligate ihu ihv ho (hN.trans hNM)
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

theorem finiteReversibleGenerated_to_infinite {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : InfiniteReversibleGenerated L field w := by
  induction h with
  | food hn hL _ => exact .food hn hL
  | ligate _ _ ho _ ihu ihv => exact .ligate ihu ihv ho
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

/-- Every reversible generation has a finite cap certificate, but this cap
need not be the target's length: cleavage can first require a longer product. -/
theorem infiniteReversibleGenerated_finite_certificate {L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    ∃ N, FiniteReversibleGenerated N L field w := by
  induction h with
  | @food w hn hL => exact ⟨w.length, .food hn hL le_rfl⟩
  | @ligate u v _ _ ho ihu ihv =>
    obtain ⟨N, hN⟩ := ihu
    obtain ⟨M, hM⟩ := ihv
    refine ⟨max (max N M) (u ++ v).length, .ligate
      (finiteReversibleGenerated_mono_cap (by omega) hN)
      (finiteReversibleGenerated_mono_cap (by omega) hM) ho (by omega)⟩
  | left hu hv _ ho ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, .left hu hv hN ho⟩
  | right hu hv _ ho ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, .right hu hv hN ho⟩

theorem infiniteReversibleGenerated_iff_finite_certificate {L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} :
    InfiniteReversibleGenerated L field w ↔ ∃ N, FiniteReversibleGenerated N L field w :=
  ⟨infiniteReversibleGenerated_finite_certificate,
    fun ⟨_, h⟩ => finiteReversibleGenerated_to_infinite h⟩

end HordijkSteelThreshold
