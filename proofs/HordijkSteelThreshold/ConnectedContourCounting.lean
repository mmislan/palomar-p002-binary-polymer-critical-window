module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Insert an out-and-back excursion at a visited vertex. -/
theorem walk_insert_excursion {r : V} (p : G.Walk r r) {u v : V}
    (hu : u ∈ p.support) (huv : G.Adj u v) :
    ∃ q : G.Walk r r, q.length = p.length + 2 ∧
      q.support.toFinset = insert v p.support.toFinset := by
  let q := (p.takeUntil u hu).append
    ((Walk.cons huv (Walk.cons huv.symm Walk.nil)).append (p.dropUntil u hu))
  refine ⟨q, ?_, ?_⟩
  · have h := congrArg Walk.length (p.take_spec hu)
    simp only [Walk.length_append] at h
    simp only [q, Walk.length_append, Walk.length_cons, Walk.length_nil]
    omega
  · ext x
    have h : x ∈ p.support ↔ x ∈ (p.takeUntil u hu).support ∨
        x ∈ (p.dropUntil u hu).support := by
      conv_lhs => rw [← p.take_spec hu]
      exact Walk.mem_support_append_iff _ _
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
      Walk.support_cons, Walk.support_nil, List.mem_cons]
    have hu' : u ∈ (p.takeUntil u hu).support := Walk.end_mem_support _
    grind

/-- A cut-crossing property constructs a covering closed walk of optimal tree-tour length.
The property will be supplied by connectedness of the actual contour. -/
theorem finite_connected_covering_tour (C : Finset V) (r : V) (hr : r ∈ C)
    (hcross : ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    ∃ p : G.Walk r r, p.support.toFinset = C ∧ p.length = 2 * (C.card - 1) := by
  have extend : ∀ k : ℕ, ∀ p : G.Walk r r,
      p.support.toFinset ⊆ C →
      p.length = 2 * (p.support.toFinset.card - 1) →
      (C \ p.support.toFinset).card = k →
      ∃ q : G.Walk r r, q.support.toFinset = C ∧ q.length = 2 * (C.card - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hp hl hk
      by_cases he : p.support.toFinset = C
      · exact ⟨p, he, by simpa [he] using hl⟩
      · have hrp : r ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
        obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hp hrp he
        obtain ⟨q, hql, hqs⟩ := walk_insert_excursion G p (List.mem_toFinset.mp hu) huv
        have hqsub : q.support.toFinset ⊆ C := by
          rw [hqs]
          exact Finset.insert_subset hv hp
        have hc : q.support.toFinset.card = p.support.toFinset.card + 1 := by
          rw [hqs, Finset.card_insert_of_notMem hvs]
        have hpos : 0 < p.support.toFinset.card := Finset.card_pos.mpr ⟨r, hrp⟩
        have hqlen : q.length = 2 * (q.support.toFinset.card - 1) := by omega
        have hsmall : (C \ q.support.toFinset).card < k := by
          have h1 := Finset.card_sdiff_add_card_eq_card hp
          have h2 := Finset.card_sdiff_add_card_eq_card hqsub
          omega
        exact ih _ hsmall q hqsub hqlen rfl
  apply extend _ Walk.nil
  · simpa using hr
  · simp
  · rfl

variable [Fintype V] [DecidableRel G.Adj]

/-- Specifying both endpoints cannot increase the degree-based walk count. -/
theorem card_walks_le_degree_pow (d : ℕ) (hd : ∀ v, (G.neighborFinset v).card ≤ d)
    (n : ℕ) (u v : V) : (G.finsetWalkLength n u v).card ≤ d ^ n := by
  induction n generalizing u v with
  | zero =>
    simp only [finsetWalkLength]
    split
    · rename_i h
      subst v
      simp
    · simp
  | succ n ih =>
    simp only [finsetWalkLength]
    refine Finset.card_biUnion_le.trans ?_
    simp only [Finset.card_map]
    calc
      ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card
          ≤ ∑ _w : G.neighborSet u, d ^ n := Finset.sum_le_sum (fun w _ => ih w v)
      _ ≤ d * d ^ n := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        apply Nat.mul_le_mul_right
        simpa [SimpleGraph.neighborFinset] using hd u
      _ = d ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Fixed-anchor connected contours are encoded by walks, with no ambient vertex factor. -/
theorem card_connected_contours_le (d b : ℕ)
    (hd : ∀ v, (G.neighborFinset v).card ≤ d) (r : V)
    (family : Finset (Finset V))
    (hfamily : ∀ C ∈ family, C.card = b ∧ r ∈ C ∧
      ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
        ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    family.card ≤ d ^ (2 * (b - 1)) := by
  have hs : family ⊆ (G.finsetWalkLength (2 * (b - 1)) r r).image
      (fun p => p.support.toFinset) := by
    intro C hC
    obtain ⟨hb, hr, hc⟩ := hfamily C hC
    obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour G C r hr hc
    exact Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr (by simpa [hb] using hl), hp⟩
  exact (Finset.card_le_card hs).trans
    (Finset.card_image_le.trans (card_walks_le_degree_pow G d hd _ r r))

end HordijkSteelThreshold
