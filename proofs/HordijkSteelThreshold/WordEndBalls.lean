module

public import proofs.HordijkSteelThreshold.WordMolecularAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- Six end edits and a stay-put choice; duplicates only decrease cardinality. -/
def endWordChoices (s : List Bool) : Finset (List Bool) :=
  insert s (insert s.tail (insert s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b])))))

theorem endWordChoices_card (s : List Bool) : (endWordChoices s).card ≤ 7 := by
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun b => b :: s)
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun b => s ++ [b])
  have hu := Finset.card_union_le
    ((Finset.univ : Finset Bool).image (fun b => b :: s))
    ((Finset.univ : Finset Bool).image (fun b => s ++ [b]))
  have ha := Finset.card_insert_le s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b])))
  have hb := Finset.card_insert_le s.tail (insert s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b]))))
  have hc := Finset.card_insert_le s (insert s.tail (insert s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b])))))
  simp only [Finset.card_univ, Fintype.card_bool] at h1 h2
  unfold endWordChoices
  omega

theorem endWord_adj_mem_choices {u v : List Bool} (h : endWordGraph.Adj u v) :
    v ∈ endWordChoices u := by
  obtain ⟨b, h | h | h | h⟩ := h
  · subst v; cases b <;> simp [endWordChoices]
  · subst u; cases b <;> simp [endWordChoices]
  · subst v; cases b <;> simp [endWordChoices]
  · subst u; cases b <;> simp [endWordChoices]

def endWordBall : ℕ → List Bool → Finset (List Bool)
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion (endWordBall k)

theorem endWordBall_self (k : ℕ) (s : List Bool) : s ∈ endWordBall k s := by
  induction k with
  | zero => simp [endWordBall]
  | succ k ih =>
    exact Finset.mem_biUnion.mpr ⟨s, by simp [endWordChoices], ih⟩

theorem endWordBall_card (k : ℕ) (s : List Bool) : (endWordBall k s).card ≤ 7 ^ k := by
  induction k generalizing s with
  | zero => simp [endWordBall]
  | succ k ih =>
    calc
      (endWordBall (k + 1) s).card ≤ ∑ v ∈ endWordChoices s, (endWordBall k v).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ endWordChoices s, 7 ^ k := Finset.sum_le_sum (fun v _ => ih v)
      _ ≤ 7 * 7 ^ k := by
        simp only [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (endWordChoices_card s)
      _ = 7 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

theorem endWord_walk_mem_ball {u v : List Bool} (p : endWordGraph.Walk u v)
    (k : ℕ) (hk : p.length ≤ k) : v ∈ endWordBall k u := by
  induction k generalizing u v with
  | zero =>
    have he := p.eq_of_length_eq_zero (by omega)
    subst v
    exact endWordBall_self 0 u
  | succ k ih =>
    cases p with
    | nil => exact endWordBall_self (k + 1) u
    | @cons u v w ha p =>
      apply Finset.mem_biUnion.mpr
      refine ⟨v, endWord_adj_mem_choices ha, ih p ?_⟩
      simp only [Walk.length_cons] at hk
      omega

end HordijkSteelThreshold
