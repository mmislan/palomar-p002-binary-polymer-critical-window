module

public import proofs.HordijkSteelThreshold.WordCoreAvoidance

@[expose] public section

namespace HordijkSteelThreshold

/-- Sliding one letter through a fixed-length word makes its label independent of the word. -/
theorem fixedLength_shift_constant {A : Type*} (g : List Bool → A) (M : ℕ)
    (hshift : ∀ (a b : Bool) (t : List Bool), t.length + 1 = M →
      g (a :: t) = g (t ++ [b]))
    (u v : List Bool) (hu : u.length = M) (hv : v.length = M) : g u = g v := by
  have rotate : ∀ front : List Bool, ∀ middle suffix : List Bool,
      front.length = suffix.length → front.length + middle.length = M →
      g (front ++ middle) = g (middle ++ suffix) := by
    intro front
    induction front with
    | nil =>
      intro middle suffix hs _
      cases suffix <;> simp_all
    | cons a front ih =>
      intro middle suffix hs ht
      cases suffix with
      | nil => simp at hs
      | cons b suffix =>
        have h1 := hshift a b (front ++ middle) (by
          simp only [List.length_cons, List.length_append] at *
          omega)
        have h2 := ih (middle ++ [b]) suffix (by simpa using hs) (by
          simp only [List.length_append, List.length_cons, List.length_nil] at *
          omega)
        rw [List.append_assoc] at h1
        simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h1.trans h2
  simpa using rotate u [] v (hu.trans hv.symm) (by simpa using hu)

/-- If both parent moves above M preserve labels, all words from M through N share a label.
The spare level M+1 is essential. -/
theorem highBand_label_constant {A : Type*} (g : List Bool → A) (M N : ℕ)
    (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N →
      g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N)
    (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
  have hshift : ∀ (a b : Bool) (t : List Bool), t.length + 1 = M →
      g (a :: t) = g (t ++ [b]) := by
    intro a b t ht
    have h := hparent ((a :: t) ++ [b]) (by simp; omega) (by simp; omega)
    simp only [List.dropLast_concat] at h
    simpa only [List.cons_append, List.tail_cons] using h.2.symm.trans h.1
  let base := List.replicate M false
  have descend : ∀ n : ℕ, ∀ s : List Bool, s.length = n → M ≤ n → n ≤ N → g s = g base := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hlo hhi
      by_cases he : n = M
      · exact fixedLength_shift_constant g M hshift s base (hs.trans he) (by simp [base])
      · have hlt : M < s.length := by omega
        have hlen : s.dropLast.length < n := by simp; omega
        exact (hparent s hlt (by omega)).2.trans
          (ih _ hlen s.dropLast rfl (by simp; omega) (by simp; omega))
  exact (descend _ u rfl hu.1 hu.2).trans (descend _ v rfl hv.1 hv.2).symm

end HordijkSteelThreshold
