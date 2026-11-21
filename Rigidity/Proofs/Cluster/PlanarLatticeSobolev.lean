import Rigidity.Proofs.Cluster.CoarseSobolev

/-!
# The Sobolev inequality on a square of the planar lattice

For a function `F` on the grid `{0, …, L-1}²`,
`∑_p (F(p) - (F))² ≤ (1/2) (∑ |horizontal increments| + ∑ |vertical increments|)²`,
the planar Sobolev–Poincaré inequality from `L¹` to `L²` with a constant independent of `L`. The
proof writes `∑_p (F(p) - (F))² = (2L²)⁻¹ ∑_{p,q} (F(p) - F(q))²` and bounds `|F(p) - F(q)|` by
the variation along the row of `p` and the column of `q`, and also by the variation along the
column of `p` and the row of `q`; the product of the two bounds sums to `L² (R + C)²`.
-/

open Finset

namespace Rigidity.Percolation

/-- The oscillation of a sequence between two indices below `L` is at most its total variation on
`{0, …, L-1}`. -/
theorem abs_sub_le_sum_range_abs_sub (g : ℕ → ℝ) {i j L : ℕ} (hi : i < L) (hj : j < L) :
    |g i - g j| ≤ ∑ k ∈ range (L - 1), |g (k + 1) - g k| := by
  have key : ∀ a b : ℕ, a ≤ b → b < L → |g b - g a| ≤ ∑ k ∈ range (L - 1), |g (k + 1) - g k| := by
    intro a b hab hb
    have htel : g b - g a = ∑ k ∈ range (b - a), (g (a + k + 1) - g (a + k)) := by
      have h := Finset.sum_range_sub (fun k => g (a + k)) (b - a)
      simp only [add_zero, ← add_assoc] at h
      rw [h, Nat.add_sub_cancel' hab]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hmap : ∑ k ∈ range (b - a), |g (a + k + 1) - g (a + k)| =
        ∑ m ∈ (range (b - a)).map (addLeftEmbedding a), |g (m + 1) - g m| := by
      rw [Finset.sum_map]
      rfl
    rw [hmap]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hm
    rw [Finset.mem_range] at hk ⊢
    simp only [addLeftEmbedding_apply]
    omega
  rcases le_total i j with h | h
  · rw [abs_sub_comm]
    exact key i j h hj
  · exact key j i h hi

/-- `∑_{x ∈ D} (f x - (f)_D)² = (2|D|)⁻¹ ∑_{x, y ∈ D} (f x - f y)²`. -/
theorem sum_sq_sub_mean_eq {ι : Type*} (D : Finset ι) (f : ι → ℝ) (hD : D.Nonempty) :
    ∑ x ∈ D, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
      (∑ x ∈ D, ∑ y ∈ D, (f x - f y) ^ 2) / (2 * D.card) := by
  have hn : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD.card_pos.ne'
  have h1 : ∑ x ∈ D, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
      ∑ x ∈ D, f x ^ 2 - (∑ y ∈ D, f y) ^ 2 / D.card := by
    have e : ∀ x, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
        f x ^ 2 - 2 * ((∑ y ∈ D, f y) / D.card) * f x + ((∑ y ∈ D, f y) / D.card) ^ 2 := by
      intro x
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  have h2 : ∑ x ∈ D, ∑ y ∈ D, (f x - f y) ^ 2 =
      2 * D.card * ∑ x ∈ D, f x ^ 2 - 2 * (∑ y ∈ D, f y) ^ 2 := by
    have e : ∀ x y, (f x - f y) ^ 2 = f x ^ 2 - 2 * f x * f y + f y ^ 2 := by
      intro x y
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [h1, h2]
  field_simp

/-- The double sum `∑_{p, q ∈ G} (a p + b q)(c p + e q)`. -/
theorem sum_sum_add_mul_add {ι : Type*} (G : Finset ι) (a b c e : ι → ℝ) :
    ∑ p ∈ G, ∑ q ∈ G, (a p + b q) * (c p + e q) =
      G.card * ∑ p ∈ G, a p * c p + (∑ p ∈ G, a p) * (∑ q ∈ G, e q) +
        (∑ q ∈ G, b q) * (∑ p ∈ G, c p) + G.card * ∑ q ∈ G, b q * e q := by
  have e1 : ∀ p q, (a p + b q) * (c p + e q) =
      a p * c p + a p * e q + b q * c p + b q * e q := by
    intro p q
    ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]

/-- The variation of `F` along the row of height `k` of the grid `{0, …, L-1}²`. -/
noncomputable def gridRowVar (F : ℕ × ℕ → ℝ) (L k : ℕ) : ℝ :=
  ∑ a ∈ range (L - 1), |F (a + 1, k) - F (a, k)|

/-- The variation of `F` along the column of abscissa `a` of the grid `{0, …, L-1}²`. -/
noncomputable def gridColVar (F : ℕ × ℕ → ℝ) (L a : ℕ) : ℝ :=
  ∑ b ∈ range (L - 1), |F (a, b + 1) - F (a, b)|

theorem gridRowVar_nonneg (F : ℕ × ℕ → ℝ) (L k : ℕ) : 0 ≤ gridRowVar F L k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gridColVar_nonneg (F : ℕ × ℕ → ℝ) (L a : ℕ) : 0 ≤ gridColVar F L a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The planar grid Sobolev inequality.** For `F` on `{0, …, L-1}²`,
`∑_p (F p - (F))² ≤ (1/2) (∑_k rowVar k + ∑_a colVar a)²`. -/
theorem sum_sq_sub_mean_le_grid (L : ℕ) (hL : 0 < L) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ range L ×ˢ range L,
        (F p - (∑ q ∈ range L ×ˢ range L, F q) / (range L ×ˢ range L).card) ^ 2 ≤
      (1 / 2) * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 := by
  have hGne : (range L ×ˢ range L).Nonempty := ⟨(0, 0), by simp [hL]⟩
  have hGcard : ((range L ×ˢ range L).card : ℝ) = (L : ℝ) ^ 2 := by
    rw [Finset.card_product, Finset.card_range]
    push_cast
    ring
  have hsq : ∀ p ∈ range L ×ˢ range L, ∀ q ∈ range L ×ˢ range L,
      (F p - F q) ^ 2 ≤ (gridRowVar F L p.2 + gridColVar F L q.1) *
        (gridColVar F L p.1 + gridRowVar F L q.2) := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp hq
    have h1 : |F (p1, p2) - F (q1, q2)| ≤ gridRowVar F L p2 + gridColVar F L q1 := by
      have ha := abs_sub_le_sum_range_abs_sub (fun a => F (a, p2)) hp.1 hq.1
      have hb := abs_sub_le_sum_range_abs_sub (fun b => F (q1, b)) hp.2 hq.2
      calc |F (p1, p2) - F (q1, q2)|
          = |(F (p1, p2) - F (q1, p2)) + (F (q1, p2) - F (q1, q2))| := by congr 1; ring
        _ ≤ |F (p1, p2) - F (q1, p2)| + |F (q1, p2) - F (q1, q2)| := abs_add_le _ _
        _ ≤ gridRowVar F L p2 + gridColVar F L q1 := add_le_add ha hb
    have h2 : |F (p1, p2) - F (q1, q2)| ≤ gridColVar F L p1 + gridRowVar F L q2 := by
      have ha := abs_sub_le_sum_range_abs_sub (fun b => F (p1, b)) hp.2 hq.2
      have hb := abs_sub_le_sum_range_abs_sub (fun a => F (a, q2)) hp.1 hq.1
      calc |F (p1, p2) - F (q1, q2)|
          = |(F (p1, p2) - F (p1, q2)) + (F (p1, q2) - F (q1, q2))| := by congr 1; ring
        _ ≤ |F (p1, p2) - F (p1, q2)| + |F (p1, q2) - F (q1, q2)| := abs_add_le _ _
        _ ≤ gridColVar F L p1 + gridRowVar F L q2 := add_le_add ha hb
    rw [← sq_abs, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _)
      (add_nonneg (gridRowVar_nonneg _ _ _) (gridColVar_nonneg _ _ _))
  have hsum2 : ∀ φ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.2 = L * ∑ k ∈ range L, φ k := by
    intro φ
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum1 : ∀ φ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.1 = L * ∑ k ∈ range L, φ k := by
    intro φ
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum12 : ∀ φ ψ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.2 * ψ p.1 =
      (∑ k ∈ range L, φ k) * ∑ k ∈ range L, ψ k := by
    intro φ ψ
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_comm]
  have hsum21 : ∀ φ ψ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, ψ p.1 * φ p.2 =
      (∑ k ∈ range L, φ k) * ∑ k ∈ range L, ψ k := by
    intro φ ψ
    rw [← hsum12 φ ψ]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hdouble : ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2 ≤
      (L : ℝ) ^ 2 * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 := by
    calc ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2
        ≤ ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L,
            (gridRowVar F L p.2 + gridColVar F L q.1) *
              (gridColVar F L p.1 + gridRowVar F L q.2) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hsq p hp q hq
      _ = _ := by
          rw [sum_sum_add_mul_add (range L ×ˢ range L) (fun p => gridRowVar F L p.2)
            (fun q => gridColVar F L q.1) (fun p => gridColVar F L p.1)
            (fun q => gridRowVar F L q.2)]
          rw [hsum12 (gridRowVar F L) (gridColVar F L), hsum21 (gridRowVar F L) (gridColVar F L),
            hsum2 (gridRowVar F L), hsum1 (gridColVar F L), hGcard]
          ring
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  rw [sum_sq_sub_mean_eq _ F hGne, hGcard, div_le_iff₀ (by positivity)]
  calc ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2
      ≤ (L : ℝ) ^ 2 * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 :=
        hdouble
    _ = _ := by ring

end Rigidity.Percolation
