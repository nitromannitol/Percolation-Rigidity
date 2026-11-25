import Rigidity.Proofs.Poincare.HeatDuality
import Rigidity.Proofs.Poincare.GeneralHeatGradient

/-!
# The duality identity for the heat flow on `ℤ^d`

The extension of `HeatDuality.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`.

The lattice form of the duality step (D.21)-(D.23) in the proof of Armstrong, Kuusi and
Mourrat, Proposition D.1, applied to `u` itself: for a finitely supported vector field
`G = (G_j)_{j < d}` with divergence `g(y) = Σ_j (G_j(y - e_j) - G_j(y))`, and `T ≥ 0`,

  `Σ_y g(y) u(y) = Σ_j Σ_y G_j(y) A_j(T, y) + ∫_0^T Σ_i Σ_y ∇_i g(y) A_i(t, y) dt`

with `A_j(t, ·) = Φ_t * ∇_j u` (`tsum_mul_eq_add_integral`). Only the heat averages of `∇u`
enter, so no growth condition on `u` is needed beyond `HeatSummable u`. The proof is the
fundamental theorem of calculus for `A_j`, two summations by parts and the curl-free identity
`∇_i A_j = ∇_j A_i`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

section Parts

variable {S : Finset (Vertex d)} {G : Vertex d → ℝ}

theorem summable_mul_of_supp (hG : ∀ y ∉ S, G y = 0) (F : Vertex d → ℝ) :
    Summable fun y => G y * F y :=
  summable_of_ne_finset_zero (s := S) fun y hy => by rw [hG y hy, zero_mul]

theorem supp_shift (hG : ∀ y ∉ S, G y = 0) (e : Vertex d) :
    ∀ y ∉ S.image (· - e), G (y + e) = 0 := by
  intro y hy
  refine hG _ fun h => hy ?_
  rw [Finset.mem_image]
  exact ⟨y + e, h, by abel⟩

theorem tsum_mul_sub_eq (G F : Vertex d → ℝ) (e : Vertex d) :
    ∑' y, G y * F (y - e) = ∑' y, G (y + e) * F y := by
  rw [← (Equiv.addRight e).tsum_eq]
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

theorem tsum_mul_add_eq (G F : Vertex d → ℝ) (e : Vertex d) :
    ∑' y, G y * F (y + e) = ∑' y, G (y - e) * F y := by
  have h := tsum_mul_sub_eq G F (-e)
  simp only [sub_neg_eq_add, ← sub_eq_add_neg] at h
  exact h

/-- **Summation by parts**: `Σ_y H(y) (F(y + e) - F(y)) = Σ_y (H(y - e) - H(y)) F(y)`. -/
theorem tsum_mul_fd_eq (hH : ∀ y ∉ S, G y = 0) (F : Vertex d → ℝ) (e : Vertex d) :
    ∑' y, G y * (F (y + e) - F y) = ∑' y, (G (y - e) - G y) * F y := by
  have h1 := summable_mul_of_supp hH (fun y => F (y + e))
  have h2 := summable_mul_of_supp hH F
  have h3 := summable_mul_of_supp (supp_shift hH (-e)) F
  simp only [← sub_eq_add_neg] at h3
  have e1 : ∀ y, G y * (F (y + e) - F y) = G y * F (y + e) - G y * F y := fun y => by ring
  have e2 : ∀ y, (G (y - e) - G y) * F y = G (y - e) * F y - G y * F y := fun y => by ring
  simp only [e1, e2]
  rw [h1.tsum_sub h2, h3.tsum_sub h2, tsum_mul_add_eq]

/-- **Summation by parts, second order**:
`Σ_y G(y) (F(y + e) + F(y - e) - 2F(y)) = -Σ_y ∇_e G(y) ∇_e F(y)`. -/
theorem tsum_mul_second_eq (hG : ∀ y ∉ S, G y = 0) (F : Vertex d → ℝ) (e : Vertex d) :
    ∑' y, G y * (F (y + e) + F (y - e) - 2 * F y) =
      -∑' y, (G (y + e) - G y) * (F (y + e) - F y) := by
  have hGe := supp_shift hG e
  have s1 := summable_mul_of_supp hG (fun y => F (y + e))
  have s2 := summable_mul_of_supp hG (fun y => F (y - e))
  have s3 := summable_mul_of_supp hG F
  have s4 := summable_mul_of_supp hGe (fun y => F (y + e))
  have s5 := summable_mul_of_supp hGe F
  have e1 : ∀ y, G y * (F (y + e) + F (y - e) - 2 * F y) =
      G y * F (y + e) + G y * F (y - e) - 2 * (G y * F y) := fun y => by ring
  have e2 : ∀ y, (G (y + e) - G y) * (F (y + e) - F y) =
      G (y + e) * F (y + e) - G (y + e) * F y - G y * F (y + e) + G y * F y := fun y => by ring
  simp only [e1, e2]
  rw [(s1.add s2).tsum_sub (s3.mul_left 2), s1.tsum_add s2, tsum_mul_left,
    ((s4.sub s5).sub s1).tsum_add s3, (s4.sub s5).tsum_sub s1, s4.tsum_sub s5,
    tsum_mul_sub_eq G F e]
  have : ∑' y, G (y + e) * F (y + e) = ∑' y, G y * F y :=
    (Equiv.addRight e).tsum_eq fun y => G y * F y
  rw [this]
  ring

end Parts

variable {u : Vertex d → ℝ}

/-- The divergence `g(y) = Σ_j (G_j(y - e_j) - G_j(y))` of a vector field. -/
def divField (G : Fin d → Vertex d → ℝ) (y : Vertex d) : ℝ :=
  ∑ j : Fin d, (G j (y - unit j) - G j y)

theorem divField_add (G : Fin d → Vertex d → ℝ) (y e : Vertex d) :
    divField G (y + e) - divField G y =
      ∑ j : Fin d, ((G j (y - unit j + e) - G j (y - unit j)) - (G j (y + e) - G j y)) := by
  simp only [divField]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show y + e - unit j = y - unit j + e by abel]
  ring

/-- The integrand of the duality identity: `Σ_j Σ_y G_j lap A_j = -Σ_i Σ_y ∇_i g A_i`. -/
theorem tsum_mul_lap_heatGrad [NeZero d] (hu : HeatSummable u) {S : Finset (Vertex d)}
    {G : Fin d → Vertex d → ℝ} (hG : ∀ j, ∀ y ∉ S, G j y = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j : Fin d, ∑' y, G j y * lap (heatGrad u j t) y =
      -∑ i : Fin d, ∑' y, (divField G (y + unit i) - divField G y) * heatGrad u i t y := by
  set A := fun j => heatGrad u j t with hA
  have hlap : ∀ j y, lap (A j) y = ∑ i : Fin d,
      (A j (y + unit i) + A j (y - unit i) - 2 * A j y) := by
    intro j y
    simp only [lap, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  -- second-order summation by parts in each direction
  have h1 : ∀ j, ∑' y, G j y * lap (A j) y =
      -∑ i : Fin d, ∑' y, (G j (y + unit i) - G j y) * (A j (y + unit i) - A j y) := by
    intro j
    simp only [hlap, Finset.mul_sum]
    rw [Summable.tsum_finsetSum fun i _ => summable_mul_of_supp (hG j) _]
    simp only [tsum_mul_second_eq (hG j), Finset.sum_neg_distrib]
  -- the curl-free identity
  have hcurl : ∀ i j y, A j (y + unit i) - A j y = A i (y + unit j) - A i y :=
    fun i j y => heatGrad_add_unit_sub hu i j ht y
  have h2 : ∀ i j, ∑' y, (G j (y + unit i) - G j y) * (A j (y + unit i) - A j y) =
      ∑' y, ((G j (y - unit j + unit i) - G j (y - unit j)) - (G j (y + unit i) - G j y)) *
        A i y := by
    intro i j
    simp only [hcurl i j]
    have hD : ∀ y ∉ S ∪ S.image (· - unit i), (G j (y + unit i) - G j y) = 0 := by
      intro y hy
      rw [Finset.mem_union, not_or] at hy
      rw [supp_shift (hG j) (unit i) y hy.2, hG j y hy.1, sub_zero]
    rw [tsum_mul_fd_eq hD]
  calc ∑ j : Fin d, ∑' y, G j y * lap (A j) y
      = -∑ j : Fin d, ∑ i : Fin d, ∑' y, (G j (y + unit i) - G j y) *
          (A j (y + unit i) - A j y) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => h1 j
    _ = -∑ i : Fin d, ∑ j : Fin d, ∑' y, ((G j (y - unit j + unit i) - G j (y - unit j)) -
          (G j (y + unit i) - G j y)) * A i y := by
        rw [Finset.sum_comm]
        simp only [h2]
    _ = -∑ i : Fin d, ∑' y, (divField G (y + unit i) - divField G y) * A i y := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have hs : ∀ j : Fin d, Summable fun y => ((G j (y - unit j + unit i) - G j (y - unit j)) -
            (G j (y + unit i) - G j y)) * A i y := by
          intro j
          refine summable_of_ne_finset_zero (s := S.image (· + unit j) ∪
            (S.image (· + unit j - unit i) ∪ (S ∪ S.image (· - unit i)))) fun y hy => ?_
          simp only [Finset.mem_union, not_or] at hy
          have a1 : G j (y - unit j) = 0 := hG j _ fun h => hy.1 (Finset.mem_image.2
            ⟨_, h, by abel⟩)
          have a2 : G j (y - unit j + unit i) = 0 := hG j _ fun h => hy.2.1 (Finset.mem_image.2
            ⟨_, h, by abel⟩)
          have a3 : G j y = 0 := hG j y hy.2.2.1
          have a4 : G j (y + unit i) = 0 := supp_shift (hG j) (unit i) y hy.2.2.2
          rw [a1, a2, a3, a4]
          ring
        rw [← Summable.tsum_finsetSum fun j _ => hs j]
        refine tsum_congr fun y => ?_
        rw [← Finset.sum_mul, divField_add]

/-- `Σ_y g(y) u(y) = Σ_j Σ_y G_j(y) ∇_j u(y)` for a finitely supported field. -/
theorem tsum_divField_mul (u : Vertex d → ℝ) {S : Finset (Vertex d)}
    {G : Fin d → Vertex d → ℝ} (hG : ∀ j, ∀ y ∉ S, G j y = 0) :
    ∑' y, divField G y * u y = ∑ j : Fin d, ∑' y, G j y * fd u j y := by
  have hs : ∀ j : Fin d, Summable fun y => (G j (y - unit j) - G j y) * u y := by
    intro j
    refine summable_of_ne_finset_zero (s := S ∪ S.image (· + unit j)) fun y hy => ?_
    rw [Finset.mem_union, not_or] at hy
    rw [hG j y hy.1, hG j _ fun h => hy.2 (Finset.mem_image.2 ⟨_, h, by abel⟩)]
    ring
  simp only [divField, Finset.sum_mul]
  rw [Summable.tsum_finsetSum fun j _ => hs j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tsum_mul_fd_eq (hG j) u (unit j)]
  rfl

/-- **The duality identity**. -/
theorem tsum_mul_eq_add_integral [NeZero d] (hu : HeatSummable u) {S : Finset (Vertex d)}
    {G : Fin d → Vertex d → ℝ} (hG : ∀ j, ∀ y ∉ S, G j y = 0) {T : ℝ} (hT : 0 ≤ T) :
    ∑' y, divField G y * u y = ∑ j : Fin d, ∑' y, G j y * heatGrad u j T y +
      ∫ t in (0 : ℝ)..T, ∑ i : Fin d, ∑' y,
        (divField G (y + unit i) - divField G y) * heatGrad u i t y := by
  have hcont : ∀ j y, ContinuousOn (fun t => lap (heatGrad u j t) y) (Set.Icc 0 T) := by
    intro j y
    have h := fun w => continuousOn_heatGrad hu j hT w
    simp only [lap]
    exact (continuousOn_finsetSum _ fun i _ => (h _).add (h _)).sub
      (continuousOn_const.mul (h _))
  have hfin : ∀ (j : Fin d) (F : Vertex d → ℝ), ∑' y, G j y * F y = ∑ y ∈ S, G j y * F y :=
    fun j F => tsum_eq_sum fun y hy => by rw [hG j y hy, zero_mul]
  have hint : ∀ j y, IntervalIntegrable (fun t => G j y * lap (heatGrad u j t) y) volume 0 T :=
    fun j y => ((hcont j y).intervalIntegrable_of_Icc hT).const_mul _
  -- the fundamental theorem of calculus, summed against `G`
  have hftc : ∑ j : Fin d, ∑' y, G j y * heatGrad u j T y -
      ∑ j : Fin d, ∑' y, G j y * fd u j y =
      ∫ t in (0 : ℝ)..T, ∑ j : Fin d, ∑' y, G j y * lap (heatGrad u j t) y := by
    simp only [hfin]
    have hint2 : ∀ j, IntervalIntegrable
        (fun t => ∑ y ∈ S, G j y * lap (heatGrad u j t) y) volume 0 T := fun j =>
      (continuousOn_finsetSum S fun y _ => continuousOn_const.mul (hcont j y)
        ).intervalIntegrable_of_Icc hT
    have e1 : ∫ t in (0 : ℝ)..T, ∑ j : Fin d, ∑ y ∈ S, G j y * lap (heatGrad u j t) y =
        ∑ j : Fin d, ∫ t in (0 : ℝ)..T, ∑ y ∈ S, G j y * lap (heatGrad u j t) y :=
      intervalIntegral.integral_finsetSum fun j _ => hint2 j
    have e2 : ∀ j, ∫ t in (0 : ℝ)..T, ∑ y ∈ S, G j y * lap (heatGrad u j t) y =
        ∑ y ∈ S, ∫ t in (0 : ℝ)..T, G j y * lap (heatGrad u j t) y := fun j =>
      intervalIntegral.integral_finsetSum fun y _ => hint j y
    rw [e1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_sub, heatGrad_sub_eq_integral hu j hT y, intervalIntegral.integral_const_mul]
  have hcongr : ∫ t in (0 : ℝ)..T, ∑ j : Fin d, ∑' y, G j y * lap (heatGrad u j t) y =
      ∫ t in (0 : ℝ)..T, -∑ i : Fin d, ∑' y,
        (divField G (y + unit i) - divField G y) * heatGrad u i t y := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hT] at ht
    exact tsum_mul_lap_heatGrad hu hG ht.1
  rw [hcongr, intervalIntegral.integral_neg, ← tsum_divField_mul u hG] at hftc
  linarith

end Rigidity.Poincare.GeneralDim
