import Rigidity.Proofs.Green.DarioGuWeightedL2

/-!
# The semigroup property (3.2) of `Φ_C` of Dario–Gu

* `dgShape_anti`: the shape `g(t, r)` is nonincreasing in `t`;
* `dgShape_half_ge`: `g(t, r)/8 ≤ g(t, r/2)`;
* `sum_dgPhi_mul_dgPhi_le`: `Σ_z Φ_C(t₁, z - y) Φ_C(t₂, x - z) ≤ Φ_{C'}(t₁ + t₂, x - y)` for
  `1 ≤ t₁ ≤ t₂` ((3.2), which the source proves "by an explicit computation or by using the
  semigroup property of the law of the random walk on `ℤ^d`", lines 1197-1201; here by the
  explicit computation).

The estimate (4.12), in the form used in (4.21) and (4.23), is `mul_dgPhi_le`
(`s Φ_c(τ, d) ≤ c Φ_{2c}(τ, d)` for `τ ≤ s ≤ d`, in `DarioGuCorrectorLemma`).
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

theorem dgShape_anti {t₁ t₂ r : ℝ} (h0 : 0 < t₁) (h : t₁ ≤ t₂) (hr : 0 ≤ r) :
    dgShape t₂ r ≤ dgShape t₁ r := by
  have h0' : 0 < t₂ := lt_of_lt_of_le h0 h
  by_cases h1 : r ≤ t₁
  · have h2 : r ≤ t₂ := h1.trans h
    unfold dgShape
    rw [if_pos h2, if_pos h1]
    exact div_le_div_of_nonneg_left (sq_nonneg _) h0 h
  · push Not at h1
    rw [dgShape_of_le h0 h1.le]
    have hl : 0 ≤ Real.log (r / t₁) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
    by_cases h2 : r ≤ t₂
    · unfold dgShape
      rw [if_pos h2]
      have : r ^ 2 / t₂ ≤ r := by rw [div_le_iff₀ h0']; nlinarith
      nlinarith
    · push Not at h2
      rw [dgShape_of_le h0' h2.le]
      have hl' : Real.log (r / t₂) ≤ Real.log (r / t₁) :=
        Real.log_le_log (div_pos (by linarith) h0') (div_le_div_of_nonneg_left hr h0 h)
      nlinarith

theorem dgShape_half_ge {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) : dgShape t r / 8 ≤ dgShape t (r / 2) := by
  have hsq := dgShape_le_sq ht hr
  rcases le_or_gt (r / 2) t with h1 | h1
  · have : dgShape t (r / 2) = (r / 2) ^ 2 / t := by unfold dgShape; rw [if_pos h1]
    rw [this]
    have : (r / 2) ^ 2 / t = r ^ 2 / t / 4 := by ring
    rw [this]
    have : 0 ≤ r ^ 2 / t := by positivity
    linarith
  · have hr1 : t ≤ r / 2 := h1.le
    rw [dgShape_of_le ht hr1, dgShape_of_le ht (by linarith)]
    have hpos : 0 < r / 2 / t := div_pos (by linarith) ht
    have hlog : Real.log (r / t) = Real.log 2 + Real.log (r / 2 / t) := by
      rw [← Real.log_mul (by norm_num) hpos.ne']
      congr 1; field_simp
    have hl0 : 0 ≤ Real.log (r / 2 / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    rw [hlog]
    nlinarith

/-- **The semigroup property (3.2) of `Φ_C`** (explicit computation). -/
theorem sum_dgPhi_mul_dgPhi_le {C : ℝ} (hC : 0 < C) : ∃ C' : ℝ, 0 < C' ∧
    ∀ t₁ t₂ : ℝ, 1 ≤ t₁ → t₁ ≤ t₂ → ∀ (x y : Vertex 2) (S : Finset (Vertex 2)),
      ∑ z ∈ S, dgPhi C t₁ (latticeDist z y) * dgPhi C t₂ (latticeDist x z) ≤
        dgPhi C' (t₁ + t₂) (latticeDist x y) := by
  obtain ⟨L, hL, hsum⟩ := sum_exp_neg_dgShape_le (by positivity : (0 : ℝ) < 2 * C)
  set C' := max (16 * C) (2 * C ^ 2 * L) with hC'
  have hC'0 : 0 < C' := lt_max_of_lt_left (by positivity)
  refine ⟨C', hC'0, fun t₁ t₂ ht₁ ht₁₂ x y S => ?_⟩
  have ht₁0 : 0 < t₁ := by linarith
  have ht₂0 : 0 < t₂ := by linarith
  set T := t₁ + t₂ with hT
  have hT0 : 0 < T := by linarith
  set r := latticeDist x y
  set G := dgShape T r
  have hG0 : 0 ≤ G := dgShape_nonneg hT0 (latticeDist_nonneg x y)
  have hpt : ∀ z : Vertex 2, dgPhi C t₁ (latticeDist z y) * dgPhi C t₂ (latticeDist x z) ≤
      C ^ 2 * t₁⁻¹ * t₂⁻¹ * Real.exp (-(G / (16 * C))) *
        Real.exp (-(dgShape t₁ (latticeDist z y) / (2 * C))) := by
    intro z
    have ha := latticeDist_nonneg z y
    have hb := latticeDist_nonneg x z
    have h1 := dgShape_anti ht₁0 (show t₁ ≤ T by linarith) ha
    have h2 := dgShape_anti ht₂0 (show t₂ ≤ T by linarith) hb
    have htri : latticeDist x y ≤ latticeDist z y + latticeDist x z := by
      have h := latticeDist_triangle x z y
      have h' := latticeDist_comm z x
      linarith
    have h3 := dgShape_add_ge hT0 ha hb (latticeDist_nonneg x y) htri
    have h4 : dgShape (2 * T) (latticeDist x y) / 2 = dgShape T (latticeDist x y / 2) := by
      have := dgShape_homog (l := 1 / 2) (t := 2 * T) (r := latticeDist x y) (by norm_num)
        (by positivity)
      rw [show 1 / 2 * (2 * T) = T by ring, show 1 / 2 * latticeDist x y = latticeDist x y / 2 by
        ring] at this
      rw [this]; ring
    have h5 := dgShape_half_ge hT0 (latticeDist_nonneg x y)
    have hg2 := dgShape_nonneg ht₂0 hb
    have hchain : G / 16 + dgShape t₁ (latticeDist z y) / 2 ≤
        dgShape t₁ (latticeDist z y) + dgShape t₂ (latticeDist x z) := by
      have : G = dgShape T (latticeDist x y) := rfl
      rw [this]
      linarith
    rw [dgPhi_eq, dgPhi_eq]
    have hexp : Real.exp (-(dgShape t₁ (latticeDist z y) / C)) *
        Real.exp (-(dgShape t₂ (latticeDist x z) / C)) ≤
        Real.exp (-(G / (16 * C))) * Real.exp (-(dgShape t₁ (latticeDist z y) / (2 * C))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have e1 : G / (16 * C) + dgShape t₁ (latticeDist z y) / (2 * C) =
          (G / 16 + dgShape t₁ (latticeDist z y) / 2) / C := by field_simp
      have e2 : dgShape t₁ (latticeDist z y) / C + dgShape t₂ (latticeDist x z) / C =
          (dgShape t₁ (latticeDist z y) + dgShape t₂ (latticeDist x z)) / C := by ring
      have := div_le_div_of_nonneg_right hchain hC.le
      linarith
    calc C * t₁⁻¹ * Real.exp (-(dgShape t₁ (latticeDist z y) / C)) *
          (C * t₂⁻¹ * Real.exp (-(dgShape t₂ (latticeDist x z) / C)))
        = C ^ 2 * t₁⁻¹ * t₂⁻¹ * (Real.exp (-(dgShape t₁ (latticeDist z y) / C)) *
            Real.exp (-(dgShape t₂ (latticeDist x z) / C))) := by ring
      _ ≤ C ^ 2 * t₁⁻¹ * t₂⁻¹ * (Real.exp (-(G / (16 * C))) *
            Real.exp (-(dgShape t₁ (latticeDist z y) / (2 * C)))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  calc ∑ z ∈ S, dgPhi C t₁ (latticeDist z y) * dgPhi C t₂ (latticeDist x z)
      ≤ ∑ z ∈ S, C ^ 2 * t₁⁻¹ * t₂⁻¹ * Real.exp (-(G / (16 * C))) *
          Real.exp (-(dgShape t₁ (latticeDist z y) / (2 * C))) := Finset.sum_le_sum fun z _ => hpt z
    _ = C ^ 2 * t₁⁻¹ * t₂⁻¹ * Real.exp (-(G / (16 * C))) *
          ∑ z ∈ S, Real.exp (-(dgShape t₁ (latticeDist z y) / (2 * C))) := by rw [Finset.mul_sum]
    _ ≤ C ^ 2 * t₁⁻¹ * t₂⁻¹ * Real.exp (-(G / (16 * C))) * (L * t₁) :=
        mul_le_mul_of_nonneg_left (hsum t₁ ht₁ y S) (by positivity)
    _ = C ^ 2 * L * t₂⁻¹ * Real.exp (-(G / (16 * C))) := by field_simp
    _ ≤ 2 * C ^ 2 * L * T⁻¹ * Real.exp (-(G / (16 * C))) := by
        have : t₂⁻¹ ≤ 2 * T⁻¹ := by
          rw [inv_le_comm₀ ht₂0 (by positivity), mul_inv, inv_inv]
          linarith
        have hE := Real.exp_pos (-(G / (16 * C)))
        nlinarith [mul_pos (mul_pos (sq_pos_of_pos hC) hL) hE]
    _ ≤ dgPhi C' T r := by
        rw [dgPhi_eq]
        have h16 : 16 * C ≤ C' := le_max_left _ _
        have he : Real.exp (-(G / (16 * C))) ≤ Real.exp (-(G / C')) :=
          Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left hG0 (by positivity) h16))
        have hc : 2 * C ^ 2 * L ≤ C' := le_max_right _ _
        have hTi : 0 < T⁻¹ := inv_pos.2 hT0
        calc 2 * C ^ 2 * L * T⁻¹ * Real.exp (-(G / (16 * C)))
            ≤ C' * T⁻¹ * Real.exp (-(G / C')) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hc hTi.le) he (Real.exp_pos _).le
                (by positivity)
          _ = _ := rfl

end Rigidity.Green
