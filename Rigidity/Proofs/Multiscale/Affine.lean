import Rigidity.Proofs.Multiscale.Poincare

/-!
# The multiscale Poincaré inequality relative to an affine function

The form in which Armstrong–Dario apply Proposition 8.2 in §5 (first display of the proof of
Lemma 5.8): for a slope `ξ ∈ ℝ^d` and `w = u - ℓ_ξ`, `ℓ_ξ(x) = ξ · x`,

`‖w - (w)_{□_m}‖²_{L̲²} ≤ C 3^{2n} ‖∇w‖²_{L̲²}
  + C (Σ_{k=n}^{m-1} 3^k (|3^k ℤ^d ∩ □_m|⁻¹ Σ_y
      | |□_k|⁻¹ ⟨∇u⟩_{y + □_k} - (1 - 3^{-k}) ξ |²)^{1/2})²`.

The spatial sum of the gradient of `ℓ_ξ` over a subcube of scale `k` is `(1 - 3^{-k}) |□_k| ξ`,
since the subcube has `3^{k(d-1)} (3^k - 1)` edges in each direction. Armstrong and Dario compare
`|□_k|⁻¹ ⟨∇u⟩` with `ξ` itself; the difference `3^{-k} ξ` adds at most `(m - n) |ξ|` to the sum.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb.Percolation

variable {d : ℕ}

/-- The affine function `ℓ_ξ(x) = ξ · x`. -/
noncomputable def affineFun (ξ : Fin d → ℝ) (x : Vertex d) : ℝ := ∑ i, ξ i * (x i : ℝ)

/-- The spatial sum of the gradient is additive in the function. -/
theorem gradSum_sub (B : Finset (Vertex d)) (u v : Vertex d → ℝ) :
    gradSum B (fun x => u x - v x) = gradSum B u - gradSum B v := by
  funext j
  simp only [gradSum, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- The increment of `ℓ_ξ` along `e_j` is `ξ_j`. -/
theorem affineFun_add_unitVec (ξ : Fin d → ℝ) (x : Vertex d) (j : Fin d) :
    affineFun ξ (x + unitVec j) - affineFun ξ x = ξ j := by
  simp only [affineFun, ← Finset.sum_sub_distrib, Pi.add_apply, unitVec, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro i _ hij
    simp [hij]
  · simp

/-- A subcube of scale `k` has `(3^k)^{d-1} (3^k - 1)` edges in direction `j`. -/
theorem card_filter_add_unitVec_mem_cube (k : ℕ) (z : Vertex d) (j : Fin d) :
    (((cube k z).filter fun x => x + unitVec j ∈ cube k z).card : ℝ) =
      ((3 : ℝ) ^ k) ^ (d - 1) * ((3 : ℝ) ^ k - 1) := by
  classical
  have hset : (cube k z).filter (fun x => x + unitVec j ∈ cube k z) =
      Fintype.piFinset (Function.update
        (fun i => Finset.Ico (cubeCorner k z i) (cubeCorner k z i + 3 ^ k)) j
        (Finset.Ico (cubeCorner k z j) (cubeCorner k z j + 3 ^ k - 1))) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, mem_cube_iff_corner, Pi.add_apply,
      unitVec_apply]
    constructor
    · rintro ⟨hx, hxj⟩ i
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self, Finset.mem_Ico]
        have h1 := hx i
        have h2 := hxj i
        rw [if_pos rfl] at h2
        constructor <;> omega
      · rw [Function.update_of_ne hij, Finset.mem_Ico]
        exact hx i
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hij : i = j
        · subst hij
          have h1 := h i
          rw [Function.update_self, Finset.mem_Ico] at h1
          constructor <;> omega
        · have h1 := h i
          rw [Function.update_of_ne hij, Finset.mem_Ico] at h1
          exact h1
      · by_cases hij : i = j
        · subst hij
          have h1 := h i
          rw [Function.update_self, Finset.mem_Ico] at h1
          rw [if_pos rfl]
          constructor <;> omega
        · have h1 := h i
          rw [Function.update_of_ne hij, Finset.mem_Ico] at h1
          rw [if_neg hij, add_zero]
          exact h1
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin d)) \ {j},
      (Function.update (fun i => Finset.Ico (cubeCorner k z i) (cubeCorner k z i + 3 ^ k)) j
        (Finset.Ico (cubeCorner k z j) (cubeCorner k z j + 3 ^ k - 1)) i).card = 3 ^ k := by
    intro i hi
    have h : i ≠ j := by simpa using hi
    rw [Function.update_of_ne h, Int.card_Ico, add_sub_cancel_left]
    exact_mod_cast Int.toNat_natCast (3 ^ k)
  have hcard : ((Finset.univ : Finset (Fin d)) \ {j}).card = d - 1 := by
    rw [Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton]
  have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have htn : (cubeCorner k z j + 3 ^ k - 1 - cubeCorner k z j).toNat = 3 ^ k - 1 := by
    have h : cubeCorner k z j + 3 ^ k - 1 - cubeCorner k z j = ((3 ^ k - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [h, Int.toNat_natCast]
  rw [hset, Fintype.card_piFinset,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j), Function.update_self,
    Finset.prod_congr rfl hF, Finset.prod_const, Int.card_Ico, hcard, htn]
  push_cast [Nat.cast_sub h1]
  ring

/-- The normalized spatial average of the gradient of `ℓ_ξ` over a subcube of scale `k` is
`(1 - 3^{-k}) ξ`. -/
theorem gradSum_affineFun (k : ℕ) (z : Vertex d) (ξ : Fin d → ℝ) (j : Fin d) :
    (((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (cube k z) (affineFun ξ) j = (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j := by
  have hd : d - 1 + 1 = d := by
    have := j.pos
    omega
  have hpow : ((3 : ℝ) ^ k) ^ d = ((3 : ℝ) ^ k) ^ (d - 1) * 3 ^ k := by
    rw [← pow_succ, hd]
  simp only [gradSum]
  rw [← Finset.sum_filter, Finset.sum_congr rfl fun x _ => affineFun_add_unitVec ξ x j,
    Finset.sum_const, nsmul_eq_mul, card_filter_add_unitVec_mem_cube, hpow]
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  field_simp

/-- **Multiscale Poincaré inequality relative to an affine function** (Armstrong–Dario 2018,
Proposition 8.2 in the form used in the proof of Lemma 5.8). -/
theorem exists_multiscalePoincare_affine :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, (m : ℝ) / 2 ≤ n → n ≤ m →
      ∀ (z : Vertex d) (u : Vertex d → ℝ) (ξ : Fin d → ℝ),
        ((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z,
            (u x - affineFun ξ x - finsetMean (cube m z) (fun y => u y - affineFun ξ y)) ^ 2 ≤
          C * (3 : ℝ) ^ (2 * n) * (((cube m z).card : ℝ)⁻¹ *
              ∑ x ∈ cube m z, gradNormSq (cube m z) (fun y => u y - affineFun ξ y) x) +
            C * (∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (((centers m z k).card : ℝ)⁻¹ *
              ∑ y ∈ centers m z k, ∑ j : Fin d,
                ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (subcube k y) u j -
                  (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j) ^ 2)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := multiscalePoincare_holds d
  refine ⟨2 * C ^ 2, by positivity, fun m n hmn hnm z u ξ => ?_⟩
  set w : Vertex d → ℝ := fun y => u y - affineFun ξ y with hw
  have hmain := h m n hmn hnm z w
  have hsub : ∀ k ∈ Finset.Ico n m, subcubeGradMeanSq m z k w =
      ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin d,
        ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (subcube k y) u j - (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j) ^ 2 := by
    intro k hk
    have hkm : k ≤ m := (Finset.mem_Ico.1 hk).2.le
    rw [subcubeGradMeanSq]
    congr 1
    rw [sum_centers hkm z (fun B => ∑ j : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum B w j) ^ 2),
      sum_centers hkm z (fun B => ∑ j : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum B u j -
        (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j) ^ 2)]
    refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hw, gradSum_sub, Pi.sub_apply, mul_sub, gradSum_affineFun]
  set Sm := ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (((centers m z k).card : ℝ)⁻¹ *
    ∑ y ∈ centers m z k, ∑ j : Fin d,
      ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (subcube k y) u j - (1 - ((3 : ℝ) ^ k)⁻¹) * ξ j) ^ 2)
    with hSm
  have hsumeq : ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (subcubeGradMeanSq m z k w) = Sm := by
    rw [hSm]
    exact Finset.sum_congr rfl fun k hk => by rw [hsub k hk]
  rw [hsumeq] at hmain
  set G := ((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) w x with hGdef
  set X := Real.sqrt (((cube m z).card : ℝ)⁻¹ *
    ∑ x ∈ cube m z, (w x - finsetMean (cube m z) w) ^ 2) with hXdef
  have hG : 0 ≤ G := mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => by
    simp only [gradNormSq]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity)
  have hX : X ^ 2 = ((cube m z).card : ℝ)⁻¹ *
      ∑ x ∈ cube m z, (w x - finsetMean (cube m z) w) ^ 2 :=
    Real.sq_sqrt (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hsq : X ^ 2 ≤ (C * 3 ^ n * Real.sqrt G + C * Sm) ^ 2 :=
    pow_le_pow_left₀ hX0 hmain 2
  have hGs : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG
  have h2n : (3 : ℝ) ^ (2 * n) = (3 ^ n) ^ 2 := by rw [pow_mul']
  show ((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z, (w x - finsetMean (cube m z) w) ^ 2 ≤
    2 * C ^ 2 * (3 : ℝ) ^ (2 * n) * G + 2 * C ^ 2 * Sm ^ 2
  rw [← hX, h2n]
  calc X ^ 2 ≤ (C * 3 ^ n * Real.sqrt G + C * Sm) ^ 2 := hsq
    _ ≤ 2 * (C * 3 ^ n * Real.sqrt G) ^ 2 + 2 * (C * Sm) ^ 2 := by
        nlinarith [sq_nonneg (C * 3 ^ n * Real.sqrt G - C * Sm)]
    _ = 2 * C ^ 2 * (3 ^ n) ^ 2 * G + 2 * C ^ 2 * Sm ^ 2 := by
        rw [mul_pow, mul_pow, hGs]
        ring

end Rigidity.Proofs.Multiscale
