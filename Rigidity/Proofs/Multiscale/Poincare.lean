import Rigidity.Proofs.Multiscale.Scales

/-!
# The discrete multiscale Poincaré inequality

Proof of `MultiscalePoincare d`, Armstrong–Dario 2018, Proposition A.2.

Departure from the source: Armstrong and Dario derive the discrete inequality from the continuum
inequality (their Proposition A.1, from Armstrong–Kuusi–Mourrat) by smoothing. Here it follows from
the lattice multiscale Poincaré inequality on the closed cubes `P + {0, …, 3^m}^d` with
face-weighted block means (`LatticeHC.exists_sum_sq_sub_vertexMean_le_multiscale`), applied to
the extension of `u` by the clamp. The block terms of the scales below `n` and of the top scale
are at most the energy, those of the scales `n ≤ k < m` are at most the spatial averages over the
subcubes plus a boundary-layer error `C 3^{k/2} ‖∇u‖`, and these errors sum to at most
`C 3^{m/2} ‖∇u‖ ≤ C 3^n ‖∇u‖` because `n ≥ m/2`.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb LatticeProb.Percolation LatticeHC

variable {d : ℕ}

/-- `Σ_{k<m} √3^k ≤ 2 √3^m`. -/
theorem sum_range_sqrt_three_pow_le (m : ℕ) :
    ∑ k ∈ Finset.range m, Real.sqrt 3 ^ k ≤ 2 * Real.sqrt 3 ^ m := by
  have hr : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    calc (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have h := geom_sum_mul (Real.sqrt 3) m
  have hS : 0 ≤ ∑ k ∈ Finset.range m, Real.sqrt 3 ^ k :=
    Finset.sum_nonneg fun k _ => pow_nonneg (Real.sqrt_nonneg _) _
  nlinarith [pow_nonneg (Real.sqrt_nonneg 3) m]

/-- `Σ_{k<n} 3^k ≤ 3^n`. -/
theorem sum_range_three_pow_le (n : ℕ) : ∑ k ∈ Finset.range n, (3 : ℝ) ^ k ≤ 3 ^ n := by
  have h := geom_sum_mul (3 : ℝ) n
  have hS : 0 ≤ ∑ k ∈ Finset.range n, (3 : ℝ) ^ k :=
    Finset.sum_nonneg fun k _ => pow_nonneg (by norm_num) _
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) n]

/-- The squares of the powers of `√3` are the powers of `3`. -/
theorem sqrt_three_pow_sq (k : ℕ) : (Real.sqrt 3 ^ k) ^ 2 = 3 ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The mean square of the spatial averages is nonnegative. -/
theorem subcubeGradMeanSq_nonneg (m : ℕ) (z : Vertex d) (k : ℕ) (u : Vertex d → ℝ) :
    0 ≤ subcubeGradMeanSq m z k u :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The face-weighted mean of a nonnegative function is nonnegative. -/
theorem cubeAvg_nonneg (c : Site d) (L : ℕ) {f : Edge d → ℝ} (hf : ∀ e, 0 ≤ f e) :
    0 ≤ cubeAvg c L f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ =>
    mul_nonneg (pow_nonneg (by norm_num) _) (hf e))

/-- **The block terms of the extension, square-root form**: for `k ≤ m`,
`blockSq_k(∇ũ)^{1/2} ≤ √2 (subcubeGradMeanSq m z k u)^{1/2} + (2 · 12 d 4^d)^{1/2} √3^{-k}
cubeAvg(|∇ũ|²)^{1/2}`. -/
theorem sqrt_blockSq_clampSite_le {k m : ℕ} (hk : k ≤ m) (z : Vertex d) (u : Vertex d → ℝ) :
    Real.sqrt (blockSq (cubeCorner m z) m k (fun e =>
        u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src))) ≤
      Real.sqrt 2 * Real.sqrt (subcubeGradMeanSq m z k u) +
        Real.sqrt (2 * (12 * d * 4 ^ d)) * (Real.sqrt 3 ^ k)⁻¹ *
          Real.sqrt (cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
            (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
              u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2)) := by
  set ca := cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
    (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
      u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2) with hca
  set S := subcubeGradMeanSq m z k u
  have hca0 : 0 ≤ ca := cubeAvg_nonneg _ _ fun e => sq_nonneg _
  have hS0 : 0 ≤ S := subcubeGradMeanSq_nonneg m z k u
  have h : blockSq (cubeCorner m z) m k (fun e =>
        u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ≤
      2 * S + 2 * (12 * d * 4 ^ d) * ((3 : ℝ) ^ k)⁻¹ * ca :=
    blockSq_le_of_eqOn hk z u (fun x => u (clampSite (cubeCorner m z) (3 ^ m) x))
      (fun x hx => congrArg u (clampSite_of_mem hx))
  set A := Real.sqrt 2 * Real.sqrt S with hA
  set B := Real.sqrt (2 * (12 * d * 4 ^ d)) * (Real.sqrt 3 ^ k)⁻¹ * Real.sqrt ca with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hA2 : A ^ 2 = 2 * S := by
    rw [hA, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt hS0]
  have hB2 : B ^ 2 = 2 * (12 * d * 4 ^ d) * ((3 : ℝ) ^ k)⁻¹ * ca := by
    rw [hB, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (12 * d * 4 ^ d) by positivity),
      Real.sq_sqrt hca0, inv_pow, sqrt_three_pow_sq]
  have hle : blockSq (cubeCorner m z) m k (fun e =>
      u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
        u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ≤ (A + B) ^ 2 := by
    nlinarith [mul_nonneg hA0 hB0]
  exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (add_nonneg hA0 hB0))

/-- **The sum over the scales**: the bookkeeping behind Proposition A.2. If the block terms
`bs k ≤ ca` at every scale, the top one is at most the one below, and at every scale
`√(bs k) ≤ √2 √(S k) + b √3^{-k} √ca`, then for `m/2 ≤ n ≤ m`,
`Σ_{k ≤ m} 3^k √(bs k) + √ca ≤ (3 + 8b) a 3^n Γ + 4√2 Σ_{k=n}^{m-1} 3^k √(S k)` when `√ca ≤ a Γ`. -/
theorem sum_scales_le {m n : ℕ} (hm2 : m ≤ 2 * n) (hnm : n ≤ m) (a b ca Γ : ℝ) (bs S : ℕ → ℝ)
    (hb0 : 0 ≤ b) (hle : ∀ k ≤ m, bs k ≤ ca) (hpred : 1 ≤ m → bs m ≤ bs (m - 1))
    (hscale : ∀ k ≤ m, Real.sqrt (bs k) ≤
      Real.sqrt 2 * Real.sqrt (S k) + b * (Real.sqrt 3 ^ k)⁻¹ * Real.sqrt ca)
    (hcaΓ : Real.sqrt ca ≤ a * Γ) :
    ∑ k ∈ Finset.range (m + 1), (3 : ℝ) ^ k * Real.sqrt (bs k) + Real.sqrt ca ≤
      (3 + 8 * b) * a * 3 ^ n * Γ +
        4 * Real.sqrt 2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (S k) := by
  have hn3 : (0 : ℝ) ≤ 3 ^ n := by positivity
  have hT0 : 0 ≤ ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) :=
    Finset.sum_nonneg fun k _ => by positivity
  -- the scales n ≤ k < m
  have hTle : ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) ≤
      Real.sqrt 2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (S k) +
        2 * b * 3 ^ n * Real.sqrt ca := by
    have hterm : ∀ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) ≤
        Real.sqrt 2 * ((3 : ℝ) ^ k * Real.sqrt (S k)) +
          b * Real.sqrt ca * Real.sqrt 3 ^ k := by
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Ico.1 hk).2.le
      have h := hscale k hkm
      have h3 : (3 : ℝ) ^ k * (Real.sqrt 3 ^ k)⁻¹ = Real.sqrt 3 ^ k := by
        have hpos : (0 : ℝ) < Real.sqrt 3 ^ k := by positivity
        rw [← sqrt_three_pow_sq k]
        field_simp
      calc (3 : ℝ) ^ k * Real.sqrt (bs k)
          ≤ (3 : ℝ) ^ k * (Real.sqrt 2 * Real.sqrt (S k) +
              b * (Real.sqrt 3 ^ k)⁻¹ * Real.sqrt ca) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = Real.sqrt 2 * ((3 : ℝ) ^ k * Real.sqrt (S k)) +
              b * Real.sqrt ca * ((3 : ℝ) ^ k * (Real.sqrt 3 ^ k)⁻¹) := by ring
        _ = _ := by rw [h3]
    have hgeom : ∑ k ∈ Finset.Ico n m, Real.sqrt 3 ^ k ≤ 2 * 3 ^ n := by
      have hsub : ∑ k ∈ Finset.Ico n m, Real.sqrt 3 ^ k ≤
          ∑ k ∈ Finset.range m, Real.sqrt 3 ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => Finset.mem_range.2
          (Finset.mem_Ico.1 hk).2) fun k _ _ => pow_nonneg (Real.sqrt_nonneg _) _
      have hpow : Real.sqrt 3 ^ m ≤ 3 ^ n := by
        have hsq : (Real.sqrt 3 ^ m) ^ 2 ≤ ((3 : ℝ) ^ n) ^ 2 := by
          rw [sqrt_three_pow_sq, ← pow_mul]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have h0 : 0 ≤ Real.sqrt 3 ^ m := pow_nonneg (Real.sqrt_nonneg _) _
        nlinarith
      linarith [sum_range_sqrt_three_pow_le m]
    have hca0 : 0 ≤ b * Real.sqrt ca := mul_nonneg hb0 (Real.sqrt_nonneg _)
    calc ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k)
        ≤ ∑ k ∈ Finset.Ico n m, (Real.sqrt 2 * ((3 : ℝ) ^ k * Real.sqrt (S k)) +
          b * Real.sqrt ca * Real.sqrt 3 ^ k) := Finset.sum_le_sum hterm
      _ = Real.sqrt 2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (S k) +
          b * Real.sqrt ca * ∑ k ∈ Finset.Ico n m, Real.sqrt 3 ^ k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ Real.sqrt 2 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (S k) +
          b * Real.sqrt ca * (2 * 3 ^ n) := by
        have := mul_le_mul_of_nonneg_left hgeom hca0
        linarith
      _ = _ := by ring
  -- the scales k < n
  have hlow : ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt (bs k) ≤
      3 ^ n * Real.sqrt ca := by
    calc ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt (bs k)
        ≤ ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt ca :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (hle k ((Finset.mem_range.1 hk).le.trans hnm))) (by positivity)
      _ = (∑ k ∈ Finset.range n, (3 : ℝ) ^ k) * Real.sqrt ca := by rw [Finset.sum_mul]
      _ ≤ 3 ^ n * Real.sqrt ca :=
          mul_le_mul_of_nonneg_right (sum_range_three_pow_le n) (Real.sqrt_nonneg _)
  -- the top scale
  have htop : (3 : ℝ) ^ m * Real.sqrt (bs m) ≤ 3 ^ n * Real.sqrt ca +
      3 * ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) := by
    rcases eq_or_lt_of_le hnm with heq | hlt
    · have h2 : (3 : ℝ) ^ m * Real.sqrt (bs m) ≤ 3 ^ m * Real.sqrt ca :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle m le_rfl)) (by positivity)
      rw [show (3 : ℝ) ^ n = 3 ^ m by rw [heq]]
      linarith
    · have hm1 : 1 ≤ m := by omega
      have hmem : m - 1 ∈ Finset.Ico n m := Finset.mem_Ico.2 ⟨by omega, by omega⟩
      have hsingle : (3 : ℝ) ^ (m - 1) * Real.sqrt (bs (m - 1)) ≤
          ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) :=
        Finset.single_le_sum (f := fun k => (3 : ℝ) ^ k * Real.sqrt (bs k))
          (fun k _ => by positivity) hmem
      have hmono : Real.sqrt (bs m) ≤ Real.sqrt (bs (m - 1)) := Real.sqrt_le_sqrt (hpred hm1)
      have h3 : (3 : ℝ) ^ m = 3 * 3 ^ (m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hca' : 0 ≤ (3 : ℝ) ^ n * Real.sqrt ca := by positivity
      calc (3 : ℝ) ^ m * Real.sqrt (bs m) ≤ 3 ^ m * Real.sqrt (bs (m - 1)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = 3 * (3 ^ (m - 1) * Real.sqrt (bs (m - 1))) := by rw [h3]; ring
        _ ≤ _ := by linarith
  have hsplit : ∑ k ∈ Finset.range (m + 1), (3 : ℝ) ^ k * Real.sqrt (bs k) =
      ∑ k ∈ Finset.range n, (3 : ℝ) ^ k * Real.sqrt (bs k) +
        ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (bs k) +
          (3 : ℝ) ^ m * Real.sqrt (bs m) := by
    rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ hnm]
  have hca1 : Real.sqrt ca ≤ 3 ^ n * Real.sqrt ca :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) (one_le_pow₀ (by norm_num))
  have hcaΓ' : 3 ^ n * Real.sqrt ca ≤ 3 ^ n * (a * Γ) := mul_le_mul_of_nonneg_left hcaΓ hn3
  have hbca' : b * (3 ^ n * Real.sqrt ca) ≤ b * (3 ^ n * (a * Γ)) :=
    mul_le_mul_of_nonneg_left hcaΓ' hb0
  rw [hsplit]
  nlinarith

/-- **Armstrong–Dario 2018, Proposition A.2** (discrete multiscale Poincaré inequality). -/
theorem multiscalePoincare_holds (d : ℕ) : MultiscalePoincare d := by
  obtain ⟨CL, hCL, hL⟩ := exists_sum_sq_sub_vertexMean_le_multiscale (d := d)
  have hb0 : 0 ≤ Real.sqrt (2 * (12 * d * 4 ^ d)) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ Real.sqrt (2 ^ d) := Real.sqrt_nonneg _
  refine ⟨Real.sqrt CL * ((3 + 8 * Real.sqrt (2 * (12 * d * 4 ^ d))) * Real.sqrt (2 ^ d) +
    4 * Real.sqrt 2), by positivity, ?_⟩
  intro m n hmn hnm z u
  have hm2 : m ≤ 2 * n := by
    have h : (m : ℝ) ≤ 2 * n := by linarith
    exact_mod_cast h
  have hcard : ((cube m z).card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
    rw [card_cube]
    push_cast
    ring
  -- the energy term
  have hcaΓ : Real.sqrt (cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
        (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2)) ≤
      Real.sqrt (2 ^ d) * Real.sqrt (((cube m z).card : ℝ)⁻¹ *
        ∑ x ∈ cube m z, gradNormSq (cube m z) u x) := by
    rw [hcard, sum_gradNormSq, ← Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ d by positivity)]
    exact Real.sqrt_le_sqrt (cubeAvg_sq_clampSite_le m z u)
  -- the scales
  have hkey := sum_scales_le hm2 hnm (Real.sqrt (2 ^ d)) (Real.sqrt (2 * (12 * d * 4 ^ d)))
    (cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
      (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
        u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2))
    (Real.sqrt (((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) u x))
    (fun k => blockSq (cubeCorner m z) m k (fun e =>
      u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
        u (clampSite (cubeCorner m z) (3 ^ m) e.src)))
    (fun k => subcubeGradMeanSq m z k u) hb0
    (fun k hk => blockSq_le_cubeAvg hk _ _) (fun hm1 => blockSq_self_le_pred hm1 _ _)
    (fun k hk => sqrt_blockSq_clampSite_le hk z u) hcaΓ
  -- the lattice inequality
  have h1 := hL (cubeCorner m z) m (fun x => u (clampSite (cubeCorner m z) (3 ^ m) x))
  have h2 := sum_sq_sub_finsetMean_le_clampSite m z u
  set R : ℝ := ∑ k ∈ Finset.range (m + 1), (3 : ℝ) ^ k *
      Real.sqrt (blockSq (cubeCorner m z) m k (fun e =>
        u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
          u (clampSite (cubeCorner m z) (3 ^ m) e.src))) +
    Real.sqrt (cubeAvg (cubeCorner m z) (3 ^ m) (fun e =>
      (u (clampSite (cubeCorner m z) (3 ^ m) e.tgt) -
        u (clampSite (cubeCorner m z) (3 ^ m) e.src)) ^ 2)) with hR
  have hR0 : 0 ≤ R := add_nonneg (Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hLHS2 : ((cube m z).card : ℝ)⁻¹ *
      ∑ x ∈ cube m z, (u x - finsetMean (cube m z) u) ^ 2 ≤ CL * R ^ 2 := by
    rw [hcard]
    exact le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have hLHS : Real.sqrt (((cube m z).card : ℝ)⁻¹ *
      ∑ x ∈ cube m z, (u x - finsetMean (cube m z) u) ^ 2) ≤ Real.sqrt CL * R :=
    (Real.sqrt_le_sqrt hLHS2).trans_eq (by rw [Real.sqrt_mul hCL, Real.sqrt_sq hR0])
  set Γ := Real.sqrt (((cube m z).card : ℝ)⁻¹ * ∑ x ∈ cube m z, gradNormSq (cube m z) u x)
  set Q := ∑ k ∈ Finset.Ico n m, (3 : ℝ) ^ k * Real.sqrt (subcubeGradMeanSq m z k u)
  set a := Real.sqrt (2 ^ d)
  set b := Real.sqrt (2 * (12 * d * 4 ^ d))
  have hΓ0 : 0 ≤ Γ := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun k _ =>
    mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hs : 0 ≤ Real.sqrt CL := Real.sqrt_nonneg _
  have hRle : R ≤ (3 + 8 * b) * a * 3 ^ n * Γ + 4 * Real.sqrt 2 * Q := hkey
  have hX : Real.sqrt CL * R ≤ Real.sqrt CL * ((3 + 8 * b) * a * 3 ^ n * Γ + 4 * Real.sqrt 2 * Q) :=
    mul_le_mul_of_nonneg_left hRle hs
  have hp1 : 0 ≤ Real.sqrt CL * (4 * Real.sqrt 2) * 3 ^ n * Γ := by positivity
  have hp2 : 0 ≤ Real.sqrt CL * ((3 + 8 * b) * a) * Q := by positivity
  nlinarith

end Rigidity.Proofs.Multiscale
