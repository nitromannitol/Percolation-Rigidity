import Rigidity.Proofs.Cluster.GeneralOmegaDecayIteration

/-!
# The identification of the limit of `E[-μ]` from the decay of `ω`, in every dimension

Let `L` be the limit of the finite-volume matrices `ā_{□_n}⁻¹`, so that
`lim E[-μ(□_n, q)] = (1/2) q · L q` (`half_sum_mul_cubeAhomInvLimit_eq`). It is invertible
(display (5.1) for the limit) and the matrices `ā_{□_n}` converge to `L⁻¹`
(`tendsto_cubeAhomFinite`). From the scale on which `ā_{□_n}⁻¹ ā_{□_n} = 1`,
`D_n = ∑ᵢ (E[ν(□_n, eᵢ)] - (1/2) eᵢ · ā_{□_n} eᵢ)`, so that `D_n` converges to
`∑ᵢ (lim E[ν(□_n, eᵢ)] - (1/2) (L⁻¹)ᵢᵢ)` (`tendsto_cubeOmegaD`).

With the homogenized matrix `ā = σ I` (isotropy), the duality inequality gives `L ≥ σ⁻¹ I` and
hence `q · L⁻¹ q ≤ σ |q|²`. If `lim D_n ≤ 0`, the nonnegative quadratic form
`q ↦ σ |q|² - q · L⁻¹ q` has nonpositive values at the unit vectors and vanishes; testing it at
`L z` gives `z · L z = σ⁻¹ |z|²`. Under the bound of Lemma 5.9 of Armstrong and Dario, `D_n` decays
geometrically, and therefore `lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`
(`cubeMuLimit_eq_of_decay`): the qualitative content of Proposition 5.2, with Lemma 5.9 as a
hypothesis, in every dimension `d ≥ 2`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

theorem mulVec_single_one_apply (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (A *ᵥ Pi.single j 1) i = A i j := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- `(1/2) q · L q = lim E[-μ(□_n, q)]`. -/
theorem half_sum_mul_cubeAhomInvLimit_eq [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (q : Fin d → ℝ) :
    1 / 2 * ∑ i, q i * (cubeAhomInvLimit p *ᵥ q) i = cubeMuLimit p q := by
  rw [isSlopeQuadratic_cubeMuLimit hd hpc q]
  simp only [Matrix.mulVec, dotProduct, cubeAhomInvLimit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The limit matrix `L` is invertible.** -/
theorem isUnit_det_cubeAhomInvLimit [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : IsUnit (cubeAhomInvLimit (d := d) p).det := by
  obtain ⟨c, C, hc, -, hb⟩ := exists_cubeMuLimit_two_sided hd hpc
  refine isUnit_det_of_le_sum_mul (c := 2 * c) (by positivity) fun q => ?_
  have h1 := (hb q).1
  rw [← half_sum_mul_cubeAhomInvLimit_eq hd hpc q] at h1
  linarith

/-- **The matrices `ā_{□_n}` converge to `L⁻¹`.** -/
theorem tendsto_cubeAhomFinite [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    Tendsto (fun n => cubeAhomFinite (d := d) p n) atTop (𝓝 (cubeAhomInvLimit (d := d) p)⁻¹) := by
  have hB : Tendsto (fun n => cubeAhomInvFinite (d := d) p n) atTop
      (𝓝 (cubeAhomInvLimit (d := d) p)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_cubeAhomInvFinite hd hpc i j
  have hc : ContinuousAt Ring.inverse (cubeAhomInvLimit (d := d) p).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_det_cubeAhomInvLimit hd hpc).ne_zero
  exact (continuousAt_matrix_inv _ hc).tendsto.comp hB

/-- `E[-μ(□_n, ā_{□_n} r)] = (1/2) r · ā_{□_n} r` once `ā_{□_n}⁻¹ ā_{□_n} = 1`. -/
theorem cubeMuMean_cubeAhomFinite [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {n : ℕ}
    (hinv : cubeAhomInvFinite p n * cubeAhomFinite (d := d) p n = 1) (r : Fin d → ℝ) :
    cubeMuMean p n (cubeAhomFinite p n *ᵥ r) = 1 / 2 * ∑ i, r i * (cubeAhomFinite p n *ᵥ r) i := by
  rw [← half_sum_mul_cubeAhomInvFinite_eq hd hpc n, Matrix.mulVec_mulVec, hinv,
    Matrix.one_mulVec]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The limit of `D_n`**: `D_n → ∑ᵢ (lim E[ν(□_n, eᵢ)] - (1/2) (L⁻¹)ᵢᵢ)`. -/
theorem tendsto_cubeOmegaD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    Tendsto (cubeOmegaD (d := d) p) atTop (𝓝 (∑ i : Fin d,
      (cubeNuLimit p (Pi.single i 1) - 1 / 2 * (cubeAhomInvLimit (d := d) p)⁻¹ i i))) := by
  obtain ⟨N, hN⟩ := exists_cubeAhomInvFinite_mul_cubeAhomFinite hd hpc
  have heq : ∀ n, N ≤ n → cubeOmegaD (d := d) p n = ∑ i : Fin d,
      (cubeNuMean p n (Pi.single i 1) - 1 / 2 * cubeAhomFinite (d := d) p n i i) := by
    intro n hn
    obtain ⟨hinv, -⟩ := hN n hn
    unfold cubeOmegaD
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cubeMuMean_cubeAhomFinite hd hpc hinv, sum_single_mul_eq, mulVec_single_one_apply]
    ring
  have hA := tendsto_cubeAhomFinite hd hpc
  have hlim : Tendsto (fun n => ∑ i : Fin d,
      (cubeNuMean p n (Pi.single i 1) - 1 / 2 * cubeAhomFinite (d := d) p n i i)) atTop
      (𝓝 (∑ i : Fin d,
        (cubeNuLimit p (Pi.single i 1) - 1 / 2 * (cubeAhomInvLimit (d := d) p)⁻¹ i i))) :=
    tendsto_finsetSum _ fun i _ => (tendsto_cubeNuLimit hd hpc _).sub
      ((tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hA i) i).const_mul _)
  exact hlim.congr' (eventually_atTop.2 ⟨N, fun n hn => (heq n hn).symm⟩)

/-- **`L⁻¹ ≤ σ I`** when `ā = σ I`: by duality `L ≥ σ⁻¹ I`, and testing with `x = L⁻¹ q`,
`q · L⁻¹ q ≤ σ |q|²`. -/
theorem sum_mul_inv_cubeAhomInvLimit_mulVec_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {σ : ℝ} (hσ : 0 < σ)
    (hA : cubeAhom (d := d) p = σ • (1 : Matrix (Fin d) (Fin d) ℝ)) (q : Fin d → ℝ) :
    ∑ i, q i * ((cubeAhomInvLimit (d := d) p)⁻¹ *ᵥ q) i ≤ σ * ∑ i, q i ^ 2 := by
  set L := cubeAhomInvLimit (d := d) p with hL
  have hdet := isUnit_det_cubeAhomInvLimit hd hpc
  set x := L⁻¹ *ᵥ q with hx
  have hLx : L *ᵥ x = q := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h1 := cubeMuLimit_ge_of_cubeAhom_eq_smul_one hd hpc hσ hA x
  rw [← half_sum_mul_cubeAhomInvLimit_eq hd hpc x, ← hL, hLx, div_le_iff₀ (by positivity)] at h1
  have h2 : 0 ≤ ∑ i, (x i - σ * q i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e2 : ∑ i, (x i - σ * q i) ^ 2 =
      ∑ i, x i ^ 2 - 2 * σ * ∑ i, x i * q i + σ ^ 2 * ∑ i, q i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, q i * x i = ∑ i, x i * q i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e3]
  have h3 : σ * ∑ i, x i * q i ≤ σ * (σ * ∑ i, q i ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left h3 hσ

/-- **The identification of the limit of `E[-μ]` from the limit of `D_n`** (every dimension
`d ≥ 2`): if `ā = σ I` and `∑ᵢ (σ - (L⁻¹)ᵢᵢ) ≤ 0`, then `lim E[-μ(□_n, q)] = |q|² / (2σ)`. -/
theorem cubeMuLimit_eq_of_sum_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {σ : ℝ} (hσ : 0 < σ)
    (hA : cubeAhom (d := d) p = σ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hD : ∑ i : Fin d, (σ - (cubeAhomInvLimit (d := d) p)⁻¹ i i) ≤ 0) (z : Fin d → ℝ) :
    cubeMuLimit p z = (∑ i, z i ^ 2) / (2 * σ) := by
  set L := cubeAhomInvLimit (d := d) p with hL
  have hdet := isUnit_det_cubeAhomInvLimit hd hpc
  set f : (Fin d → ℝ) → ℝ := fun q => σ * ∑ i, q i ^ 2 - ∑ i, q i * (L⁻¹ *ᵥ q) i with hf
  have hfq : IsSlopeQuadratic f :=
    (isSlopeQuadratic_sum_sq.const_mul σ).sub (isSlopeQuadratic_dotProduct_mulVec L⁻¹)
  have hf0 : ∀ q, 0 ≤ f q := fun q => by
    have := sum_mul_inv_cubeAhomInvLimit_mulVec_le hd hpc hσ hA q
    simp only [hf]
    linarith
  have hs : ∀ b : Fin d, ∑ k, (Pi.single b 1 : Fin d → ℝ) k ^ 2 = 1 := fun b => by
    rw [Finset.sum_eq_single b (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have hfe : ∀ i : Fin d, f (Pi.single i 1) = σ - L⁻¹ i i := fun i => by
    simp only [hf, hs, mul_one]
    rw [sum_single_mul_eq, mulVec_single_one_apply]
  have hsum : ∑ i, f (Pi.single i 1) ≤ 0 := by
    simp only [hfe]
    exact hD
  have hzero : ∀ q, f q = 0 := fun q => by
    have h1 := hfq.le_of_nonneg hf0 q
    have h2 : (d : ℝ) * (∑ i, q i ^ 2) * ∑ i, f (Pi.single i 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hsum
    linarith [hf0 q]
  set w := L *ᵥ z with hw
  have hLw : L⁻¹ *ᵥ w = z := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hfw := hzero w
  simp only [hf, hLw] at hfw
  have h2 : 0 ≤ ∑ i, (z i - σ * w i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e2 : ∑ i, (z i - σ * w i) ^ 2 =
      ∑ i, z i ^ 2 - 2 * σ * ∑ i, w i * z i + σ * (σ * ∑ i, w i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : σ * ∑ i, w i * z i ≤ ∑ i, z i ^ 2 := by nlinarith
  have h4 := cubeMuLimit_ge_of_cubeAhom_eq_smul_one hd hpc hσ hA z
  have h5 := half_sum_mul_cubeAhomInvLimit_eq hd hpc z
  rw [← hL, ← hw] at h5
  have e5 : ∑ i, z i * w i = ∑ i, w i * z i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e5] at h5
  rw [div_le_iff₀ (by positivity)] at h4
  rw [eq_div_iff (by positivity)]
  nlinarith

theorem inv_smul_one_mulVec {σ : ℝ} (hσ : σ ≠ 0) (q : Fin d → ℝ) :
    (σ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ q = σ⁻¹ • q := by
  have h : (σ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) * (σ • (1 : Matrix (Fin d) (Fin d) ℝ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hσ,
      one_smul]
  rw [Matrix.inv_eq_left_inv h, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part, from Lemma 5.9** (every dimension
`d ≥ 2`). If `D_n ≤ C (σ₉ⁿ + ∑_{l ≤ n} ρ^{n-l} τ_l)` from some scale on, with `σ₉, ρ < 1`, then
`lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q` for every `q`. -/
theorem cubeMuLimit_eq_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l)
    (q : Fin d → ℝ) :
    cubeMuLimit p q = 1 / 2 * ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i := by
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  obtain ⟨K, l, hl0, hl1, N, hK⟩ :=
    exists_cubeOmegaD_le_pow_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have hlim := tendsto_cubeOmegaD hd hpc
  have hpow : Tendsto (fun n => K * l ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hl0.le hl1).const_mul K
  have hD := le_of_tendsto_of_tendsto hlim hpow (eventually_atTop.2 ⟨N, hK⟩)
  have hν : ∀ i : Fin d, cubeNuLimit p (Pi.single i 1) = σ / 2 := fun i => by
    rw [cubeNuLimit_eq_cubeAhom hd hpc, hA]
    rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp)]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    ring
  simp only [hν] at hD
  have hD' : ∑ i : Fin d, (σ - (cubeAhomInvLimit (d := d) p)⁻¹ i i) ≤ 0 := by
    have e : ∑ i : Fin d, (σ / 2 - 1 / 2 * (cubeAhomInvLimit (d := d) p)⁻¹ i i) =
        1 / 2 * ∑ i : Fin d, (σ - (cubeAhomInvLimit (d := d) p)⁻¹ i i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e] at hD
    linarith
  rw [cubeMuLimit_eq_of_sum_le hd hpc hσ hA hD' q, hA, inv_smul_one_mulVec hσ.ne']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by field_simp

end Rigidity.Percolation
