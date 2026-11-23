import Rigidity.Proofs.Cluster.GeneralIdentification

/-!
# The rate of Proposition 5.2 in expectation from Lemma 5.9, in every dimension

Assume the bound of Lemma 5.9 of Armstrong and Dario in the form
`D_n ≤ C (σ₉ⁿ + ∑_{l ≤ n} ρ^{n-l} τ_l)` from some scale on, with `σ₉, ρ < 1`. Then `τ_n` decays
geometrically (`exists_cubeTau_le_pow_of_decay`), and:

* by display (5.24), the matrices `ā_{□_n}⁻¹` converge geometrically to their limit `L`
  (`exists_abs_cubeAhomInvLimit_sub_le_of_decay`), and `L = ā⁻¹` (`cubeAhomInvLimit_eq_of_decay`,
  from `cubeMuLimit_eq_of_decay`): Step 4 of the proof of Lemma 5.10;
* `|E[-μ(□_n, q)] - (1/2) q · ā⁻¹ q| ≤ K |q|² lⁿ` (`exists_abs_cubeMuMean_sub_le_of_decay`);
* the increments `E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]` are bounded below by the approximate
  monotonicity (4.49) and above through `τ_k` by display (5.9) at the slope `ā⁻¹ (ā ξ)`, so that
  `|E[ν(□_n, ξ)] - (1/2) ξ · ā ξ| ≤ K |ξ|² lⁿ` (`exists_abs_cubeNuMean_sub_le_of_decay`).

These are display (5.4) of Armstrong and Dario (in expectation, for the cubes `□_n`), with Lemma 5.9
as a hypothesis, in every dimension `d ≥ 2`. Armstrong and Dario derive (5.4) from Lemma 5.3 and
the bound (5.5) on `E[ω(□_n, ·)₊]`; the route here uses only the decay of `τ_k`, as in Step 4 of
their proof of Lemma 5.10 for the matrices `ā_{□_n}`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The polarization coefficients of `x ↦ x · A x` are `Aᵢⱼ + Aⱼᵢ`. -/
theorem slopePolar_eq_add_of_eq_dotProduct {g : (Fin d → ℝ) → ℝ} (A : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ x, g x = ∑ i, x i * (A *ᵥ x) i) (i j : Fin d) :
    slopePolar g i j = A i j + A j i := by
  have hq : ∀ u v : Fin d → ℝ, ∑ k, (u + v) k * (A *ᵥ (u + v)) k =
      ∑ k, u k * (A *ᵥ u) k + ∑ k, v k * (A *ᵥ v) k +
        (∑ k, u k * (A *ᵥ v) k + ∑ k, v k * (A *ᵥ u) k) := by
    intro u v
    simp only [Matrix.mulVec_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hs : ∀ a b : Fin d, ∑ k, (Pi.single a 1 : Fin d → ℝ) k * (A *ᵥ Pi.single b 1) k =
      A a b := by
    intro a b
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [slopePolar, h]
  rw [hq, hs, hs, hs, hs]
  ring

theorem inv_smul_one_eq {σ : ℝ} (hσ : σ ≠ 0) :
    (σ • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = σ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ) :=
  Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hσ,
      one_smul])

/-- **The limit of `ā_{□_n}⁻¹` is `ā⁻¹`, from the bound of Lemma 5.9** (every dimension
`d ≥ 2`). -/
theorem cubeAhomInvLimit_eq_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    cubeAhomInvLimit (d := d) p = (cubeAhom (d := d) p)⁻¹ := by
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  have hμ := cubeMuLimit_eq_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have hg : ∀ x : Fin d → ℝ, cubeMuLimit p x =
      ∑ i, x i * (((1 / 2 : ℝ) • (cubeAhom (d := d) p)⁻¹) *ᵥ x) i := fun x => by
    rw [hμ x, Matrix.smul_mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  ext i j
  change slopePolar (cubeMuLimit (d := d) p) i j = _
  rw [slopePolar_eq_add_of_eq_dotProduct _ hg, hA, inv_smul_one_eq hσ.ne']
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
    ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij),
      smul_eq_mul, mul_zero, add_zero]

/-- **Geometric convergence of `ā_{□_n}⁻¹` under the bound of Lemma 5.9** (Armstrong and Dario,
Step 4 of the proof of Lemma 5.10, every dimension `d ≥ 2`), entrywise. -/
theorem exists_abs_cubeAhomInvLimit_sub_le_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ i j : Fin d,
      |cubeAhomInvLimit p i j - cubeAhomInvFinite p n i j| ≤ K * l ^ n := by
  obtain ⟨Kτ, lτ, hlτ0, hlτ1, Nτ, hτ⟩ :=
    exists_cubeTau_le_pow_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨C, hC, hclose⟩ := exists_abs_cubeAhomInvFinite_sub_le hd hpc
  set r := 1 / √(√(3 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := one_div_sqrt_sqrt_three_lt_one
  set σ := max lτ r with hσdef
  have hσ1 : σ < 1 := max_lt hlτ1 hr1
  have hσ0 : 0 < σ := lt_of_lt_of_le hlτ0 (le_max_left _ _)
  have hlσ : lτ ≤ σ := le_max_left _ _
  have hrσ : r ≤ σ := le_max_right _ _
  have h1σ : 0 < 1 - σ := sub_pos.2 hσ1
  set K₀ := max Kτ 0 with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_right _ _
  set B := C * (K₀ / (1 - σ) + 1) with hBdef
  refine ⟨B, σ, by positivity, hσ0, hσ1, Nτ, fun n hn i j => ?_⟩
  have hσn : 0 ≤ σ ^ n := pow_nonneg hσ0.le n
  have hbound : ∀ m, n ≤ m →
      |cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j| ≤ B * σ ^ n := by
    intro m hm
    refine (hclose n m hm i j).trans ?_
    have hT : ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k ≤ K₀ * (σ ^ n / (1 - σ)) := by
      calc ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k
          ≤ ∑ k ∈ Finset.Ico n m, K₀ * σ ^ k := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' : n ≤ k := (Finset.mem_Ico.1 hk).1
            have a := hτ k (le_trans hn hk')
            have hl : 0 ≤ lτ ^ k := pow_nonneg hlτ0.le k
            calc cubeTau (d := d) p k ≤ Kτ * lτ ^ k := a
              _ ≤ K₀ * lτ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hl
              _ ≤ K₀ * σ ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlτ0.le hlσ k) hK₀0
        _ = K₀ * ∑ k ∈ Finset.Ico n m, σ ^ k := by rw [Finset.mul_sum]
        _ ≤ K₀ * (σ ^ n / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hσ0.le hσ1) hK₀0
    have hE : 1 / √(√((3 : ℝ) ^ n)) ≤ σ ^ n := by
      rw [one_div_sqrt_sqrt_three_pow]
      exact pow_le_pow_left₀ hr0 hrσ n
    have e : B * σ ^ n = C * (K₀ * (σ ^ n / (1 - σ)) + σ ^ n) := by
      rw [hBdef]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (add_le_add hT hE) hC
  have hlim : Tendsto (fun m => |cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j|)
      atTop (𝓝 |cubeAhomInvLimit p i j - cubeAhomInvFinite p n i j|) :=
    ((tendsto_cubeAhomInvFinite hd hpc i j).sub tendsto_const_nhds).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, hbound⟩)

/-- **Geometric rate of `E[-μ(□_n, q)]` under the bound of Lemma 5.9** (display (5.4) for `μ`,
in expectation, every dimension `d ≥ 2`): from some scale on,
`|E[-μ(□_n, q)] - (1/2) q · ā⁻¹ q| ≤ K |q|² lⁿ`. -/
theorem exists_abs_cubeMuMean_sub_le_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin d → ℝ,
      |cubeMuMean p n q - 1 / 2 * ∑ i, q i * ((cubeAhom (d := d) p)⁻¹ *ᵥ q) i| ≤
        K * (∑ i, q i ^ 2) * l ^ n := by
  obtain ⟨K, l, hK, hl0, hl1, N, h⟩ :=
    exists_abs_cubeAhomInvLimit_sub_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have hμ := cubeMuLimit_eq_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  refine ⟨d * d * K / 2, l, by positivity, hl0, hl1, N, fun n hn q => ?_⟩
  rw [← hμ q]
  have hg : IsSlopeQuadratic fun x : Fin d → ℝ => cubeMuMean p n x - cubeMuLimit p x :=
    (isSlopeQuadratic_cubeMuMean hd hpc n).sub (isSlopeQuadratic_cubeMuLimit hd hpc)
  have hM : ∀ i j : Fin d,
      slopeMatrix (fun x : Fin d → ℝ => cubeMuMean p n x - cubeMuLimit p x) i j =
        (cubeAhomInvFinite p n i j - cubeAhomInvLimit p i j) / 2 := by
    intro i j
    simp only [slopeMatrix, slopePolar, cubeAhomInvFinite, cubeAhomInvLimit]
    ring
  have habs := hg.abs_le q
  beta_reduce at habs
  simp only [hM] at habs
  have hS : ∑ i : Fin d, ∑ j : Fin d,
      |(cubeAhomInvFinite p n i j - cubeAhomInvLimit (d := d) p i j) / 2| ≤ d * d * K / 2 * l ^ n := by
    have h1 : ∑ i : Fin d, ∑ j : Fin d,
        |(cubeAhomInvFinite p n i j - cubeAhomInvLimit (d := d) p i j) / 2| ≤
        ∑ _i : Fin d, ∑ _j : Fin d, K * l ^ n / 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [abs_div, abs_two, abs_sub_comm]
      exact div_le_div_of_nonneg_right (h n hn i j) (by norm_num)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc |cubeMuMean p n q - cubeMuLimit p q|
      ≤ (∑ i : Fin d, ∑ j : Fin d,
          |(cubeAhomInvFinite p n i j - cubeAhomInvLimit (d := d) p i j) / 2|) * ∑ i, q i ^ 2 :=
        habs
    _ ≤ d * d * K / 2 * l ^ n * ∑ i, q i ^ 2 := mul_le_mul_of_nonneg_right hS hq0
    _ = d * d * K / 2 * (∑ i, q i ^ 2) * l ^ n := by ring

/-- **Tail bound for a convergent sequence with geometric increments**: if `a_k → L` and
`|a_k - a_{k+1}| ≤ B lᵏ` for `k ≥ N`, then `|a_n - L| ≤ B lⁿ / (1 - l)` for `n ≥ N`. -/
theorem abs_sub_lim_le_of_abs_sub_succ_le {a : ℕ → ℝ} {L B l : ℝ} {N : ℕ}
    (ha : Tendsto a atTop (𝓝 L)) (hB : 0 ≤ B) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (h : ∀ k, N ≤ k → |a k - a (k + 1)| ≤ B * l ^ k) {n : ℕ} (hn : N ≤ n) :
    |a n - L| ≤ B * (l ^ n / (1 - l)) := by
  have hm : ∀ m, n ≤ m → |a n - a m| ≤ B * (l ^ n / (1 - l)) := by
    intro m hm
    have e : a n - a m = ∑ k ∈ Finset.Ico n m, (a k - a (k + 1)) := by
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hnm ih =>
        rw [Finset.sum_Ico_succ_top hnm, ← ih]
        ring
    rw [e]
    calc |∑ k ∈ Finset.Ico n m, (a k - a (k + 1))| ≤ ∑ k ∈ Finset.Ico n m, |a k - a (k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico n m, B * l ^ k :=
          Finset.sum_le_sum fun k hk => h k (hn.trans (Finset.mem_Ico.1 hk).1)
      _ = B * ∑ k ∈ Finset.Ico n m, l ^ k := by rw [Finset.mul_sum]
      _ ≤ B * (l ^ n / (1 - l)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hl0 hl1) hB
  have hlim : Tendsto (fun m => |a n - a m|) atTop (𝓝 |a n - L|) :=
    (tendsto_const_nhds.sub ha).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, hm⟩)

/-- **Geometric bound for the increments of `E[ν]` under the bound of Lemma 5.9** (every
dimension `d ≥ 2`): from some scale on, `|E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]| ≤ B |ξ|² σᵏ`. -/
theorem exists_abs_cubeNuIncrement_le_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ B s : ℝ, 0 ≤ B ∧ 0 < s ∧ s < 1 ∧ ∃ N : ℕ, ∀ k, N ≤ k → ∀ ξ : Fin d → ℝ,
      |cubeNuIncrement p k ξ| ≤ B * (∑ i, ξ i ^ 2) * s ^ k := by
  obtain ⟨Kτ, lτ, hlτ0, hlτ1, Nτ, hτ⟩ :=
    exists_cubeTau_le_pow_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨σ, hσ, hA⟩ := exists_cubeAhom_eq_smul_one hd hpc
  obtain ⟨Cu, hCu, hup⟩ := exists_cubeNuIncrement_le hd hpc
  obtain ⟨Cl, hCl, hlow⟩ := exists_neg_le_cubeNuIncrement hd hpc
  set r := 1 / √(3 : ℝ) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have h : 1 < √(3 : ℝ) := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hrdef, div_lt_one (by linarith)]
    exact h
  set s := max lτ r with hsdef
  have hs1 : s < 1 := max_lt hlτ1 hr1
  have hs0 : 0 < s := lt_of_lt_of_le hlτ0 (le_max_left _ _)
  have hls : lτ ≤ s := le_max_left _ _
  have hrs : r ≤ s := le_max_right _ _
  set K₀ := max Kτ 0 with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_right _ _
  set B := d * σ ^ 2 * (K₀ + Cu) + Cl * d with hBdef
  refine ⟨B, s, by positivity, hs0, hs1, Nτ, fun k hk ξ => ?_⟩
  have hsk : 0 ≤ s ^ k := pow_nonneg hs0.le k
  have hrk : 1 / √3 ^ k ≤ s ^ k := by
    rw [← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) hrs k
  have hξ0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the upper bound, at the slope `ā⁻¹ (ā ξ) = ξ`
  have hu := hup k (cubeAhom p *ᵥ ξ)
  have hAξ : (cubeAhom (d := d) p)⁻¹ *ᵥ (cubeAhom p *ᵥ ξ) = ξ := by
    rw [hA, inv_smul_one_eq hσ.ne', Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
  rw [hAξ] at hu
  have hsq : ∑ i, (cubeAhom (d := d) p *ᵥ ξ) i ^ 2 = σ ^ 2 * ∑ i, ξ i ^ 2 := by
    rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  rw [hsq] at hu
  have hτk : cubeNuTau (d := d) p k ≤ K₀ * s ^ k := by
    have a := hτ k hk
    have b : cubeNuTau (d := d) p k ≤ cubeTau (d := d) p k :=
      le_add_of_nonneg_left (cubeMuTau_nonneg p k)
    have hl : 0 ≤ lτ ^ k := pow_nonneg hlτ0.le k
    have c1 : Kτ * lτ ^ k ≤ K₀ * s ^ k :=
      calc Kτ * lτ ^ k ≤ K₀ * lτ ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hl
        _ ≤ K₀ * s ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlτ0.le hls k) hK₀0
    linarith
  have hCk : Cu / √3 ^ k ≤ Cu * s ^ k := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hrk hCu
  have hup' : cubeNuIncrement p k ξ ≤ d * σ ^ 2 * (K₀ + Cu) * (∑ i, ξ i ^ 2) * s ^ k := by
    have h1 : cubeNuTau (d := d) p k + Cu / √3 ^ k ≤ (K₀ + Cu) * s ^ k := by linarith
    have h2 : (0 : ℝ) ≤ d * (σ ^ 2 * ∑ i, ξ i ^ 2) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have e : d * σ ^ 2 * (K₀ + Cu) * (∑ i, ξ i ^ 2) * s ^ k =
        d * (σ ^ 2 * ∑ i, ξ i ^ 2) * ((K₀ + Cu) * s ^ k) := by ring
    rw [e]
    linarith
  -- the lower bound
  have hl := hlow k ξ
  have hlo : -(Cl * d * (∑ i, ξ i ^ 2) * s ^ k) ≤ cubeNuIncrement p k ξ := by
    have h1 := mul_le_mul_of_nonneg_left (sq_sum_abs_le_card_mul ξ) hCl
    have h2 : Cl * (∑ i, |ξ i|) ^ 2 / √3 ^ k ≤ Cl * (d * ∑ i, ξ i ^ 2) * s ^ k := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul h1 hrk (by positivity) (by positivity)
    have e : Cl * (d * ∑ i, ξ i ^ 2) * s ^ k = Cl * d * (∑ i, ξ i ^ 2) * s ^ k := by ring
    linarith
  have hB1 : 0 ≤ d * σ ^ 2 * (K₀ + Cu) * (∑ i, ξ i ^ 2) * s ^ k := by positivity
  have hB2 : 0 ≤ Cl * d * (∑ i, ξ i ^ 2) * s ^ k := by positivity
  have e : B * (∑ i, ξ i ^ 2) * s ^ k = d * σ ^ 2 * (K₀ + Cu) * (∑ i, ξ i ^ 2) * s ^ k +
      Cl * d * (∑ i, ξ i ^ 2) * s ^ k := by
    rw [hBdef]
    ring
  rw [abs_le, e]
  constructor <;> linarith

/-- **Geometric rate of `E[ν(□_n, ξ)]` under the bound of Lemma 5.9** (display (5.4) for `ν`, in
expectation, every dimension `d ≥ 2`): from some scale on,
`|E[ν(□_n, ξ)] - (1/2) ξ · ā ξ| ≤ K |ξ|² lⁿ`. -/
theorem exists_abs_cubeNuMean_sub_le_of_decay [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉)
    (hσ₉ : 0 ≤ σ₉) (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → cubeOmegaD (d := d) p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * cubeTau (d := d) p l) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ ξ : Fin d → ℝ,
      |cubeNuMean p n ξ - 1 / 2 * ∑ i, ξ i * (cubeAhom (d := d) p *ᵥ ξ) i| ≤
        K * (∑ i, ξ i ^ 2) * l ^ n := by
  obtain ⟨B, s, hB, hs0, hs1, N, h⟩ :=
    exists_abs_cubeNuIncrement_le_of_decay hd hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  refine ⟨B / (1 - s), s, div_nonneg hB h1s.le, hs0, hs1, N, fun n hn ξ => ?_⟩
  have hlim := tendsto_cubeNuLimit hd hpc ξ
  have hL : cubeNuLimit p ξ = 1 / 2 * ∑ i, ξ i * (cubeAhom (d := d) p *ᵥ ξ) i := by
    rw [cubeNuLimit_eq_cubeAhom hd hpc]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hL] at hlim
  have hξ0 : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb := abs_sub_lim_le_of_abs_sub_succ_le hlim (mul_nonneg hB hξ0) hs0.le hs1
    (fun k hk => by
      have := h k hk ξ
      unfold cubeNuIncrement at this
      exact this) hn
  refine hb.trans (le_of_eq ?_)
  field_simp

end Rigidity.Percolation
