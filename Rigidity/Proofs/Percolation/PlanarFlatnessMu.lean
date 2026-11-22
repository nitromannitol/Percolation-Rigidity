import Rigidity.Proofs.Percolation.PlanarFlatnessTools

/-!
# Flatness of the coarsened minimizers of `μ` (Lemma 5.8 of Armstrong and Dario, first part)

Let `u = u(·, □_{n+1}, q)` be the minimizer of `μ(□_{n+1}, q)` and `[u]_P` its coarsening. From
Lemma 5.7 (weak convergence), Lemma 5.5 (almost additivity of the spatial averages of the
coarsened gradients) and the bound on the energy of `[u]_P`, the multiscale Poincaré inequality
(Proposition A.2) with `n₀ = ⌈(9/10)(n + 1)⌉` gives

`E[|□_{n+1}|⁻¹ ∑_{x ∈ □_{n+1}} |[u]_P(x) - x · ā_{□_n}⁻¹ q - c|²]
  ≤ C |q|² 3^{2n} (3^{-n/10} + 3^{-n} ∑_{k=0}^{n} 3^k τ_k)`,

`c` the mean of `[u]_P - x · ā_{□_n}⁻¹ q` over `□_{n+1}`. This is display (5.32) of Lemma 5.8 of
Armstrong and Dario in dimension two (`1/(4d+2) = 1/10`; with their normalization of the
additive constant, `c = 0`). The mean-zero normalization of Armstrong and Dario is replaced by the
subtraction of the mean. The spatial average of the gradient of `x ↦ x · ξ` over a subcube of
scale `k` is `(1 - 3^{-k}) ξ`; the difference with `ξ` is absorbed in the error `3^{-k/4}`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (cube centers subcube gradSum gradNormSq finsetMean affineFun)

/-- The mean square deviation `|U|⁻¹ ∑_{x ∈ U} |w(x) - x · ξ - c|²` of a function from the
affine function of slope `ξ`, `c` the mean of `w - ℓ_ξ` over `U`. -/
noncomputable def planarFlatnessError (U : TriadicCube 2) (w : Vertex 2 → ℝ) (ξ : Fin 2 → ℝ) :
    ℝ :=
  U.volume⁻¹ * ∑ x ∈ U.toIntegerCube.vertices,
    (w x - affineFun ξ x - finsetMean U.toIntegerCube.vertices (fun y => w y - affineFun ξ y)) ^ 2

theorem planarFlatnessError_nonneg (U : TriadicCube 2) (w : Vertex 2 → ℝ) (ξ : Fin 2 → ℝ) :
    0 ≤ planarFlatnessError U w ξ :=
  mul_nonneg (inv_nonneg.2 U.volume_pos.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem coarseEnergy_nonneg {ω : Configuration 2} (U : TriadicCube 2) (w : ClusterFun ω U) :
    0 ≤ coarseEnergy ω U w := by
  refine mul_nonneg (inv_nonneg.2 U.volume_pos.le) (Finset.sum_nonneg fun x _ => ?_)
  simp only [gradNormSq]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

theorem planarMuRestrictError_nonneg (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (q : Fin 2 → ℝ) : 0 ≤ planarMuRestrictError ω U n q :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- `|ā_{□_n}⁻¹ q|² ≤ 4 K² |q|²` for a bound `K` of the entries. -/
theorem sum_sq_mulVec_le {M : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ} (hM : ∀ i j, |M i j| ≤ K)
    (q : Fin 2 → ℝ) :
    (M *ᵥ q) 0 ^ 2 + (M *ᵥ q) 1 ^ 2 ≤ 4 * K ^ 2 * (q 0 ^ 2 + q 1 ^ 2) := by
  have hrow : ∀ j, (M *ᵥ q) j ^ 2 ≤ 2 * K ^ 2 * (q 0 ^ 2 + q 1 ^ 2) := by
    intro j
    have e : (M *ᵥ q) j = M j 0 * q 0 + M j 1 * q 1 := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e]
    have h0 : M j 0 ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM j 0) 2
    have h1 : M j 1 ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM j 1) 2
    nlinarith [sq_nonneg (M j 0 * q 0 - M j 1 * q 1), sq_nonneg (q 0), sq_nonneg (q 1),
      mul_le_mul_of_nonneg_right h0 (sq_nonneg (q 0)),
      mul_le_mul_of_nonneg_right h1 (sq_nonneg (q 1))]
  have := hrow 0
  have := hrow 1
  linarith

/-- The exponents of the proof of Lemma 5.8: with `10 n₀ ≤ 9 (n + 1) + 9`,
`9^{n₀} 3^{(n+1)/10} ≤ 81 · 9^n 3^{-n/10}`. -/
theorem nine_pow_mul_rpow_le {m n n₀ : ℕ} (hm : m = n + 1) (h : 10 * n₀ ≤ 9 * m + 9) :
    (9 : ℝ) ^ n₀ * (3 : ℝ) ^ ((1 / 10 : ℝ) * ((m : ℕ) : ℝ)) ≤
      81 * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 10)) := by
  subst hm
  have h9 : ∀ k : ℕ, (9 : ℝ) ^ k = (3 : ℝ) ^ (2 * (k : ℝ)) := fun k => by
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h81 : (81 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by norm_num
  rw [h9, h9, h81, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hr : (10 * n₀ : ℝ) ≤ 9 * (n + 1) + 9 := by exact_mod_cast h
  push_cast
  linarith

/-- `3^{n+1} 3^{3(n+1)/4} ≤ 9 · 9^n 3^{-n/10}`. -/
theorem three_pow_mul_rpow_le {m n : ℕ} (hm : m = n + 1) :
    (3 : ℝ) ^ m * (3 : ℝ) ^ (3 * (m : ℝ) / 4) ≤
      9 * ((9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 10)) := by
  subst hm
  have h9 : (9 : ℝ) ^ n = (3 : ℝ) ^ (2 * (n : ℝ)) := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h3 : (3 : ℝ) ^ (n + 1) = (3 : ℝ) ^ ((n : ℝ) + 1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  rw [h9, h3, show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  linarith

/-- **The pointwise bound of the proof of Lemma 5.8**: the multiscale Poincaré inequality for the
coarsened minimizer of `μ(□_m, q)`, with the subcube averages split as in (5.36) of Armstrong and
Dario around arbitrary vectors `c_k`. -/
theorem exists_planarMuFlatness_le_pointwise :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (m n₀ : ℕ), (m : ℝ) / 2 ≤ n₀ → n₀ ≤ m →
      ∀ (ω : Configuration 2) (q ξ : Fin 2 → ℝ) (c : ℕ → Fin 2 → ℝ),
      planarFlatnessError ⟨m, 0⟩ (coarsen ω ⟨m, 0⟩ (planarMuMinimizer ω ⟨m, 0⟩ q)) ξ ≤
        (CM * (9 : ℝ) ^ n₀) * coarseEnergy ω ⟨m, 0⟩ (planarMuMinimizer ω ⟨m, 0⟩ q) +
        ∑ k ∈ Finset.Ico n₀ m, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
          (planarMuRestrictError ω ⟨m, 0⟩ k q +
            ((subcubesAt (⟨m, 0⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
              ∑ V ∈ subcubesAt (⟨m, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
                (planarMuGradAvg ω V q j - c k j) ^ 2) +
        (CM * (9 : ℝ) ^ n₀ * (ξ 0 ^ 2 + ξ 1 ^ 2) +
          ∑ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (3 * ∑ j : Fin 2, (c k j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2))) := by
  obtain ⟨CM, hCM, hM⟩ := exists_flatness_le_multiscale
  refine ⟨CM, hCM, fun m n₀ hn₀2 hn₀m ω q ξ c => ?_⟩
  set U : TriadicCube 2 := ⟨m, 0⟩ with hU
  set s := Finset.Ico n₀ m with hs
  set Ξ := ξ 0 ^ 2 + ξ 1 ^ 2 with hΞ
  set E : Configuration 2 → ℝ := fun ω => coarseEnergy ω U (planarMuMinimizer ω U q) with hE
  set A : ℕ → Configuration 2 → ℝ := fun k ω => planarMuRestrictError ω U k q with hAdef
  set B : ℕ → Configuration 2 → ℝ := fun k ω =>
    (((subcubesAt U k).card : ℝ))⁻¹ * ∑ V ∈ subcubesAt U k, ∑ j : Fin 2,
      (planarMuGradAvg ω V q j - c k j) ^ 2 with hBdef
  set Cc : ℕ → ℝ := fun k => ∑ j : Fin 2, (c k j - ξ j) ^ 2 with hCc
  change planarFlatnessError U (coarsen ω U (planarMuMinimizer ω U q)) ξ ≤
      (CM * (9 : ℝ) ^ n₀) * E ω + ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
        (A k ω + B k ω) +
      (CM * (9 : ℝ) ^ n₀ * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ))
  have hvol : U.volume = ((cube m (0 : Vertex 2)).card : ℝ) := by
    rw [show cube m (0 : Vertex 2) = U.toIntegerCube.vertices from rfl,
      card_toIntegerCube_vertices_eq U]
    rfl
  set w := coarsen ω U (planarMuMinimizer ω U q) with hw
  have h1 := hM m n₀ hn₀2 hn₀m 0 w ξ
  have hflat : planarFlatnessError U w ξ =
      ((cube m (0 : Vertex 2)).card : ℝ)⁻¹ * ∑ x ∈ cube m (0 : Vertex 2),
        (w x - affineFun ξ x -
          finsetMean (cube m (0 : Vertex 2)) (fun y => w y - affineFun ξ y)) ^ 2 := by
    rw [planarFlatnessError, hvol]
    rfl
  have hEω : ((cube m (0 : Vertex 2)).card : ℝ)⁻¹ *
      ∑ x ∈ cube m (0 : Vertex 2), gradNormSq (cube m (0 : Vertex 2)) w x = E ω := by
    simp only [hE, coarseEnergy, hvol]
    rfl
  rw [hflat]
  rw [hEω, ← hΞ] at h1
  refine h1.trans ?_
  have hk : ∀ k ∈ s, (3 : ℝ) ^ k * (((centers m (0 : Vertex 2) k).card : ℝ)⁻¹ *
      ∑ y ∈ centers m (0 : Vertex 2) k,
      ∑ j : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 +
        ((9 : ℝ) ^ k)⁻¹ * Ξ) ≤
      3 * (3 : ℝ) ^ k * (A k ω + B k ω) + (3 : ℝ) ^ k * (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ) := by
    intro k hks
    have hkm : k ≤ m := (Finset.mem_Ico.1 hks).2.le
    have h2 : ((centers m (0 : Vertex 2) k).card : ℝ)⁻¹ *
        ∑ y ∈ centers m (0 : Vertex 2) k, ∑ j : Fin 2,
        (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 ≤
        3 * A k ω + 3 * B k ω + 3 * Cc k :=
      sum_centers_coarsen_le (ω := ω) hkm 0 q ξ (c k)
    have h3 : (3 : ℝ) ^ k * (((centers m (0 : Vertex 2) k).card : ℝ)⁻¹ *
        ∑ y ∈ centers m (0 : Vertex 2) k,
        ∑ j : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2) ≤
        (3 : ℝ) ^ k * (3 * A k ω + 3 * B k ω + 3 * Cc k) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum hk
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ CM * (3 : ℝ) ^ m by positivity)
  rw [Finset.mul_sum, Finset.mul_sum] at hsum'
  have e1 : ∑ i ∈ s, CM * (3 : ℝ) ^ m * (3 * (3 : ℝ) ^ i * (A i ω + B i ω) +
      (3 : ℝ) ^ i * (3 * Cc i + ((9 : ℝ) ^ i)⁻¹ * Ξ)) =
      ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) * (A k ω + B k ω) +
      ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1] at hsum'
  have e2 : CM * (3 : ℝ) ^ m * ∑ k ∈ s, (3 : ℝ) ^ k *
      (((centers m (0 : Vertex 2) k).card : ℝ)⁻¹ * ∑ y ∈ centers m (0 : Vertex 2) k, ∑ j : Fin 2,
        (((9 : ℝ) ^ k)⁻¹ * gradSum (subcube k y) w j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * Ξ) =
      ∑ i ∈ s, CM * (3 : ℝ) ^ m * ((3 : ℝ) ^ i *
        (((centers m (0 : Vertex 2) i).card : ℝ)⁻¹ * ∑ y ∈ centers m (0 : Vertex 2) i, ∑ j : Fin 2,
          (((9 : ℝ) ^ i)⁻¹ * gradSum (subcube i y) w j - ξ j) ^ 2 + ((9 : ℝ) ^ i)⁻¹ * Ξ)) := by
    rw [Finset.mul_sum]
  have hE0 : 0 ≤ E ω := coarseEnergy_nonneg U (planarMuMinimizer ω U q)
  have e3 : CM * (9 : ℝ) ^ n₀ * (E ω + Ξ) = CM * (9 : ℝ) ^ n₀ * E ω + CM * (9 : ℝ) ^ n₀ * Ξ := by
    ring
  linarith

/-- **The arithmetic of the proof of Lemma 5.8.** -/
theorem planarFlatness_arith {τ : ℕ → ℝ} (hτ : ∀ l, 0 ≤ τ l) {CM Cg K CA C55 C57 Q Ξ : ℝ}
    (hCM : 0 ≤ CM) (hCg : 0 ≤ Cg) (hCA : 0 ≤ CA) (hC55 : 0 ≤ C55) (hC57 : 0 ≤ C57)
    (hQ0 : 0 ≤ Q) (hΞ0 : 0 ≤ Ξ) (hΞQ : Ξ ≤ 4 * K ^ 2 * Q) {m n n₀ : ℕ} (hm : m = n + 1)
    (h10b : 10 * n₀ ≤ 9 * m + 9) {Cc : ℕ → ℝ}
    (hCcT : ∀ k ∈ Finset.Ico n₀ m,
      Cc k ≤ CA * Q * (∑ l ∈ Finset.Ico k m, τ l + (3 : ℝ) ^ (-(k : ℝ) / 4))) :
    CM * (9 : ℝ) ^ n₀ * (Cg * Q * (3 : ℝ) ^ ((1 / 10 : ℝ) * ((m : ℕ) : ℝ))) +
      ∑ k ∈ Finset.Ico n₀ m, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (C55 * Q * (∑ l ∈ Finset.Ico k m, τ l + (3 : ℝ) ^ (-(k : ℝ) / 4)) +
          C57 * Q * (τ k + (3 : ℝ) ^ (-(k : ℝ) / 4))) +
      (CM * (9 : ℝ) ^ n₀ * Ξ + ∑ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ)) ≤
      (81 * (CM * (Cg + 4 * K ^ 2)) + 9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2)) +
          9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2))) * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) +
          ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range m, (3 : ℝ) ^ k * τ k) := by
  set L : ℝ := 3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  set s := Finset.Ico n₀ m with hs
  set ρ : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℝ) / 4) with hρ
  set T : ℕ → ℝ := fun k => ∑ l ∈ Finset.Ico k m, τ l with hT
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => by positivity
  have hT0 : ∀ k, 0 ≤ T k := fun k => Finset.sum_nonneg fun l _ => hτ l
  change CM * (9 : ℝ) ^ n₀ * (Cg * Q * (3 : ℝ) ^ ((1 / 10 : ℝ) * ((m : ℕ) : ℝ))) +
      ∑ k ∈ s, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (C55 * Q * (T k + ρ k) + C57 * Q * (τ k + ρ k)) +
      (CM * (9 : ℝ) ^ n₀ * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ)) ≤
      (81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L + 9 * L) * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) + ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range m, (3 : ℝ) ^ k * τ k)
  have hCcT' : ∀ k ∈ s, Cc k ≤ CA * Q * (T k + ρ k) := hCcT
  have hτT : ∀ k ∈ s, τ k ≤ T k := by
    intro k hk
    exact Finset.single_le_sum (f := fun l => τ l) (fun l _ => hτ l)
      (Finset.mem_Ico.2 ⟨le_rfl, (Finset.mem_Ico.1 hk).2⟩)
  have h9ρ : ∀ k, ((9 : ℝ) ^ k)⁻¹ ≤ ρ k := by
    intro k
    have h1 : ((9 : ℝ) ^ k)⁻¹ ≤ (Real.sqrt 3)⁻¹ ^ k := by
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      refine inv_anti₀ (by positivity) ?_
      have : Real.sqrt 3 ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      linarith
    exact h1.trans (inv_sqrt_three_pow_le k)
  have hterm : ∀ k ∈ s, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
      (C55 * Q * (T k + ρ k) + C57 * Q * (τ k + ρ k)) +
      CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ) ≤
      L * Q * (3 : ℝ) ^ m * ((3 : ℝ) ^ k * T k + (3 : ℝ) ^ k * ρ k) := by
    intro k hk
    have h1 := hCcT' k hk
    have h2 := hτT k hk
    have h3 : ((9 : ℝ) ^ k)⁻¹ * Ξ ≤ ρ k * (4 * K ^ 2 * Q) :=
      mul_le_mul (h9ρ k) hΞQ hΞ0 (hρ0 k)
    have hpos : 0 ≤ CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k := by positivity
    have hT := hT0 k
    have hρk := hρ0 k
    have e : L * Q * (3 : ℝ) ^ m * ((3 : ℝ) ^ k * T k + (3 : ℝ) ^ k * ρ k) =
        CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * ((3 * (C55 + C57) + (3 * CA + 4 * K ^ 2)) *
          (Q * (T k + ρ k))) := by
      rw [hL]
      ring
    rw [e]
    have hin : 3 * (C55 * Q * (T k + ρ k) + C57 * Q * (τ k + ρ k)) +
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ) ≤
        (3 * (C55 + C57) + (3 * CA + 4 * K ^ 2)) * (Q * (T k + ρ k)) := by
      have k1 : C57 * Q * (τ k + ρ k) ≤ C57 * Q * (T k + ρ k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k2 : ρ k * (4 * K ^ 2 * Q) ≤ 4 * K ^ 2 * (Q * (T k + ρ k)) := by
        linarith [mul_nonneg (mul_nonneg (sq_nonneg K) hQ0) hT]
      linarith
    have := mul_le_mul_of_nonneg_left hin hpos
    linarith
  have hsumterm := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hsumterm
  have hS1 : ∑ k ∈ s, (3 : ℝ) ^ k * T k ≤ 3 * ∑ l ∈ Finset.range m, (3 : ℝ) ^ l * τ l :=
    sum_Ico_three_pow_mul_sum_le hτ n₀ m
  have hS2 : ∑ k ∈ s, (3 : ℝ) ^ k * ρ k ≤ (3 : ℝ) ^ (3 * (m : ℝ) / 4) :=
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => Finset.mem_range.2 (Finset.mem_Ico.1 hk).2)
      fun k _ _ => by have := hρ0 k; positivity).trans (sum_range_three_pow_mul_rpow_le m)
  have hE1 := nine_pow_mul_rpow_le (n := n) (n₀ := n₀) hm h10b
  have hE2 := three_pow_mul_rpow_le (n := n) hm
  have h3m : (3 : ℝ) ^ m = 3 * (3 : ℝ) ^ n := by rw [hm, pow_succ]; ring
  have h93 : (9 : ℝ) ^ n * ((3 : ℝ) ^ n)⁻¹ = (3 : ℝ) ^ n := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow, mul_assoc,
      mul_inv_cancel₀ (by positivity), mul_one]
  have hr1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 / 10 : ℝ) * ((m : ℕ) : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  set R := ∑ k ∈ Finset.range m, (3 : ℝ) ^ k * τ k with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hτ k)
  set P := (9 : ℝ) ^ n * (3 : ℝ) ^ (-(n : ℝ) / 10) with hP
  have hP0 : 0 ≤ P := by positivity
  set G := (3 : ℝ) ^ ((1 / 10 : ℝ) * ((m : ℕ) : ℝ)) with hG
  have hfirst : CM * (9 : ℝ) ^ n₀ * (Cg * Q * G) + CM * (9 : ℝ) ^ n₀ * Ξ ≤
      81 * (CM * (Cg + 4 * K ^ 2)) * Q * P := by
    have k1 : CM * (9 : ℝ) ^ n₀ * Ξ ≤ CM * (9 : ℝ) ^ n₀ * (4 * K ^ 2 * Q * G) :=
      mul_le_mul_of_nonneg_left (hΞQ.trans (le_mul_of_one_le_right (by positivity) hr1))
        (by positivity)
    calc CM * (9 : ℝ) ^ n₀ * (Cg * Q * G) + CM * (9 : ℝ) ^ n₀ * Ξ
        ≤ CM * (9 : ℝ) ^ n₀ * (Cg * Q * G) + CM * (9 : ℝ) ^ n₀ * (4 * K ^ 2 * Q * G) := by
          linarith
      _ = CM * (Cg + 4 * K ^ 2) * Q * ((9 : ℝ) ^ n₀ * G) := by ring
      _ ≤ CM * (Cg + 4 * K ^ 2) * Q * (81 * P) :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = 81 * (CM * (Cg + 4 * K ^ 2)) * Q * P := by ring
  have hsecond : L * Q * (3 : ℝ) ^ m *
      (∑ k ∈ s, (3 : ℝ) ^ k * T k + ∑ k ∈ s, (3 : ℝ) ^ k * ρ k) ≤
      9 * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L * Q * P := by
    have k1 : (3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * T k) ≤
        9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) := by
      calc (3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * T k)
          ≤ (3 : ℝ) ^ m * (3 * R) := mul_le_mul_of_nonneg_left hS1 (by positivity)
        _ = 9 * ((9 : ℝ) ^ n * ((3 : ℝ) ^ n)⁻¹ * R) := by rw [h3m, h93]; ring
        _ = 9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) := by ring
    have k2 : (3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * ρ k) ≤ 9 * P :=
      (mul_le_mul_of_nonneg_left hS2 (by positivity)).trans hE2
    have hLQ : 0 ≤ L * Q := by positivity
    calc L * Q * (3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * T k + ∑ k ∈ s, (3 : ℝ) ^ k * ρ k)
        = L * Q * ((3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * T k)) +
          L * Q * ((3 : ℝ) ^ m * (∑ k ∈ s, (3 : ℝ) ^ k * ρ k)) := by ring
      _ ≤ L * Q * (9 * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R))) + L * Q * (9 * P) :=
          add_le_add (mul_le_mul_of_nonneg_left k1 hLQ) (mul_le_mul_of_nonneg_left k2 hLQ)
      _ = 9 * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L * Q * P := by ring
  have hfin : CM * (9 : ℝ) ^ n₀ * (Cg * Q * G) +
      ∑ k ∈ s, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (C55 * Q * (T k + ρ k) + C57 * Q * (τ k + ρ k)) +
      (CM * (9 : ℝ) ^ n₀ * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ)) ≤
      (81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L + 9 * L) * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) + ((3 : ℝ) ^ n)⁻¹ * R) := by
    have e : (81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L + 9 * L) * Q * (9 : ℝ) ^ n *
        ((3 : ℝ) ^ (-(n : ℝ) / 10) + ((3 : ℝ) ^ n)⁻¹ * R) =
        81 * (CM * (Cg + 4 * K ^ 2)) * Q * P + 9 * L * Q * P +
        9 * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) +
        ((81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L) * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) +
          9 * L * Q * P) := by
      rw [hP]
      ring
    have hX0 : 0 ≤ 81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L :=
      add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCM (add_nonneg hCg
        (mul_nonneg (by norm_num) (sq_nonneg K))))) (mul_nonneg (by norm_num) hL0)
    have hW0 : 0 ≤ (9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R) :=
      mul_nonneg (pow_nonneg (by norm_num) n)
        (mul_nonneg (inv_nonneg.2 (pow_nonneg (by norm_num) n)) hR0)
    have hextra : 0 ≤ (81 * (CM * (Cg + 4 * K ^ 2)) + 9 * L) * Q *
        ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L * Q * P :=
      add_nonneg (mul_nonneg (mul_nonneg hX0 hQ0) hW0)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL0) hQ0) hP0)
    rw [e]
    have hsplit := add_le_add hfirst (hsumterm.trans hsecond)
    calc _ = (CM * (9 : ℝ) ^ n₀ * (Cg * Q * G) + CM * (9 : ℝ) ^ n₀ * Ξ) +
          (∑ k ∈ s, 3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (C55 * Q * (T k + ρ k) + C57 * Q * (τ k + ρ k)) +
          ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ)) := by
          ring
      _ ≤ 81 * (CM * (Cg + 4 * K ^ 2)) * Q * P +
          (9 * L * Q * ((9 : ℝ) ^ n * (((3 : ℝ) ^ n)⁻¹ * R)) + 9 * L * Q * P) := hsplit
      _ ≤ _ := by linarith only [hextra]
  exact hfin

/-- **Flatness of the coarsened minimizers of `μ`** (Armstrong and Dario, Lemma 5.8, display
(5.32), in dimension two), from Lemmas 5.7 and 5.5 and the energy bound (4.24). -/
theorem exists_planarMuFlatness_majorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h57 : PlanarWeakConvergence p)
    (h55 : PlanarRestrictQuadCoarsenMu p) (hcg : PlanarCoarseGradMomentMu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin 2 → ℝ),
      ∃ Φ : Configuration 2 → ℝ, AEMeasurable Φ (latticeBondLaw 2 p) ∧ (∀ ω, 0 ≤ Φ ω) ∧
        (∀ ω, planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q))
            (planarAhomInvFinite p n *ᵥ q) ≤ Φ ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Φ ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (9 : ℝ) ^ n *
            ((3 : ℝ) ^ (-(n : ℝ) / 10) +
              ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨C57, hC57, h57⟩ := h57
  obtain ⟨C55, hC55, h55⟩ := h55
  obtain ⟨Cg, hCg, hcg⟩ := hcg (1 / 10) (by norm_num)
  obtain ⟨CM, hCM, hpw⟩ := exists_planarMuFlatness_le_pointwise
  obtain ⟨K, hK, hKb⟩ := exists_abs_planarAhomInvFinite_le hpc
  obtain ⟨CA, hCA, hA⟩ := exists_sum_sq_planarAhomInvFinite_sub_le hpc
  refine ⟨81 * (CM * (Cg + 4 * K ^ 2)) +
    9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2)) +
    9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2)), by positivity, fun n q => ?_⟩
  have hQ0 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  have hΞQ := sum_sq_mulVec_le (hKb n) q
  have h10a : 9 * (n + 1) ≤ 10 * ((9 * (n + 1) + 9) / 10) := by omega
  have h10b : 10 * ((9 * (n + 1) + 9) / 10) ≤ 9 * (n + 1) + 9 := by omega
  have hn₀m : (9 * (n + 1) + 9) / 10 ≤ n + 1 := by omega
  have hn₀2 : ((n + 1 : ℕ) : ℝ) / 2 ≤ (((9 * (n + 1) + 9) / 10 : ℕ) : ℝ) := by
    have : ((9 * (n + 1) : ℕ) : ℝ) ≤ ((10 * ((9 * (n + 1) + 9) / 10) : ℕ) : ℝ) := by
      exact_mod_cast h10a
    push_cast at this ⊢
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsA : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      9 * (⟨n + 1, 0⟩ : TriadicCube 2).scale ≤ 10 * k ∧ k < (⟨n + 1, 0⟩ : TriadicCube 2).scale :=
    fun k hk => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
      exact ⟨by change 9 * (n + 1) ≤ 10 * k; omega, h2⟩
  have hne : ∀ k, (subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).Nonempty := fun k =>
    ⟨scaleCube k 0, Finset.mem_image_of_mem _
      (((⟨n + 1, 0⟩ : TriadicCube 2).mem_toIntegerCube_vertices 0).2 (by
        intro i
        change |2 * ((0 : Vertex 2) i - (3 : ℤ) ^ (n + 1) * (0 : Vertex 2) i)| < (3 : ℤ) ^ (n + 1)
        simp))⟩
  have mF : ∀ k, ∀ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, AEMeasurable (fun ω =>
      ∑ j : Fin 2, (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
      (latticeBondLaw 2 p) :=
    fun k V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      ((aemeasurable_planarMuGradAvg hpc V q j).sub aemeasurable_const).pow_const 2
  have IB : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ∫⁻ ω, ENNReal.ofReal ((((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C57 * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k _
    refine lintegral_ofReal_avg_le (hne k) (fun V _ ω => Finset.sum_nonneg fun _ _ =>
      sq_nonneg _) (mF k) fun V hV => ?_
    have hVs : V.scale = k := scale_of_mem_subcubesAt hV
    have h := h57 V q
    rw [hVs] at h
    exact h
  obtain ⟨Φ, hΦm, hΦ0, hXΦ, hΦint⟩ := exists_majorant_of_le (μ := latticeBondLaw 2 p)
    (X := fun ω => planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) (planarAhomInvFinite p n *ᵥ q))
    (f₀ := fun ω => coarseEnergy ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q))
    (f := fun k ω => planarMuRestrictError ω ⟨n + 1, 0⟩ k q)
    (g := fun k ω => (((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
    (s := Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1))
    (a₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) *
        ((planarAhomInvFinite p n *ᵥ q) 0 ^ 2 + (planarAhomInvFinite p n *ᵥ q) 1 ^ 2) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (3 * ∑ j : Fin 2,
            ((planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2 +
          ((9 : ℝ) ^ k)⁻¹ *
            ((planarAhomInvFinite p n *ᵥ q) 0 ^ 2 + (planarAhomInvFinite p n *ᵥ q) 1 ^ 2)))
    (b₀ := Cg * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ ((1 / 10 : ℝ) * (((n + 1 : ℕ) : ℕ) : ℝ)))
    (bf := fun k => C55 * (q 0 ^ 2 + q 1 ^ 2) *
      (∑ l ∈ Finset.Ico k (n + 1), planarTau p l + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => C57 * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (by positivity) (fun k _ => by positivity)
    (add_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity))))
    (fun ω => coarseEnergy_nonneg _ _) (fun k _ ω => planarMuRestrictError_nonneg ω _ k q)
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (hcg ⟨n + 1, 0⟩ q).1 (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 q).1)
    (fun k _ => aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun V hV => mF k V hV))
    (fun ω => hpw (n + 1) ((9 * (n + 1) + 9) / 10) hn₀2 hn₀m ω q (planarAhomInvFinite p n *ᵥ q)
      (fun k => planarAhomInvFinite p k *ᵥ q))
    (hcg ⟨n + 1, 0⟩ q).2 (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 q).2) IB
    (by positivity)
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun l _ =>
      planarTau_nonneg p l) (by positivity)))
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (planarTau_nonneg p k) (by positivity)))
  refine ⟨Φ, hΦm, hΦ0, hXΦ, hΦint.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  refine planarFlatness_arith (τ := planarTau p) (planarTau_nonneg p) hCM hCg hCA hC55 hC57 hQ0
    (by positivity) hΞQ (m := n + 1) (n := n) rfl h10b (Cc := fun k =>
      ∑ j : Fin 2, ((planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2) ?_
  intro k hk
  have hkn : k ≤ n := by have := (Finset.mem_Ico.1 hk).2; omega
  refine (hA k n hkn q).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine add_le_add ?_ le_rfl
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
    fun l _ _ => planarTau_nonneg p l

/-- The bound of `exists_planarMuFlatness_majorant` for the expectation itself. -/
theorem exists_lintegral_planarMuFlatness_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h57 : PlanarWeakConvergence p)
    (h55 : PlanarRestrictQuadCoarsenMu p) (hcg : PlanarCoarseGradMomentMu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (planarFlatnessError ⟨n + 1, 0⟩
          (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q))
          (planarAhomInvFinite p n *ᵥ q)) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (9 : ℝ) ^ n *
          ((3 : ℝ) ^ (-(n : ℝ) / 10) +
            ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨C, hC, h⟩ := exists_planarMuFlatness_majorant hpc h57 h55 hcg
  refine ⟨C, hC, fun n q => ?_⟩
  obtain ⟨Φ, -, -, hle, hint⟩ := h n q
  exact (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hle ω)).trans hint

end Rigidity.Percolation
