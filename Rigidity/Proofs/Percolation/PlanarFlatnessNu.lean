import Rigidity.Proofs.Percolation.PlanarFlatnessMu
import Rigidity.Proofs.Percolation.PlanarNablaAffineMoments

/-!
# Flatness of the coarsened maximizers of `ν` (Lemma 5.8 of Armstrong and Dario, second part)

Let `v = v(·, □_{n+1}, ξ)` be the maximizer of `ν(□_{n+1}, ξ)` and `[v]_P` its coarsening. From
Lemma 5.5 for `ν`, the bound (4.25) on the energy of `[v]_P` and display (4.26) in `L²` (in place
of Lemma 5.7, as in Armstrong and Dario), the multiscale Poincaré inequality with
`n₀ = ⌈(9/10)(n + 1)⌉` gives

`E[|□_{n+1}|⁻¹ ∑_{x ∈ □_{n+1}} |[v]_P(x) - x · ξ - c|²]
  ≤ C |ξ|² 3^{2n} (3^{-n/10} + 3^{-n} ∑_{k=0}^{n} 3^k τ_k)`,

`c` the mean of `[v]_P - x · ξ` over `□_{n+1}`. This is display (5.33) of Lemma 5.8 of Armstrong
and Dario in dimension two, with the rate `3^{-n/10}` of (5.32) (they print `3^{-2n/(2d+1)}`; the
proof of (5.32), which they follow, gives `3^{-n/(4d+2)}`, the rate used in Lemma 5.9).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (cube centers subcube gradSum gradNormSq finsetMean affineFun
  card_centers sum_centers)

variable {ω : Configuration 2}

/-- **The subcube averages of the coarsened gradient of a maximizer of `ν`**, split as in the
proof of (5.36) of Armstrong and Dario. -/
theorem sum_centers_coarsen_nu_le {m k : ℕ} (hk : k ≤ m) (z : Vertex 2) (q ξ c : Fin 2 → ℝ) :
    ((centers m z k).card : ℝ)⁻¹ * ∑ y ∈ centers m z k, ∑ j : Fin 2,
        (((9 : ℝ) ^ k)⁻¹ *
          gradSum (subcube k y) (coarsen ω ⟨m, z⟩ (planarNuSolution ω ⟨m, z⟩ q)) j - ξ j) ^ 2 ≤
      3 * planarNuRestrictError ω ⟨m, z⟩ k q +
      3 * (((subcubesAt (⟨m, z⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
        ∑ V ∈ subcubesAt (⟨m, z⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarNuGradAvg ω V q j - c j) ^ 2) +
      3 * ∑ j : Fin 2, (c j - ξ j) ^ 2 := by
  set U : TriadicCube 2 := ⟨m, z⟩ with hU
  set w := coarsen ω U (planarNuSolution ω U q) with hw
  have hcard := card_subcubesAt_eq hk z
  rw [← hU] at hcard
  have hc : (0 : ℝ) < (centers m z k).card := by
    rw [card_centers hk]
    positivity
  rw [sum_centers hk z (fun B => ∑ j : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum B w j - ξ j) ^ 2)]
  rw [planarNuRestrictError, hcard]
  rw [sum_subcubesAt_eq hk z, sum_subcubesAt_eq hk z]
  set N : ℝ := ((centers m z k).card : ℝ) with hN
  have hterm : ∀ j ∈ cube (m - k) z,
      ∑ i : Fin 2, (((9 : ℝ) ^ k)⁻¹ * gradSum (cube k j) w i - ξ i) ^ 2 ≤
        3 * ∑ i : Fin 2, ((cubeGradSum ⟨k, j⟩ w i -
          coarsePairing ω ⟨k, j⟩ (Pi.single i 1) (planarNuSolution ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube 2).volume) ^ 2 +
        3 * ∑ i : Fin 2, (planarNuGradAvg ω ⟨k, j⟩ q i - c i) ^ 2 +
        3 * ∑ i : Fin 2, (c i - ξ i) ^ 2 := by
    intro j _
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hvol : (⟨k, j⟩ : TriadicCube 2).volume = (9 : ℝ) ^ k := rfl
    have e : ((9 : ℝ) ^ k)⁻¹ * gradSum (cube k j) w i - ξ i =
        (cubeGradSum ⟨k, j⟩ w i -
          coarsePairing ω ⟨k, j⟩ (Pi.single i 1) (planarNuSolution ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube 2).volume +
        (planarNuGradAvg ω ⟨k, j⟩ q i - c i) + (c i - ξ i) := by
      have hG : cubeGradSum ⟨k, j⟩ w i = gradSum (cube k j) w i := rfl
      rw [planarNuGradAvg, hvol, hG]
      have : (0 : ℝ) < 9 ^ k := by positivity
      field_simp
      ring
    rw [e]
    exact add_add_sq_le _ _ _
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const] at hsum
  have hcube : ((cube (m - k) z).card : ℝ) = N := by
    rw [hN, card_centers hk, Rigidity.Proofs.Multiscale.card_cube]
  rw [nsmul_eq_mul, hcube] at hsum
  exact inv_mul_le_of_le_three hc hsum

/-- **The pointwise bound of the proof of Lemma 5.8 for `ν`**: the multiscale Poincaré inequality
for the coarsened maximizer of `ν(□_m, q)`, with the subcube averages split as in (5.36) of
Armstrong and Dario around arbitrary vectors `c_k`. -/
theorem exists_planarNuFlatness_le_pointwise :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (m n₀ : ℕ), (m : ℝ) / 2 ≤ n₀ → n₀ ≤ m →
      ∀ (ω : Configuration 2) (q ξ : Fin 2 → ℝ) (c : ℕ → Fin 2 → ℝ),
      planarFlatnessError ⟨m, 0⟩ (coarsen ω ⟨m, 0⟩ (planarNuSolution ω ⟨m, 0⟩ q)) ξ ≤
        (CM * (9 : ℝ) ^ n₀) * coarseEnergy ω ⟨m, 0⟩ (planarNuSolution ω ⟨m, 0⟩ q) +
        ∑ k ∈ Finset.Ico n₀ m, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
          (planarNuRestrictError ω ⟨m, 0⟩ k q +
            ((subcubesAt (⟨m, 0⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
              ∑ V ∈ subcubesAt (⟨m, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
                (planarNuGradAvg ω V q j - c k j) ^ 2) +
        (CM * (9 : ℝ) ^ n₀ * (ξ 0 ^ 2 + ξ 1 ^ 2) +
          ∑ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (3 * ∑ j : Fin 2, (c k j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2))) := by
  obtain ⟨CM, hCM, hM⟩ := exists_flatness_le_multiscale
  refine ⟨CM, hCM, fun m n₀ hn₀2 hn₀m ω q ξ c => ?_⟩
  set U : TriadicCube 2 := ⟨m, 0⟩ with hU
  set s := Finset.Ico n₀ m with hs
  set Ξ := ξ 0 ^ 2 + ξ 1 ^ 2 with hΞ
  set E : Configuration 2 → ℝ := fun ω => coarseEnergy ω U (planarNuSolution ω U q) with hE
  set A : ℕ → Configuration 2 → ℝ := fun k ω => planarNuRestrictError ω U k q with hAdef
  set B : ℕ → Configuration 2 → ℝ := fun k ω =>
    (((subcubesAt U k).card : ℝ))⁻¹ * ∑ V ∈ subcubesAt U k, ∑ j : Fin 2,
      (planarNuGradAvg ω V q j - c k j) ^ 2 with hBdef
  set Cc : ℕ → ℝ := fun k => ∑ j : Fin 2, (c k j - ξ j) ^ 2 with hCc
  change planarFlatnessError U (coarsen ω U (planarNuSolution ω U q)) ξ ≤
      (CM * (9 : ℝ) ^ n₀) * E ω + ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
        (A k ω + B k ω) +
      (CM * (9 : ℝ) ^ n₀ * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + ((9 : ℝ) ^ k)⁻¹ * Ξ))
  have hvol : U.volume = ((cube m (0 : Vertex 2)).card : ℝ) := by
    rw [show cube m (0 : Vertex 2) = U.toIntegerCube.vertices from rfl,
      card_toIntegerCube_vertices_eq U]
    rfl
  set w := coarsen ω U (planarNuSolution ω U q) with hw
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
      sum_centers_coarsen_nu_le (ω := ω) hkm 0 q ξ (c k)
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
  have hE0 : 0 ≤ E ω := coarseEnergy_nonneg U (planarNuSolution ω U q)
  have e3 : CM * (9 : ℝ) ^ n₀ * (E ω + Ξ) = CM * (9 : ℝ) ^ n₀ * E ω + CM * (9 : ℝ) ^ n₀ * Ξ := by
    ring
  linarith

/-- **Flatness of the coarsened maximizers of `ν`** (Armstrong and Dario, Lemma 5.8, display
(5.33), in dimension two), from Lemma 5.5 and the energy bound (4.25). -/
theorem exists_planarNuFlatness_majorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h55 : PlanarRestrictQuadCoarsenNu p)
    (hcg : PlanarCoarseGradMomentNu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ξ : Fin 2 → ℝ),
      ∃ Φ : Configuration 2 → ℝ, AEMeasurable Φ (latticeBondLaw 2 p) ∧ (∀ ω, 0 ≤ Φ ω) ∧
        (∀ ω, planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤ Φ ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Φ ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (9 : ℝ) ^ n *
            ((3 : ℝ) ^ (-(n : ℝ) / 10) +
              ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨Cn, hCn, hNab⟩ := exists_nablaAffineMajorant_le hpc
  obtain ⟨C55, hC55, h55⟩ := h55
  obtain ⟨Cg, hCg, hcg⟩ := hcg (1 / 10) (by norm_num)
  obtain ⟨CM, hCM, hpw⟩ := exists_planarNuFlatness_le_pointwise
  refine ⟨81 * (CM * (Cg + 4 * 1 ^ 2)) +
    9 * (3 * CM * (C55 + Cn) + CM * (3 * 0 + 4 * 1 ^ 2)) +
    9 * (3 * CM * (C55 + Cn) + CM * (3 * 0 + 4 * 1 ^ 2)), by positivity, fun n ξ => ?_⟩
  have hQ0 : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  have hΞQ : ξ 0 ^ 2 + ξ 1 ^ 2 ≤ 4 * 1 ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by linarith
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
  have IB : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ∫⁻ ω, ENNReal.ofReal ((((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ)
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (Cn * (ξ 0 ^ 2 + ξ 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k _
    refine lintegral_ofReal_avg_le (hne k) (fun V _ ω => nablaAffineMajorant_nonneg V ξ ω)
      (fun V _ => (measurable_nablaAffineMajorant V ξ).aemeasurable) fun V hV => ?_
    have hVs : V.scale = k := scale_of_mem_subcubesAt hV
    refine (hNab V ξ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hVs]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (planarTau_nonneg p k))
      (by positivity)
  have hX : ∀ ω, planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤
      (CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10)) *
        coarseEnergy ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
        (3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k) *
        (planarNuRestrictError ω ⟨n + 1, 0⟩ k ξ +
          ((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
            ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ) +
      (CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) * (ξ 0 ^ 2 + ξ 1 ^ 2) +
        ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
          (3 * ∑ j : Fin 2, (ξ j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2))) := by
    intro ω
    refine (hpw (n + 1) ((9 * (n + 1) + 9) / 10) hn₀2 hn₀m ω ξ ξ (fun _ => ξ)).trans ?_
    refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)) le_rfl
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun V _ => le_nablaAffineMajorant V ξ ω)
      (by positivity)
  obtain ⟨Φ, hΦm, hΦ0, hXΦ, hΦint⟩ := exists_majorant_of_le (μ := latticeBondLaw 2 p)
    (X := fun ω => planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ)
    (f₀ := fun ω => coarseEnergy ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ))
    (f := fun k ω => planarNuRestrictError ω ⟨n + 1, 0⟩ k ξ)
    (g := fun k ω => (((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ)
    (s := Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1))
    (a₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) * (ξ 0 ^ 2 + ξ 1 ^ 2) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (3 * ∑ j : Fin 2, (ξ j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2)))
    (b₀ := Cg * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ ((1 / 10 : ℝ) * (((n + 1 : ℕ) : ℕ) : ℝ)))
    (bf := fun k => C55 * (ξ 0 ^ 2 + ξ 1 ^ 2) *
      (∑ l ∈ Finset.Ico k (n + 1), planarTau p l + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => Cn * (ξ 0 ^ 2 + ξ 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (by positivity) (fun k _ => by positivity)
    (add_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity))))
    (fun ω => coarseEnergy_nonneg _ _)
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun V _ => nablaAffineMajorant_nonneg V ξ ω))
    (hcg ⟨n + 1, 0⟩ ξ).1 (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 ξ).1)
    (fun k _ => aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun V _ =>
      (measurable_nablaAffineMajorant V ξ).aemeasurable))
    hX (hcg ⟨n + 1, 0⟩ ξ).2 (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 ξ).2) IB
    (by positivity)
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun l _ =>
      planarTau_nonneg p l) (by positivity)))
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (planarTau_nonneg p k) (by positivity)))
  refine ⟨Φ, hΦm, hΦ0, hXΦ, hΦint.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  refine planarFlatness_arith (τ := planarTau p) (planarTau_nonneg p) hCM hCg le_rfl hC55 hCn hQ0
    hQ0 hΞQ (m := n + 1) (n := n) rfl h10b (Cc := fun _ => ∑ j : Fin 2, (ξ j - ξ j) ^ 2) ?_
  intro k _
  simp

/-- The bound of `exists_planarNuFlatness_majorant` for the expectation itself. -/
theorem exists_lintegral_planarNuFlatness_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h55 : PlanarRestrictQuadCoarsenNu p)
    (hcg : PlanarCoarseGradMomentNu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ξ : Fin 2 → ℝ),
      ∫⁻ ω, ENNReal.ofReal (planarFlatnessError ⟨n + 1, 0⟩
          (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (9 : ℝ) ^ n *
          ((3 : ℝ) ^ (-(n : ℝ) / 10) +
            ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨C, hC, h⟩ := exists_planarNuFlatness_majorant hpc h55 hcg
  refine ⟨C, hC, fun n ξ => ?_⟩
  obtain ⟨Φ, -, -, hle, hint⟩ := h n ξ
  exact (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hle ω)).trans hint

end Rigidity.Percolation
