import Rigidity.Proofs.Cluster.GeneralFlatnessInputs
import Rigidity.Proofs.Cluster.GeneralNablaAffineExpect

/-!
# Flatness of the coarsened maximizers of `ν`: the pointwise bound, in every dimension

Let `v = v(·, □_m, q)` be the maximizer of `ν(□_m, q)` (zero off the resolution of `□_m`) and
`w = [v]_𝒫` its coarsening. The multiscale Poincaré inequality in the form
`exists_cubeFlatness_le_multiscale`, with the block averages of `∇w` on the subcubes `V` of scale
`k` split as in display (5.36) of Armstrong and Dario,

`|V|⁻¹ ⟨∇w⟩_V - ξ = |V|⁻¹ (⟨∇w⟩_V - ⟨∇[v(·, V, q)]_𝒫⟩_V) + (|V|⁻¹ ⟨∇[v(·, V, q)]_𝒫⟩_V - c) + (c - ξ)`

(`sum_centers_coarsen_nu_le_general`: the first term is the quantity of Lemma 5.5), gives

`‖w - ℓ_ξ - (w - ℓ_ξ)_{□_m}‖²_{L̲²} ≤ C 3^{2n₀} ‖∇w‖²_{L̲²}
  + ∑_{k=n₀}^{m-1} 3C 3^m 3^k (A_k + B_k) + C 3^{2n₀} |ξ|² + ∑_k C 3^m 3^k (3 |c_k - ξ|² + 3^{-2k} |ξ|²)`

(`exists_cubeNuFlatness_le_pointwise`), `A_k` the quantity of display (5.12) at scale `k` and `B_k`
the mean over the subcubes of `| |V|⁻¹ ⟨∇[v(·, V, q)]_𝒫⟩_V - c_k |²`. This is the pointwise bound
of the proof of Lemma 5.8 of Armstrong and Dario for `ν`, in every dimension, as the
two-dimensional `Rigidity.Percolation.exists_planarNuFlatness_le_pointwise`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The mean square deviation `|U|⁻¹ ∑_{x ∈ U} |w(x) - x · ξ - c|²` of a function from the
affine function of slope `ξ`, `c` the mean of `w - ℓ_ξ` over `U`. -/
noncomputable def cubeFlatnessError (U : TriadicCube d) (w : Vertex d → ℝ) (ξ : Fin d → ℝ) : ℝ :=
  U.latticeVolume⁻¹ * ∑ x ∈ U.toIntegerCube.vertices,
    (w x - Rigidity.Proofs.Multiscale.affineFun ξ x -
      Rigidity.Proofs.Multiscale.finsetMean U.toIntegerCube.vertices
        (fun y => w y - Rigidity.Proofs.Multiscale.affineFun ξ y)) ^ 2

/-- The normalized energy `|U|⁻¹ ∑_{x ∈ U} |∇[w]_𝒫|²(x)` of the coarsening. -/
noncomputable def cubeCoarseEnergy (ω : Configuration d) (U : TriadicCube d) (w : CubeFun ω U) :
    ℝ :=
  U.latticeVolume⁻¹ * ∑ x ∈ U.toIntegerCube.vertices,
    Rigidity.Proofs.Multiscale.gradNormSq U.toIntegerCube.vertices
      (fun x => cubeExtend ω U w (partitionAnchor ω x)) x

/-- The spatial average `|V|⁻¹ ⟨eⱼ, ∇[v(·, V, ξ)]_𝒫⟩_V` of the coarsened gradient of the maximizer
of `ν(V, ξ)`. -/
noncomputable def cubeNuGradAvg (ω : Configuration d) (V : TriadicCube d) (ξ : Fin d → ℝ)
    (j : Fin d) : ℝ :=
  cubeCoarsePairing ω V (Pi.single j 1) (cubeNuSolution ω V ξ) / V.latticeVolume

theorem cubeCoarseEnergy_nonneg (U : TriadicCube d) (w : CubeFun ω U) :
    0 ≤ cubeCoarseEnergy ω U w := by
  refine mul_nonneg (inv_nonneg.2 U.latticeVolume_pos.le) (Finset.sum_nonneg fun x _ => ?_)
  simp only [Rigidity.Proofs.Multiscale.gradNormSq]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

theorem add_add_sq_le_three_mul (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

theorem inv_mul_le_of_le_three_mul {N X A B C : ℝ} (hN : 0 < N)
    (h : X ≤ 3 * A + 3 * B + 3 * (N * C)) :
    N⁻¹ * X ≤ 3 * (N⁻¹ * A) + 3 * (N⁻¹ * B) + 3 * C := by
  have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hN.le)
  have e : N⁻¹ * (3 * A + 3 * B + 3 * (N * C)) =
      3 * (N⁻¹ * A) + 3 * (N⁻¹ * B) + N⁻¹ * N * (3 * C) := by ring
  rw [e, inv_mul_cancel₀ hN.ne', one_mul] at h2
  exact h2

/-- **The subcube averages of the coarsened gradient of a maximizer of `ν`**, split as in the
proof of (5.36) of Armstrong and Dario. -/
theorem sum_centers_coarsen_nu_le_general {m k : ℕ} (hk : k ≤ m) (z : Vertex d)
    (q ξ c : Fin d → ℝ) :
    ((Rigidity.Proofs.Multiscale.centers m z k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m z k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y)
            (fun x => cubeExtend ω ⟨m, z⟩ (cubeNuSolution ω ⟨m, z⟩ q) (partitionAnchor ω x)) j -
              ξ j) ^ 2 ≤
      3 * cubeNuRestrictError ω ⟨m, z⟩ k q +
      3 * ((((⟨m, z⟩ : TriadicCube d).subcubesAt k).card : ℝ)⁻¹ *
        ∑ V ∈ (⟨m, z⟩ : TriadicCube d).subcubesAt k, ∑ j : Fin d,
          (cubeNuGradAvg ω V q j - c j) ^ 2) +
      3 * ∑ j : Fin d, (c j - ξ j) ^ 2 := by
  set U : TriadicCube d := ⟨m, z⟩ with hU
  set w : Vertex d → ℝ := fun x => cubeExtend ω U (cubeNuSolution ω U q) (partitionAnchor ω x)
    with hw
  have hcard := card_subcubesAt_eq_general (d := d) hk z
  rw [← hU] at hcard
  have hc : (0 : ℝ) < (Rigidity.Proofs.Multiscale.centers m z k).card := by
    rw [Rigidity.Proofs.Multiscale.card_centers hk]
    positivity
  rw [Rigidity.Proofs.Multiscale.sum_centers hk z (fun B => ∑ j : Fin d,
    ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum B w j - ξ j) ^ 2)]
  rw [cubeNuRestrictError, cubeRestrictError, hcard]
  rw [sum_subcubesAt_eq_general hk z, sum_subcubesAt_eq_general hk z]
  set N : ℝ := ((Rigidity.Proofs.Multiscale.centers m z k).card : ℝ) with hN
  have hterm : ∀ j ∈ Rigidity.Proofs.Multiscale.cube (m - k) z,
      ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ *
        Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i - ξ i) ^ 2 ≤
        3 * ∑ i : Fin d, ((latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
            (fun _ => Pi.single i 1) (fun x => cubeExtend ω U (cubeNuSolution ω U q)
              (partitionAnchor ω x)) -
          cubeCoarsePairing ω ⟨k, j⟩ (Pi.single i 1) (cubeNuSolution ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube d).latticeVolume) ^ 2 +
        3 * ∑ i : Fin d, (cubeNuGradAvg ω ⟨k, j⟩ q i - c i) ^ 2 +
        3 * ∑ i : Fin d, (c i - ξ i) ^ 2 := by
    intro j _
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hvol : (⟨k, j⟩ : TriadicCube d).latticeVolume = ((3 : ℝ) ^ k) ^ d := rfl
    have hG : Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i =
        latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
          (fun _ => Pi.single i 1) w := gradSum_eq_latticeEdgePairing _ w i
    have e : (((3 : ℝ) ^ k) ^ d)⁻¹ *
        Rigidity.Proofs.Multiscale.gradSum (Rigidity.Proofs.Multiscale.cube k j) w i - ξ i =
        (latticeEdgePairing (⟨k, j⟩ : TriadicCube d).toIntegerCube.vertices
            (fun _ => Pi.single i 1) w -
          cubeCoarsePairing ω ⟨k, j⟩ (Pi.single i 1) (cubeNuSolution ω ⟨k, j⟩ q)) /
            (⟨k, j⟩ : TriadicCube d).latticeVolume +
        (cubeNuGradAvg ω ⟨k, j⟩ q i - c i) + (c i - ξ i) := by
      rw [cubeNuGradAvg, hvol, hG]
      have : (0 : ℝ) < ((3 : ℝ) ^ k) ^ d := by positivity
      field_simp
      ring
    rw [e]
    exact add_add_sq_le_three_mul _ _ _
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const] at hsum
  have hcube : ((Rigidity.Proofs.Multiscale.cube (m - k) z).card : ℝ) = N := by
    rw [hN, Rigidity.Proofs.Multiscale.card_centers hk, Rigidity.Proofs.Multiscale.card_cube]
  rw [nsmul_eq_mul, hcube] at hsum
  exact inv_mul_le_of_le_three_mul hc hsum

/-- **The pointwise bound of the proof of Lemma 5.8 for `ν`**: the multiscale Poincaré inequality
for the coarsened maximizer of `ν(□_m, q)`, with the subcube averages split as in (5.36) of
Armstrong and Dario around arbitrary vectors `c_k`. -/
theorem exists_cubeNuFlatness_le_pointwise :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ (m n₀ : ℕ), (m : ℝ) / 2 ≤ n₀ → n₀ ≤ m →
      ∀ (ω : Configuration d) (q ξ : Fin d → ℝ) (c : ℕ → Fin d → ℝ),
      cubeFlatnessError ⟨m, 0⟩ (fun x => cubeExtend ω ⟨m, 0⟩ (cubeNuSolution ω ⟨m, 0⟩ q)
          (partitionAnchor ω x)) ξ ≤
        (CM * (3 : ℝ) ^ (2 * n₀)) * cubeCoarseEnergy ω ⟨m, 0⟩ (cubeNuSolution ω ⟨m, 0⟩ q) +
        ∑ k ∈ Finset.Ico n₀ m, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
          (cubeNuRestrictError ω ⟨m, 0⟩ k q +
            (((⟨m, 0⟩ : TriadicCube d).subcubesAt k).card : ℝ)⁻¹ *
              ∑ V ∈ (⟨m, 0⟩ : TriadicCube d).subcubesAt k, ∑ j : Fin d,
                (cubeNuGradAvg ω V q j - c k j) ^ 2) +
        (CM * (3 : ℝ) ^ (2 * n₀) * ∑ i, ξ i ^ 2 +
          ∑ k ∈ Finset.Ico n₀ m, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
            (3 * ∑ j : Fin d, (c k j - ξ j) ^ 2 + (((3 : ℝ) ^ k) ^ 2)⁻¹ * ∑ i, ξ i ^ 2)) := by
  obtain ⟨CM, hCM, hM⟩ := exists_cubeFlatness_le_multiscale (d := d)
  refine ⟨CM, hCM, fun m n₀ hn₀2 hn₀m ω q ξ c => ?_⟩
  set U : TriadicCube d := ⟨m, 0⟩ with hU
  set s := Finset.Ico n₀ m with hs
  set Ξ := ∑ i, ξ i ^ 2 with hΞ
  set E : ℝ := cubeCoarseEnergy ω U (cubeNuSolution ω U q) with hE
  set A : ℕ → ℝ := fun k => cubeNuRestrictError ω U k q with hAdef
  set B : ℕ → ℝ := fun k =>
    (((U.subcubesAt k).card : ℝ))⁻¹ * ∑ V ∈ U.subcubesAt k, ∑ j : Fin d,
      (cubeNuGradAvg ω V q j - c k j) ^ 2 with hBdef
  set Cc : ℕ → ℝ := fun k => ∑ j : Fin d, (c k j - ξ j) ^ 2 with hCc
  change cubeFlatnessError U (fun x => cubeExtend ω U (cubeNuSolution ω U q)
        (partitionAnchor ω x)) ξ ≤
      (CM * (3 : ℝ) ^ (2 * n₀)) * E + ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) *
        (A k + B k) +
      (CM * (3 : ℝ) ^ (2 * n₀) * Ξ + ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k *
        (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ))
  have hvol : U.latticeVolume =
      ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ) := by
    rw [show Rigidity.Proofs.Multiscale.cube m (0 : Vertex d) = U.toIntegerCube.vertices from rfl,
      U.card_toIntegerCube_vertices]
  set w : Vertex d → ℝ := fun x => cubeExtend ω U (cubeNuSolution ω U q) (partitionAnchor ω x)
    with hw
  have h1 := hM m n₀ hn₀2 hn₀m 0 w ξ
  have hflat : cubeFlatnessError U w ξ =
      ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ)⁻¹ *
        ∑ x ∈ Rigidity.Proofs.Multiscale.cube m (0 : Vertex d),
        (w x - Rigidity.Proofs.Multiscale.affineFun ξ x -
          Rigidity.Proofs.Multiscale.finsetMean (Rigidity.Proofs.Multiscale.cube m (0 : Vertex d))
            (fun y => w y - Rigidity.Proofs.Multiscale.affineFun ξ y)) ^ 2 := by
    rw [cubeFlatnessError, hvol]
    rfl
  have hEω : ((Rigidity.Proofs.Multiscale.cube m (0 : Vertex d)).card : ℝ)⁻¹ *
      ∑ x ∈ Rigidity.Proofs.Multiscale.cube m (0 : Vertex d),
        Rigidity.Proofs.Multiscale.gradNormSq (Rigidity.Proofs.Multiscale.cube m (0 : Vertex d))
          w x = E := by
    simp only [hE, cubeCoarseEnergy, hvol]
    rfl
  rw [hflat]
  rw [hEω, ← hΞ] at h1
  refine h1.trans ?_
  have hk : ∀ k ∈ s, (3 : ℝ) ^ k *
      (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y) w j - ξ j) ^ 2 +
        (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) ≤
      3 * (3 : ℝ) ^ k * (A k + B k) + (3 : ℝ) ^ k * (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) := by
    intro k hks
    have hkm : k ≤ m := (Finset.mem_Ico.1 hks).2.le
    have h2 := sum_centers_coarsen_nu_le_general (ω := ω) hkm 0 q ξ (c k)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 3 ^ k by positivity)
    nlinarith
  have hsum := Finset.sum_le_sum hk
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ CM * (3 : ℝ) ^ m by positivity)
  rw [Finset.mul_sum, Finset.mul_sum] at hsum'
  have e1 : ∑ i ∈ s, CM * (3 : ℝ) ^ m * (3 * (3 : ℝ) ^ i * (A i + B i) +
      (3 : ℝ) ^ i * (3 * Cc i + (((3 : ℝ) ^ i) ^ 2)⁻¹ * Ξ)) =
      ∑ k ∈ s, (3 * CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k) * (A k + B k) +
      ∑ k ∈ s, CM * (3 : ℝ) ^ m * (3 : ℝ) ^ k * (3 * Cc k + (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1] at hsum'
  have hE0 : 0 ≤ E := cubeCoarseEnergy_nonneg U (cubeNuSolution ω U q)
  have e3 : CM * (3 : ℝ) ^ (2 * n₀) * (E + Ξ) =
      CM * (3 : ℝ) ^ (2 * n₀) * E + CM * (3 : ℝ) ^ (2 * n₀) * Ξ := by ring
  have e2 : CM * (3 : ℝ) ^ m * ∑ k ∈ s, (3 : ℝ) ^ k *
      (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k).card : ℝ)⁻¹ *
        ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) k, ∑ j : Fin d,
          ((((3 : ℝ) ^ k) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
            (Rigidity.Proofs.Multiscale.subcube k y) w j - ξ j) ^ 2 +
        (((3 : ℝ) ^ k) ^ 2)⁻¹ * Ξ) =
      ∑ i ∈ s, CM * (3 : ℝ) ^ m * ((3 : ℝ) ^ i *
        (((Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) i).card : ℝ)⁻¹ *
          ∑ y ∈ Rigidity.Proofs.Multiscale.centers m (0 : Vertex d) i, ∑ j : Fin d,
            ((((3 : ℝ) ^ i) ^ d)⁻¹ * Rigidity.Proofs.Multiscale.gradSum
              (Rigidity.Proofs.Multiscale.subcube i y) w j - ξ j) ^ 2 +
          (((3 : ℝ) ^ i) ^ 2)⁻¹ * Ξ)) := by
    rw [Finset.mul_sum]
  linarith

end Rigidity.Percolation
