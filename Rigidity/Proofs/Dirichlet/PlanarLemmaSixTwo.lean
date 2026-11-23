import Rigidity.Proofs.Dirichlet.PlanarMuTest
import Rigidity.Proofs.Dirichlet.SubcubeMuTest
import Rigidity.Proofs.Dirichlet.Interpolation

/-!
# Lemma 6.2 of Armstrong and Dario in dimension two

Let `□_m` be resolved, with all partition cubes of its vertices of scale at most `k`, let `u` be
harmonic on `C_*(□_m)` off `∂□_m`, `w̃` the boundary interpolation of the coarsened function and
`u_hom` the solution of the discrete Dirichlet problem for `ā = σ I` with datum `w̃`. Suppose that
`|μ(T, q) + |q|²/(2σ)| ≤ ε |q|²` for every triadic cube `T ⊆ □_m` of scale `k`. Then, with
`N = 3^n ≥ K = 3^k` and `M = N/K − 1`, at every translate `x + □` of side `N` away from `∂□_m`
the triadic cubes of scale `k` inside `x + □` starting at the first point of the triadic grid of
scale `k` after `x` form a block of `M²` tiles on which `u` is tested in `μ` (`planarMu_le_test`),
and `exists_mu_test_of_subcubes` gives the `μ` test of the lattice Lemma 6.2 at `x`
(`innerEdgeEnergy_dirichletSolution_div_le_of_mu_test`), with the errors summed by
`sum_subcube_errors_le`:
`L⁻² E_ā(u_hom) ≤ L⁻² E(u) + 2 (ε σ² + σ β/2 + σ γ + σ N^{-1/2}) L⁻² Σ |∇w̃|² + (layer term)`,
`β = 1 − (MK)²/N²`, `γ = N^{-1/2} + β^{1/2} + K^{-1/2}` (`planar_lemmaSixTwo`). This is
Armstrong and Dario, Lemma 6.2, with the energy of the edges inside `□_m`, the discrete
homogenized problem and the triadic mesoscopic cubes.
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Dirichlet

variable {ω : Configuration 2}

/-- The first point of the triadic grid of scale `k` (the corners of the triadic cubes of scale
`k`) at or after `x` in each coordinate. -/
def triadicGridCorner (k : ℕ) (x : Vertex 2) : Vertex 2 :=
  fun t => x t + ((-((3 : ℤ) ^ k / 2) - x t) % 3 ^ k)

theorem triadicGridCorner_spec (k : ℕ) (x : Vertex 2) (t : Fin 2) :
    x t ≤ triadicGridCorner k x t ∧ triadicGridCorner k x t < x t + 3 ^ k ∧
      (3 : ℤ) ^ k ∣ triadicGridCorner k x t + (3 : ℤ) ^ k / 2 := by
  have hK : (0 : ℤ) < 3 ^ k := by positivity
  have h0 := Int.emod_nonneg (-((3 : ℤ) ^ k / 2) - x t) hK.ne'
  have h1 := Int.emod_lt_of_pos (-((3 : ℤ) ^ k / 2) - x t) hK
  refine ⟨by simp only [triadicGridCorner]; linarith, by simp only [triadicGridCorner]; linarith,
    ?_⟩
  simp only [triadicGridCorner]
  rw [Int.emod_def]
  exact ⟨-((-((3 : ℤ) ^ k / 2) - x t) / 3 ^ k), by ring⟩

/-- The triadic tile of scale `k` with corner `z + 3^k i`, for `z` on the triadic grid. -/
def gridTile (k : ℕ) (z i : Vertex 2) : TriadicCube 2 :=
  ⟨k, fun t => (z t + (3 : ℤ) ^ k / 2) / 3 ^ k + i t⟩

theorem gridTile_toIntegerCube {k : ℕ} {z : Vertex 2}
    (hz : ∀ t, (3 : ℤ) ^ k ∣ z t + (3 : ℤ) ^ k / 2) (i : Vertex 2) :
    (gridTile k z i).toIntegerCube = cornerCube (z + ((3 ^ k : ℕ) : ℤ) • i) (3 ^ k) := by
  unfold gridTile TriadicCube.toIntegerCube cornerCube
  simp only [TriadicCube.side, IntegerCube.mk.injEq, and_true]
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [mul_add, Int.mul_ediv_cancel' (hz t)]
  ring

/-- A translate away from the boundary lies in the interior of the cube. -/
theorem mem_cubeInterior_of_mem_cornerCube_of_mem_trim (Q : IntegerCube 2) {N r : ℕ}
    {x y : Vertex 2} (hx : x ∈ (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1))
    (hy : y ∈ (cornerCube x N).vertices) : y ∈ cubeInterior Q := by
  obtain ⟨hxT, hxL⟩ := Finset.mem_sdiff.mp hx
  have hnot : ∀ i, ¬(x i < (trimCube Q N).corner i + ((r + 1 : ℕ) : ℤ) ∨
      (trimCube Q N).corner i + ((trimCube Q N).size : ℤ) ≤ x i + ((r + 1 : ℕ) : ℤ)) :=
    fun i h => hxL (Finset.mem_filter.mpr ⟨hxT, i, h⟩)
  have hyQ := (mem_of_mem_cornerCube_of_mem_trim Q hx hy 0).1
  refine Finset.mem_filter.2 ⟨hyQ, fun i => ?_⟩
  rw [IntegerCube.mem_vertices] at hxT hy
  simp only [trimCube, cornerCube] at hxT hy hnot
  have h1 := hxT i
  have h2 := hy i
  have h3 := hnot i
  push Not at h3
  constructor <;> omega

/-- The block of tiles after the grid corner lies in the translate. -/
theorem block_subset_cornerCube {K M N : ℕ} (hMK : (M + 1) * K ≤ N) {x z : Vertex 2}
    (hz : ∀ t, x t ≤ z t ∧ z t < x t + K) :
    (cornerCube z (M * K)).vertices ⊆ (cornerCube x N).vertices := by
  intro y hy
  rw [IntegerCube.mem_vertices] at hy ⊢
  intro t
  have h1 := hy t
  have h2 := hz t
  simp only [cornerCube] at h1 ⊢
  have h3 : ((M * K : ℕ) : ℤ) + K ≤ (N : ℤ) := by
    have : (((M + 1) * K : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMK
    push_cast at this ⊢
    linarith
  constructor <;> omega

/-- The vertices of the tiles of a translate away from the boundary. -/
theorem gridTile_vertices_subset {m n k r : ℕ} (hkn : k ≤ n) {x i : Vertex 2}
    (hx : x ∈ (trimCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (3 ^ n)).vertices \
      cubeLayer (trimCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (3 ^ n)) (r + 1))
    (hi : i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices) :
    (gridTile k (triadicGridCorner k x) i).vertices ⊆ (cornerCube x (3 ^ n)).vertices ∧
      ∀ y ∈ (gridTile k (triadicGridCorner k x) i).vertices,
        y ∈ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube := by
  have hMK : (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
  have hz : ∀ t, x t ≤ triadicGridCorner k x t ∧
      triadicGridCorner k x t < x t + ((3 ^ k : ℕ) : ℤ) := fun t => by
    have := triadicGridCorner_spec k x t
    push_cast
    exact ⟨this.1, this.2.1⟩
  have hsub : (gridTile k (triadicGridCorner k x) i).vertices ⊆ (cornerCube x (3 ^ n)).vertices := by
    intro y hy
    rw [← TriadicCube.mem_toIntegerCube_vertices,
      gridTile_toIntegerCube (fun t => (triadicGridCorner_spec k x t).2.2)] at hy
    exact block_subset_cornerCube hMK hz (tile_subset _ _ hi hy)
  exact ⟨hsub, fun y hy => mem_cubeInterior_of_mem_cornerCube_of_mem_trim _ hx (hsub hy)⟩

/-- The boundary vertices of the cluster of `□_m`. -/
noncomputable def clusterBoundary (ω : Configuration 2) (m : ℕ) : Finset (Vertex 2) :=
  (clusterVertices ω ⟨m, 0⟩).filter fun x => x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube

theorem clusterBoundary_subset (ω : Configuration 2) (m : ℕ) :
    clusterBoundary ω m ⊆ clusterVertices ω ⟨m, 0⟩ := Finset.filter_subset _ _

/-- The datum `w̃` of the homogenized problem: `u` on `C_*(□_m) ∩ ∂□_m`, the coarsened function
elsewhere. -/
noncomputable def planarDatum (hP : PlanarPartitionEvent ω) (m : ℕ)
    (hU : PlanarResolved ω ⟨m, 0⟩) (u : Vertex 2 → ℝ) : Vertex 2 → ℝ :=
  boundaryInterpolation (planarCoarseData hP ⟨m, 0⟩ hU) (clusterBoundary ω m) u

theorem planarDatum_of_mem_cubeInterior (hP : PlanarPartitionEvent ω) {m : ℕ}
    (hU : PlanarResolved ω ⟨m, 0⟩) (u : Vertex 2 → ℝ) {y : Vertex 2}
    (hy : y ∈ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) :
    planarDatum hP m hU u y = u (planarCoarseAnchor ω y) := by
  have hy' : y ∉ clusterBoundary ω m := fun h => by
    have h2 := (Finset.mem_filter.1 h).2
    exact h2 hy
  unfold planarDatum
  rw [boundaryInterpolation_of_not_mem _ _ hy']
  rfl

/-- **The `μ` test at a translate**, from the tests on its triadic tiles. -/
theorem exists_planar_mu_test (hP : PlanarPartitionEvent ω) {m n k r : ℕ} (hkn : k ≤ n)
    (hU : PlanarResolved ω ⟨m, 0⟩)
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k)
    {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩)
    (a : Fin 2 → ℝ) {x : Vertex 2}
    (hx : x ∈ (trimCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (3 ^ n)).vertices \
      cubeLayer (trimCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (3 ^ n)) (r + 1)) :
    ∃ μ : ℝ, μ ≤ (∑ y ∈ (cornerCube x (3 ^ n)).vertices, clusterEnergy ω ⟨m, 0⟩ u y) /
          ((3 ^ n : ℕ) : ℝ) ^ 2 / 2 -
        ∑ j, a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j *
          cubeEdgeSlope (3 ^ n) (planarDatum hP m hU u) x j ∧
      |(∑ j, (a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j) ^ 2 / a j) / 2 + μ| ≤
        (∑ i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices, ((3 ^ k : ℕ) : ℝ) ^ 2 *
          |(∑ j, (a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j) ^ 2 / a j) / 2 +
            planarMu ω (gridTile k (triadicGridCorner k x) i)
              (fun j => a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j)|) /
            ((3 ^ n : ℕ) : ℝ) ^ 2 +
          |1 - ((cornerCube (0 : Vertex 2) (3 ^ (n - k) - 1)).vertices.card : ℝ) *
            ((3 ^ k : ℕ) : ℝ) ^ 2 / ((3 ^ n : ℕ) : ℝ) ^ 2| *
            |(∑ j, (a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j) ^ 2 / a j) / 2| +
          |∑ j, a j * cubeSlope (3 ^ n) (planarDatum hP m hU u) x j *
            (cubeEdgeSlope (3 ^ n) (planarDatum hP m hU u) x j -
              (∑ i ∈ (cornerCube 0 (3 ^ (n - k) - 1)).vertices, ((3 ^ k : ℕ) : ℝ) ^ 2 *
                cubeEdgeSlope (3 ^ k) (planarDatum hP m hU u)
                  (triadicGridCorner k x + ((3 ^ k : ℕ) : ℤ) • i) j) /
                ((3 ^ n : ℕ) : ℝ) ^ 2)| := by
  set N := 3 ^ n
  set K := 3 ^ k
  set M := 3 ^ (n - k) - 1
  set z := triadicGridCorner k x
  set w := planarDatum hP m hU u
  set p : Fin 2 → ℝ := fun j => cubeSlope N w x j
  have hV : (0 : ℝ) < ((N : ℕ) : ℝ) ^ 2 := by positivity
  have hW : (0 : ℝ) < ((K : ℕ) : ℝ) ^ 2 := by positivity
  have hdiv : ∀ t, (3 : ℤ) ^ k ∣ z t + (3 : ℤ) ^ k / 2 := fun t => (triadicGridCorner_spec k x t).2.2
  set T : Vertex 2 → TriadicCube 2 := fun i => gridTile k z i
  have hTc : ∀ i, (T i).toIntegerCube = cornerCube (z + ((K : ℕ) : ℤ) • i) K :=
    fun i => gridTile_toIntegerCube hdiv i
  refine exists_mu_test_of_subcubes a p (fun j => cubeEdgeSlope N w x j) hV hW
    (cornerCube 0 M).vertices (fun i => planarMu ω (T i) (fun j => a j * p j))
    (fun i => ∑ y ∈ (T i).toIntegerCube.vertices, clusterEnergy ω ⟨m, 0⟩ u y)
    (fun i j => cubeEdgeSlope K w (z + ((K : ℕ) : ℤ) • i) j) ?_ ?_
  · intro i hi
    obtain ⟨hsub, hint⟩ := gridTile_vertices_subset (r := r) hkn hx hi
    have hTU : (T i).vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices := fun y hy =>
      ((TriadicCube.mem_toIntegerCube_vertices _ y).1
        (Finset.filter_subset _ _ (hint y hy)))
    have hTres : PlanarResolved ω (T i) := fun y hy => hk y (hTU hy)
    have htest := planarMu_le_test hP hTU hTres hu (fun j => a j * p j)
    have hvol : (T i).volume = ((K : ℕ) : ℝ) ^ 2 := by
      change (9 : ℝ) ^ k = ((3 ^ k : ℕ) : ℝ) ^ 2
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hvol] at htest
    have hG : ∀ j, (∑ y ∈ (T i).toIntegerCube.vertices,
        (if y + unit j ∈ (T i).toIntegerCube.vertices then
          u (planarCoarseAnchor ω (y + unit j)) - u (planarCoarseAnchor ω y) else 0)) /
          ((K : ℕ) : ℝ) ^ 2 = cubeEdgeSlope K w (z + ((K : ℕ) : ℤ) • i) j := by
      intro j
      unfold cubeEdgeSlope
      rw [← hTc i, Finset.sum_filter]
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      split_ifs with hyj
      · have hy' := (TriadicCube.mem_toIntegerCube_vertices _ y).1 hy
        have hyj' := (TriadicCube.mem_toIntegerCube_vertices _ _).1 hyj
        rw [show w (y + unit j) = _ from planarDatum_of_mem_cubeInterior hP hU u (hint _ hyj'),
          show w y = _ from planarDatum_of_mem_cubeInterior hP hU u (hint y hy')]
      · rfl
    simp only [hG] at htest
    exact htest
  · -- the energies of the tiles are at most the energy of the translate
    have hblock : ∑ i ∈ (cornerCube 0 M).vertices,
        ∑ y ∈ (T i).toIntegerCube.vertices, clusterEnergy ω ⟨m, 0⟩ u y =
        ∑ y ∈ (cornerCube z (M * K)).vertices, clusterEnergy ω ⟨m, 0⟩ u y := by
      rw [sum_cornerCube_mul (by positivity) z M]
      exact Finset.sum_congr rfl fun i _ => by rw [hTc i]
    rw [hblock]
    have hMK : (M + 1) * K ≤ N := by
      change (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
    have hz : ∀ t, x t ≤ z t ∧ z t < x t + ((K : ℕ) : ℤ) := fun t => by
      have := triadicGridCorner_spec k x t
      exact ⟨this.1, by exact_mod_cast this.2.1⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (block_subset_cornerCube hMK hz)
      fun y _ _ => clusterEnergy_nonneg _ u y

/-- **Armstrong and Dario, Lemma 6.2, in dimension two.** -/
theorem planar_lemmaSixTwo (hP : PlanarPartitionEvent ω) {m n k r : ℕ} (hkn : k ≤ n)
    (hr : 0 < r) (hU : PlanarResolved ω ⟨m, 0⟩)
    (hk : ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices, (planarPartCube ω x).scale ≤ k)
    {σ ε : ℝ} (hσ : 0 < σ) (hε0 : 0 ≤ ε)
    (hconv : ∀ T : TriadicCube 2, T.scale = k → T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
      ∀ q : Fin 2 → ℝ, |(∑ j, q j ^ 2 / σ) / 2 + planarMu ω T q| ≤ ε * ∑ j, q j ^ 2)
    {u : Vertex 2 → ℝ}
    (hu : (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩)
    {s : ℝ} (hs : 2 ≤ s) :
    innerEdgeEnergy (constCond fun _ => σ) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
        (dirichletSolution (constCond fun _ => σ)
          (cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube) (planarDatum hP m hU u)) /
        (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 ≤
      (innerEdgeEnergy (clusterCond ω ⟨m, 0⟩) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube u +
          2 * ((ε * σ ^ 2 + σ * (1 - ((((3 ^ (n - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ 2 /
              ((3 ^ n : ℕ) : ℝ) ^ 2) / 2 +
            σ * (√(1 / ((3 ^ n : ℕ) : ℝ)) +
              √(1 - ((((3 ^ (n - k) - 1) * 3 ^ k : ℕ) : ℝ)) ^ 2 / ((3 ^ n : ℕ) : ℝ) ^ 2) +
              √(1 / ((3 ^ k : ℕ) : ℝ)))) *
            ∑ y ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
              (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                (planarDatum hP m hU u (y + unit j) - planarDatum hP m hU u y) ^ 2 else 0)) +
          2 * (σ / √((3 ^ n : ℕ) : ℝ) *
            ∑ y ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
              (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                (planarDatum hP m hU u (y + unit j) - planarDatum hP m hU u y) ^ 2 else 0))) /
          (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2 +
        σ * ((2 * 2 * ((r + 1 + 3 ^ n : ℕ) : ℝ) /
            ((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ)) ^ (1 - 2 / s) *
          (((2 : ℕ) : ℝ) ^ (s / 2 - 1) *
            ((1 + (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + ((2 : ℕ) : ℝ) ^ s *
              (((3 ^ n : ℕ) : ℝ) / r) ^ s)) *
              ∑ y ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices, ∑ j : Fin 2,
                (if y + unit j ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices then
                  |planarDatum hP m hU u (y + unit j) - planarDatum hP m hU u y| ^ s else 0)) /
              (((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℝ) ^ 2) ^ (2 / s)) := by
  set Q := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube with hQ
  set w := planarDatum hP m hU u with hw
  set a : Fin 2 → ℝ := fun _ => σ with ha
  set N := 3 ^ n with hNdef
  set K := 3 ^ k with hKdef
  set M := 3 ^ (n - k) - 1 with hMdef
  set A := (trimCube Q N).vertices \ cubeLayer (trimCube Q N) (r + 1) with hA
  have hN : 0 < N := by positivity
  have hK : 0 < K := by positivity
  have hL : 0 < Q.size := by change 0 < 3 ^ m; positivity
  have hMK : (M + 1) * K ≤ N := by
    change (3 ^ (n - k) - 1 + 1) * 3 ^ k ≤ 3 ^ n
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), ← pow_add, Nat.sub_add_cancel hkn]
  have htests := fun x (hx : x ∈ A) =>
    exists_planar_mu_test (r := r) hP hkn hU hk hu a hx
  choose! μ hμ using htests
  set μT : Vertex 2 → Vertex 2 → ℝ := fun x i =>
    planarMu ω (gridTile k (triadicGridCorner k x) i) (fun j => a j * cubeSlope N w x j)
  set δ : Vertex 2 → ℝ := fun x =>
    (∑ i ∈ (cornerCube 0 M).vertices, ((K : ℕ) : ℝ) ^ 2 *
        |(∑ j, (a j * cubeSlope N w x j) ^ 2 / a j) / 2 + μT x i|) / ((N : ℕ) : ℝ) ^ 2 +
      |1 - ((cornerCube (0 : Vertex 2) M).vertices.card : ℝ) * ((K : ℕ) : ℝ) ^ 2 /
        ((N : ℕ) : ℝ) ^ 2| * |(∑ j, (a j * cubeSlope N w x j) ^ 2 / a j) / 2| +
      |∑ j, a j * cubeSlope N w x j * (cubeEdgeSlope N w x j -
        (∑ i ∈ (cornerCube 0 M).vertices, ((K : ℕ) : ℝ) ^ 2 *
          cubeEdgeSlope K w (triadicGridCorner k x + ((K : ℕ) : ℤ) • i) j) / ((N : ℕ) : ℝ) ^ 2)|
    with hδ
  have key := innerEdgeEnergy_dirichletSolution_div_le_of_mu_test (d := 2) (by norm_num) a
    (fun _ => hσ) (Λ := σ) (fun _ => le_rfl) Q hL hN hr w hs μ δ (clusterEnergy ω ⟨m, 0⟩ u)
    (clusterEnergy_nonneg _ u) (fun x hx => (hμ x hx).1) (fun x hx => (hμ x hx).2)
  have hsum := sum_subcube_errors_le a hσ.le (fun _ => hσ) (fun _ => le_rfl) hK hMK w A Q.vertices
    (fun x hx y hy => ⟨(mem_of_mem_cornerCube_of_mem_trim Q hx hy 0).1,
      fun j => (mem_of_mem_cornerCube_of_mem_trim Q hx hy j).2⟩)
    (triadicGridCorner k) (fun x _ t => by
      have := triadicGridCorner_spec k x t
      rw [hKdef]
      push_cast
      exact ⟨this.1, this.2.1⟩) μT hε0 (fun x hx i hi => by
      obtain ⟨hsub, hint⟩ := gridTile_vertices_subset (r := r) hkn hx hi
      have hTU : (gridTile k (triadicGridCorner k x) i).vertices ⊆
          (⟨m, 0⟩ : TriadicCube 2).vertices := fun y hy =>
        (TriadicCube.mem_toIntegerCube_vertices _ y).1 (Finset.filter_subset _ _ (hint y hy))
      exact hconv _ rfl hTU _)
  rw [sum_clusterEnergy_eq_innerEdgeEnergy] at key
  refine key.trans ?_
  have hV : (0 : ℝ) < ((Q.size : ℕ) : ℝ) ^ 2 := by positivity
  have hsum' : 2 * ∑ x ∈ A, δ x ≤ 2 * ((ε * σ ^ 2 + σ * (1 - (((M * K : ℕ) : ℝ)) ^ 2 /
      ((N : ℕ) : ℝ) ^ 2) / 2 + σ * (√(1 / ((N : ℕ) : ℝ)) +
        √(1 - (((M * K : ℕ) : ℝ)) ^ 2 / ((N : ℕ) : ℝ) ^ 2) + √(1 / ((K : ℕ) : ℝ)))) *
      ∑ y ∈ Q.vertices, ∑ j : Fin 2,
        (if y + unit j ∈ Q.vertices then (w (y + unit j) - w y) ^ 2 else 0)) := by
    have := hsum
    linarith
  have e2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp only [Nat.cast_ofNat] at *
  gcongr

end Rigidity.Dirichlet
