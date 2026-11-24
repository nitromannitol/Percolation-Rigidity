import Rigidity.Proofs.Cluster.GeneralRestrictDefect
import Rigidity.Proofs.Cluster.GeneralMidCells
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuEnergyDefect
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone

/-!
# The quantity of Lemma 5.5 of Armstrong and Dario on the good event, in every dimension

For a triadic cube `U`, `n ≤ scale U`, a function `u_U` on `𝒞_*(U)` and functions `u_V` on the
clusters of the subcubes `V` of scale `n`, the quantity of display (5.12) of Armstrong and Dario is

`N⁻¹ ∑_V ∑ᵢ (|V|⁻¹ (⟨eᵢ, ∇[u_U]_𝒫⟩_V - ⟨eᵢ, ∇[u_V]_𝒫⟩_V))²` (`cubeRestrictError`),

`N` the number of subcubes, the spatial sums being over the lattice edges inside `V`
(`latticeEdgePairing`, `cubeCoarsePairing`); for the minimizers of `μ` and the maximizers of `ν`
this is `cubeMuRestrictError` and `cubeNuRestrictError`. On a resolved subcube the difference of
the two spatial sums is the pairing of `eᵢ` with the coarsened gradient of
`w_V = u_U|_V - u_V` (`latticeEdgePairing_coarsen_sub_cubeCoarsePairing`).

Suppose that the partition cubes of the vertices of `U` have scale less than `j`, `1 ≤ j < n`.
Then every subcube is resolved, and if on the cells `□'` of scale `j - 1` of the inner cubes of the
subcubes (`midCubeCells`) the Meyers estimate holds for `w_V` with exponent `1 + ε/2` and constant
`C_M`, the weight `Wt ≥ size(□_𝒫)` has `(avg_{□'} Wt^{(2d-1)r})^{1/r} ≤ A`, and `size(□_𝒫) ≤ W`
on `U`, the quantity of display (5.12) is at most `2d (Λ / 3^{dn})` times the normalized energy
`|U|⁻¹ ∑_V B(w_V, w_V)/2` of the differences of Lemma 5.4, `Λ = restrictQuadConst`
(`cubeRestrictError_le_of_good`, `cubeMuRestrictError_le_of_good`,
`cubeNuRestrictError_le_of_good`). This is the deterministic part of the proof of Lemma 5.5 in the
form of the two-dimensional `Rigidity.Proofs.Cluster.restrictError_le_of_good`. The Meyers
estimate applies to `w_V` because it is harmonic at the lattice-interior points of `V`
(`sub_mem_cubeHarmonic_of_mem_subcubesAt`), where its Laplacian is the open Laplacian of its
extension (`openLaplacian_cubeExtend_eq_zero`).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **Harmonic functions on the cluster have vanishing open Laplacian** at the lattice-interior
points of the cluster all of whose open neighbours lie in the cluster. -/
theorem openLaplacian_cubeExtend_eq_zero {V : TriadicCube d} {u : CubeFun ω V}
    (hu : u ∈ cubeHarmonic ω V) {x : Vertex d} (hx : x ∈ crossingClusterVertices ω V)
    (hint : V.IsLatticeInterior x)
    (hnb : ∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω V) :
    openLaplacian ω (cubeExtend ω V u) x = 0 := by
  have h0 := mem_cubeHarmonic.1 hu ⟨x, hx⟩ hint
  rw [cubeLaplacianAt_apply] at h0
  unfold openLaplacian
  have hset : (openGraph ω).neighborFinset x =
      (crossingClusterVertices ω V).filter fun y => (openGraph ω).Adj x y := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hnb y h, h⟩, fun h => h.2⟩
  rw [hset, Finset.sum_filter, ← Finset.sum_coe_sort (crossingClusterVertices ω V)]
  refine (Finset.sum_congr rfl fun y _ => ?_).trans h0
  rw [cubeExtend_apply_of_mem u y.2, cubeExtend_apply_of_mem u hx]

/-- The difference of the restriction of a harmonic function on `U` and a harmonic function on a
resolved subcube `V` is harmonic on `V`. -/
theorem sub_mem_cubeHarmonic_of_mem_subcubesAt (hd : 0 < d) (hP : PartitionEvent ω)
    {U V : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (hV : V ∈ U.subcubesAt n)
    (hVr : PartitionResolved ω V) {uU : CubeFun ω U} (huU : uU ∈ cubeHarmonic ω U)
    {uV : CubeFun ω V} (huV : uV ∈ cubeHarmonic ω V) :
    cubeRestrictExt V uU - uV ∈ cubeHarmonic ω V :=
  sub_mem (cubeRestrictExt_mem_cubeHarmonic (TriadicCube.subset_of_mem_subcubesAt hn hV)
    (crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn
      (mem_resolvedSubcubesAt.2 ⟨hV, hVr⟩)) huU) huV

/-- **The quantity of display (5.12)** for a function `u_U` on `𝒞_*(U)` and functions `u_V` on
the clusters of the subcubes of scale `n`. -/
noncomputable def cubeRestrictError (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (uU : CubeFun ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V) : ℝ :=
  ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, ∑ i : Fin d,
    ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
      cubeCoarsePairing ω V (Pi.single i 1) (uV V)) / V.latticeVolume) ^ 2

/-- **The quantity of display (5.12) for `μ`** (Lemma 5.5 of Armstrong and Dario, first term). -/
noncomputable def cubeMuRestrictError (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (q : Fin d → ℝ) : ℝ :=
  cubeRestrictError ω U n (cubeMuMinimizer ω U q) fun V => cubeMuMinimizer ω V q

/-- The maximizer `v(·, U, p)` of `ν(U, p)` on the partition event and for a resolved cube, and
zero otherwise (as Armstrong and Dario set the solutions to zero for the cubes outside `𝒫_*`). -/
noncomputable def cubeNuSolution (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) :
    CubeFun ω U :=
  if PartitionEvent ω ∧ PartitionResolved ω U then cubeNuMaximizer ω U p else 0

theorem cubeNuSolution_eq (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p : Fin d → ℝ) :
    cubeNuSolution ω U p = cubeNuMaximizer ω U p := by
  rw [cubeNuSolution, if_pos ⟨hP, hU⟩]

/-- **The quantity of display (5.12) for `ν`** (Lemma 5.5 of Armstrong and Dario, second
term). -/
noncomputable def cubeNuRestrictError (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (p : Fin d → ℝ) : ℝ :=
  cubeRestrictError ω U n (cubeNuSolution ω U p) fun V => cubeNuSolution ω V p

/-- With `U` and its subcubes resolved, the quantity of display (5.12) for `ν` is that of the
maximizers. -/
theorem cubeNuRestrictError_eq (hP : PartitionEvent ω) {U : TriadicCube d} {n : ℕ}
    (hU : PartitionResolved ω U) (hV : ∀ V ∈ U.subcubesAt n, PartitionResolved ω V)
    (p : Fin d → ℝ) :
    cubeNuRestrictError ω U n p =
      cubeRestrictError ω U n (cubeNuMaximizer ω U p) fun V => cubeNuMaximizer ω V p := by
  unfold cubeNuRestrictError cubeRestrictError
  rw [cubeNuSolution_eq hP hU]
  congr 1
  exact Finset.sum_congr rfl fun V hVm => by
    simp only
    rw [cubeNuSolution_eq hP (hV V hVm)]

/-- On a resolved cube `V`, the spatial sum over the edges of `V` of the gradient of the
coarsening of a function on the cluster of `U`, minus the coarse pairing of a function on the
cluster of `V`, is the pairing of `eᵢ` with the gradient of the coarsening of the difference of
the restriction and the function on `V`. -/
theorem latticeEdgePairing_coarsen_sub_cubeCoarsePairing (hd : 0 < d) (hP : PartitionEvent ω)
    {U V : TriadicCube d} (hVr : PartitionResolved ω V) (uU : CubeFun ω U) (v : CubeFun ω V)
    (i : Fin d) :
    latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
      cubeCoarsePairing ω V (Pi.single i 1) v =
      latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => cubeExtend ω V (cubeRestrictExt V uU - v) (partitionAnchor ω x)) := by
  have hco : ∀ y ∈ V.toIntegerCube.vertices, cubeExtend ω U uU (partitionAnchor ω y) =
      cubeExtend ω V (cubeRestrictExt V uU) (partitionAnchor ω y) := by
    intro y hy
    have hyV := (V.mem_toIntegerCube_vertices y).1 hy
    have hmem : partitionAnchor ω y ∈ crossingClusterVertices ω V :=
      mem_crossingClusterVertices.2 (partitionAnchor_mem_crossingCluster_of_resolved hd hP hVr hyV)
    rw [cubeExtend_cubeRestrictExt V uU hmem]
  have h1 : latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
      (fun x => cubeExtend ω U uU (partitionAnchor ω x)) =
      cubeCoarsePairing ω V (Pi.single i 1) (cubeRestrictExt V uU) := by
    rw [cubeCoarsePairing_eq_latticeEdgePairing]
    unfold latticeEdgePairing
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hxk
    · dsimp only
      rw [hco x hx, hco _ hxk]
    · rfl
  rw [h1, ← map_sub, cubeCoarsePairing_eq_latticeEdgePairing]

theorem abs_single_apply_le_one (i k : Fin d) : |(Pi.single i 1 : Fin d → ℝ) k| ≤ 1 := by
  by_cases h : k = i
  · subst h
    simp
  · simp [h]

/-- **The per-subcube bound** (Armstrong and Dario, proof of Lemma 5.5, Steps 2 and 3,
deterministic part, every dimension), with the cells of scale `j - 1` of the inner cube. -/
theorem latticeEdgePairing_single_sq_le_restrictQuadConst (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j) {w : CubeFun ω V} (i : Fin d)
    {ε r CM A W : ℝ} (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex d → ℝ) (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    (hW : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (hA : ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A)
    (hM : ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2)
        (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V w)) ^ (1 + ε / 2)) :
    latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) ^ 2 ≤
      restrictQuadConst d V.scale j 1 A CM (1 + ε / 2) W * cubeForm ω V w w := by
  have hVr : PartitionResolved ω V := fun z hz => (hres z hz).le.trans hj.le
  have hcov : ∀ z ∈ partitionBoxCluster ω (innerCube V j), ∃ c ∈ midCubeCells V j,
      z ∈ cube c.1 c.2 := fun z hz => midCubeCells_cover V j (mem_partitionBoxCluster.1 hz).1
  have h := latticeEdgePairing_cubeExtend_sq_le_cubeForm hd hP hVr hj hres w
    (fun _ k => abs_single_apply_le_one i k) Wt hWt hW hpq hCM hA0 (midCubeCells V j)
    (N := 3 ^ d) hcov (fun c hc => midCubeCells_enl_subset hj1 hj hc)
    (fun x => card_midCubeCells_filter_le V j x) hA hM
  refine h.trans (le_of_eq ?_)
  rw [restrictQuadConst]

/-- **The quantity of display (5.12) on the good event** (Armstrong and Dario, Lemma 5.5,
deterministic part, every dimension `d ≥ 1`), for functions `u_U` and `u_V`. -/
theorem cubeRestrictError_le_of_good (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j) (uU : CubeFun ω U)
    (uV : ∀ V : TriadicCube d, CubeFun ω V) {ε r CM A W : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex d → ℝ) (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    (hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A)
    (hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V))) ^ (1 + ε / 2)) :
    cubeRestrictError ω U n uU uV ≤
      2 * d * (restrictQuadConst d n j 1 A CM (1 + ε / 2) W / ((3 : ℝ) ^ n) ^ d) *
        ((∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
          (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume) := by
  set Λ := restrictQuadConst d n j 1 A CM (1 + ε / 2) W with hΛ
  have hN := card_subcubesAt_mul_general U hn
  have hvolU := U.latticeVolume_pos
  have hS : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hNpos : (0 : ℝ) < (U.subcubesAt n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (U.subcubesAt n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have hterm : ∀ V ∈ U.subcubesAt n, ∑ i : Fin d,
      ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
          (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
        cubeCoarsePairing ω V (Pi.single i 1) (uV V)) / V.latticeVolume) ^ 2 ≤
      (d * Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) * cubeForm ω V (cubeRestrictExt V uU - uV V)
        (cubeRestrictExt V uU - uV V) := by
    intro V hV
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hVU : V.vertices ⊆ U.vertices := TriadicCube.subset_of_mem_subcubesAt hn hV
    have hresV : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j := fun x hx => hres x (hVU hx)
    have hVr : PartitionResolved ω V := fun z hz => (hresV z hz).le.trans (by omega)
    have hWV : ∀ z ∈ crossingClusterVertices ω V, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W :=
      fun z hz => hW z (hVU ((V.mem_toIntegerCube_vertices z).1 (Finset.filter_subset _ _ hz)))
    have hvol : V.latticeVolume = ((3 : ℝ) ^ n) ^ d := by rw [TriadicCube.latticeVolume, hVs]
    have hi : ∀ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
            (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
          cubeCoarsePairing ω V (Pi.single i 1) (uV V)) / V.latticeVolume) ^ 2 ≤
        (Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) * cubeForm ω V (cubeRestrictExt V uU - uV V)
          (cubeRestrictExt V uU - uV V) := by
      intro i
      rw [latticeEdgePairing_coarsen_sub_cubeCoarsePairing hd hP hVr uU (uV V) i, div_pow, hvol]
      have hb := latticeEdgePairing_single_sq_le_restrictQuadConst hd hP hj1
        (by omega : j < V.scale) hresV i hpq hCM hA0 Wt hWt hWV (hA V hV) (hM V hV)
      rw [hVs] at hb
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      exact hb
    calc ∑ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
            (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
          cubeCoarsePairing ω V (Pi.single i 1) (uV V)) / V.latticeVolume) ^ 2
        ≤ ∑ _i : Fin d, (Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) * cubeForm ω V
            (cubeRestrictExt V uU - uV V) (cubeRestrictExt V uU - uV V) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (d * Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) * cubeForm ω V (cubeRestrictExt V uU - uV V)
            (cubeRestrictExt V uU - uV V) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hfinal : ((U.subcubesAt n).card : ℝ)⁻¹ * ((d * Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) *
      ∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
        (cubeRestrictExt V uU - uV V)) =
      2 * d * (Λ / ((3 : ℝ) ^ n) ^ d) * ((∑ V ∈ U.subcubesAt n,
        cubeForm ω V (cubeRestrictExt V uU - uV V) (cubeRestrictExt V uU - uV V) / 2) /
          U.latticeVolume) := by
    rw [← Finset.sum_div, ← hN]
    field_simp
  unfold cubeRestrictError
  calc ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, ∑ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
            (fun x => cubeExtend ω U uU (partitionAnchor ω x)) -
          cubeCoarsePairing ω V (Pi.single i 1) (uV V)) / V.latticeVolume) ^ 2
      ≤ ((U.subcubesAt n).card : ℝ)⁻¹ * ((d * Λ / (((3 : ℝ) ^ n) ^ d) ^ 2) *
          ∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
            (cubeRestrictExt V uU - uV V)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNpos.le)
    _ = _ := hfinal

/-- If the partition cubes of the vertices of `U` have scale less than `n`, every subcube of
scale `n` is resolved. -/
theorem resolvedSubcubesAt_eq_of_lt {U : TriadicCube d} {n j : ℕ} (hjn : j < n)
    (hn : n ≤ U.scale) (hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j) :
    U.resolvedSubcubesAt ω n = U.subcubesAt n := by
  refine Finset.filter_true_of_mem fun V hV z hz => ?_
  rw [TriadicCube.scale_of_mem_subcubesAt hV]
  exact (hres z (TriadicCube.subset_of_mem_subcubesAt hn hV hz)).le.trans hjn.le

/-- **The quantity of display (5.12) for `μ` on the good event** (Armstrong and Dario,
Lemma 5.5, deterministic part, every dimension `d ≥ 1`): it is at most `2d Λ / 3^{dn}` times the
normalized energy `D_n(U, q) / |U|` of the differences of Lemma 5.4. -/
theorem cubeMuRestrictError_le_of_good (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j) (q : Fin d → ℝ) {ε r CM A W : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex d → ℝ) (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    (hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A)
    (hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
          (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q))) ^ (1 + ε / 2)) :
    cubeMuRestrictError ω U n q ≤
      2 * d * (restrictQuadConst d n j 1 A CM (1 + ε / 2) W / ((3 : ℝ) ^ n) ^ d) *
        (cubeMuDefect ω U n q / U.latticeVolume) := by
  have hU : PartitionResolved ω U := fun z hz => (hres z hz).le.trans (by omega)
  have h := cubeRestrictError_le_of_good hd hP hj1 hjn hn hres (cubeMuMinimizer ω U q)
    (fun V => cubeMuMinimizer ω V q) hpq hCM hA0 Wt hWt hW hA hM
  rw [cubeMuRestrictError, cubeMuDefect, if_pos ⟨hP, hU⟩,
    resolvedSubcubesAt_eq_of_lt hjn hn hres]
  exact h

/-- **The quantity of display (5.12) for `ν` on the good event** (Armstrong and Dario,
Lemma 5.5, second term, deterministic part, every dimension `d ≥ 1`). -/
theorem cubeNuRestrictError_le_of_good (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j) (ξ : Fin d → ℝ) {ε r CM A W : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (Wt : Vertex d → ℝ) (hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z)
    (hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ W)
    (hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ A)
    (hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
          (cubeRestrictExt V (cubeNuMaximizer ω U ξ) - cubeNuMaximizer ω V ξ)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V) (cubeExtend ω V
          (cubeRestrictExt V (cubeNuMaximizer ω U ξ) - cubeNuMaximizer ω V ξ))) ^ (1 + ε / 2)) :
    cubeNuRestrictError ω U n ξ ≤
      2 * d * (restrictQuadConst d n j 1 A CM (1 + ε / 2) W / ((3 : ℝ) ^ n) ^ d) *
        (cubeNuDefect ω U n ξ / U.latticeVolume) := by
  have hU : PartitionResolved ω U := fun z hz => (hres z hz).le.trans (by omega)
  have hVr : ∀ V ∈ U.subcubesAt n, PartitionResolved ω V := fun V hV z hz => by
    rw [TriadicCube.scale_of_mem_subcubesAt hV]
    exact (hres z (TriadicCube.subset_of_mem_subcubesAt hn hV hz)).le.trans hjn.le
  have h := cubeRestrictError_le_of_good hd hP hj1 hjn hn hres (cubeNuMaximizer ω U ξ)
    (fun V => cubeNuMaximizer ω V ξ) hpq hCM hA0 Wt hWt hW hA hM
  rw [cubeNuRestrictError_eq hP hU hVr, cubeNuDefect, resolvedSubcubesAt_eq_of_lt hjn hn hres]
  exact h

end Rigidity.Percolation
