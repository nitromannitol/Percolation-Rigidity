import Rigidity.Proofs.Cluster.GeneralRestrictBadTail
import Rigidity.Proofs.Cluster.GeneralMuSubadditiveMoments
import Rigidity.Proofs.Cluster.GeneralMinimalSet
import Rigidity.Proofs.Percolation.GeneralDim.CubeVariations
import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergyBounds

/-!
# Majorants of the quantity of Lemma 5.5 by the partition sizes, in every dimension

Off the good event of the proof of Lemma 5.5 the quantity of display (5.12) is bounded crudely.
By the Cauchy–Schwarz inequality over the edges of a subcube `V`,
`⟨∇f, eᵢ⟩_V² ≤ 2d |V| ∑_V |∇f|²` (`latticeEdgePairing_single_sq_le`), and the energies on the
subcubes are at most the energy on `U`; hence the quantity is at most
`4d² |U|⁻¹ (∑_U |∇[u_U]_𝒫|² + ∑_V ∑_V |∇[u_V]_𝒫|²)` (`cubeRestrictError_le_energy`). By Lemma 3.3,
the energy of the coarsening of a function `w` on a resolved cube is at most
`K² S(U) B(w, w)`, `S(U) = ∑_{x ∈ U} size(x)^{2d-1}` (`sum_gradNormIn_coarse_sq_le_sizeSum`). For
the
minimizers of `μ`, `B(u, u) = -2|U| μ(U, q) ≤ 2 |U| Λ(U) |q|²` with `|U| Λ(U) ≤ d² K² S(U)`
(Lemma 4.4), and for the maximizers of `ν`, `B(v, v) = 2|U| ν(U, ξ) ≤ (3^d/2) |U| |ξ|₁²`. Hence

`cubeMuRestrictError ≤ 16 d⁴ K⁴ |q|² S(U)² / |U|`, `cubeNuRestrictError ≤ 4 d² 3^d K² |ξ|₁² S(U)`

(`cubeMuRestrictError_le_sizeSum`, `cubeNuRestrictError_le_sizeSum`), majorants which are
measurable functions of the configuration with all moments. This is the general-dimensional form of
`Rigidity.Proofs.Cluster.restrictError_le_energy` and of the majorants of
`Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant`, with the partition sizes in place
of the planar reach.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **Cauchy–Schwarz for the pairing with a unit vector**: `⟨∇f, eᵢ⟩_D² ≤ 2d |D| ∑_D |∇f|²_D`. -/
theorem latticeEdgePairing_single_sq_le (D : Finset (Vertex d)) (i : Fin d) (f : Vertex d → ℝ) :
    latticeEdgePairing D (fun _ => Pi.single i 1) f ^ 2 ≤
      2 * d * D.card * ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ 2 := by
  have h1 := latticeEdgePairing_sq_le D (fun _ => Pi.single i 1) f
  have h2 := sum_latticeEdge_sq_le D (g := fun _ => Pi.single i 1) (G := 1)
    (fun _ k => abs_single_apply_le_one i k)
  have h3 := latticeEdgeEnergy_le_two_mul_sum_gradNormIn_sq D f
  have h0 := latticeEdgeEnergy_nonneg D f
  calc latticeEdgePairing D (fun _ => Pi.single i 1) f ^ 2
      ≤ (∑ x ∈ D, ∑ k : Fin d, if x + LatticeProb.unit k ∈ D then
          (fun _ => (Pi.single i 1 : Fin d → ℝ)) x k ^ 2 else 0) * latticeEdgeEnergy D f := h1
    _ ≤ (d * 1 ^ 2 * D.card) * (2 * ∑ x ∈ D, gradNormIn (nearestNeighborGraph d) D f x ^ 2) :=
        mul_le_mul h2 h3 h0 (by positivity)
    _ = _ := by ring

/-- The square of the magnitude of the gradient increases with the domain. -/
theorem gradNormIn_sq_le_of_subset (G : SimpleGraph (Vertex d)) {S T : Finset (Vertex d)}
    (hST : S ⊆ T) (f : Vertex d → ℝ) (x : Vertex d) :
    gradNormIn G S f x ^ 2 ≤ gradNormIn G T f x ^ 2 := by
  unfold gradNormIn
  rw [Real.sq_sqrt (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun y _ => ite_nonneg (sq_nonneg _) le_rfl)),
    Real.sq_sqrt (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun y _ => ite_nonneg (sq_nonneg _) le_rfl))]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hST
    fun y _ _ => ite_nonneg (sq_nonneg _) le_rfl) (by norm_num)

/-- The energies on the subcubes are at most the energy on the cube. -/
theorem sum_subcubesAt_sum_gradNormIn_sq_le {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (f : Vertex d → ℝ) :
    ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices f x ^ 2 ≤
      ∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices f x ^ 2 := by
  rw [← sum_triadicCubeAt_eq hn (fun V x =>
    gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices f x ^ 2)]
  refine Finset.sum_le_sum fun x hx => gradNormIn_sq_le_of_subset _ (fun y hy => ?_) f x
  rw [TriadicCube.mem_toIntegerCube_vertices] at hy ⊢
  exact triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x).1 hx) hy

/-- **The differences of the pairings with the unit vectors by the energies**, for functions
`f_U` and `f_V` on the vertices. -/
theorem sum_sq_latticeEdgePairing_sub_le_energy {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (fU : Vertex d → ℝ) (fV : TriadicCube d → Vertex d → ℝ) :
    ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, ∑ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) fU -
          latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V)) /
            V.latticeVolume) ^ 2 ≤
      4 * d ^ 2 / U.latticeVolume * (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices fU x ^ 2 +
        ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2) := by
  have hN := card_subcubesAt_mul_general U hn
  have hvolU := U.latticeVolume_pos
  have hNpos : (0 : ℝ) < (U.subcubesAt n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (U.subcubesAt n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ n) ^ d := by positivity
  have hterm : ∀ V ∈ U.subcubesAt n, ∑ i : Fin d,
      ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) fU -
        latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V)) /
          V.latticeVolume) ^ 2 ≤
      4 * d ^ 2 / ((3 : ℝ) ^ n) ^ d * (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices fU x ^ 2 +
        ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2) := by
    intro V hV
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hvol : V.latticeVolume = ((3 : ℝ) ^ n) ^ d := by rw [TriadicCube.latticeVolume, hVs]
    have hcard : (V.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ n) ^ d := by
      rw [V.card_toIntegerCube_vertices, hvol]
    set a := ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices fU x ^ 2 with ha
    set b := ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2 with hb
    have hpt : ∀ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) fU -
          latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V)) /
            V.latticeVolume) ^ 2 ≤ 4 * d / ((3 : ℝ) ^ n) ^ d * (a + b) := by
      intro i
      have h1 := latticeEdgePairing_single_sq_le V.toIntegerCube.vertices i fU
      have h2 := latticeEdgePairing_single_sq_le V.toIntegerCube.vertices i (fV V)
      rw [hcard, ← ha] at h1
      rw [hcard, ← hb] at h2
      rw [div_pow, hvol, div_le_iff₀ (by positivity)]
      have e : 4 * d / ((3 : ℝ) ^ n) ^ d * (a + b) * (((3 : ℝ) ^ n) ^ d) ^ 2 =
          2 * (2 * d * ((3 : ℝ) ^ n) ^ d * a) + 2 * (2 * d * ((3 : ℝ) ^ n) ^ d * b) := by
        field_simp
        ring
      rw [e]
      nlinarith [sq_nonneg (latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1)
        fU + latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V))]
    calc ∑ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) fU -
          latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V)) /
            V.latticeVolume) ^ 2
        ≤ ∑ _i : Fin d, 4 * d / ((3 : ℝ) ^ n) ^ d * (a + b) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = 4 * d ^ 2 / ((3 : ℝ) ^ n) ^ d * (a + b) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hU := sum_subcubesAt_sum_gradNormIn_sq_le hn fU
  set A := ∑ x ∈ U.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices fU x ^ 2 with hA
  set A' := ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices fU x ^ 2 with hA'
  set B := ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices (fV V) x ^ 2 with hB
  have hstep : ((U.subcubesAt n).card : ℝ)⁻¹ * ∑ V ∈ U.subcubesAt n, ∑ i : Fin d,
        ((latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) fU -
          latticeEdgePairing V.toIntegerCube.vertices (fun _ => Pi.single i 1) (fV V)) /
            V.latticeVolume) ^ 2 ≤
      ((U.subcubesAt n).card : ℝ)⁻¹ * (4 * d ^ 2 / ((3 : ℝ) ^ n) ^ d * (A + B)) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (inv_nonneg.2 hNpos.le)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  refine hstep.trans (le_of_eq ?_)
  rw [← hN]
  field_simp

/-- **The quantity of display (5.12) by the energies of the coarsenings.** -/
theorem cubeRestrictError_le_energy {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale)
    (uU : CubeFun ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V) :
    cubeRestrictError ω U n uU uV ≤ 4 * d ^ 2 / U.latticeVolume *
      (∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
          U.toIntegerCube.vertices (fun x => cubeExtend ω U uU (partitionAnchor ω x)) x ^ 2 +
        ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d)
          V.toIntegerCube.vertices (fun x => cubeExtend ω V (uV V) (partitionAnchor ω x)) x ^ 2) :=
    by
  unfold cubeRestrictError
  simp only [cubeCoarsePairing_eq_latticeEdgePairing]
  exact sum_sq_latticeEdgePairing_sub_le_energy hn _ (fun V x => cubeExtend ω V (uV V)
    (partitionAnchor ω x))

/-- **The energy of the coarsening by the partition sizes** (Lemma 3.3 with `s = 2`): on a resolved
cube, `∑_U |∇[w]_𝒫|² ≤ K² S(U) B(w, w)`, `S(U) = ∑_{x ∈ U} size(x)^{2d-1}`. -/
theorem sum_gradNormIn_coarse_sq_le_sizeSum (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (w : CubeFun ω U) :
    ∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun x => cubeExtend ω U w (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 *
        (partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) * cubeForm ω U w w) := by
  have h := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hU (cubeExtend ω U w) (s := 2)
    (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  set C := crossingClusterVertices ω U with hC
  have hB := sum_clusterGradSq_eq_cubeForm U w
  have hle : ∀ z ∈ C, clusterGradSq ω C (cubeExtend ω U w) z ≤ cubeForm ω U w w := fun z hz => by
    rw [← hB]
    exact Finset.single_le_sum (f := fun z => clusterGradSq ω C (cubeExtend ω U w) z)
      (fun z _ => clusterGradSq_nonneg _ _ _ _) hz
  have hB0 : 0 ≤ cubeForm ω U w w := cubeForm_self_nonneg w
  calc ∑ z ∈ C, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * (d : ℝ) - 1) *
        gradNormIn (openGraph ω) C (cubeExtend ω U w) z ^ 2
      = ∑ z ∈ C, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) *
          clusterGradSq ω C (cubeExtend ω U w) z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _),
          stoppingSize_goodCubes_eq hP z,
          show (2 : ℝ) * (d : ℝ) - 1 = ((2 * d - 1 : ℕ) : ℝ) by
            rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num, Real.rpow_natCast]
    _ ≤ ∑ z ∈ C, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) *
          cubeForm ω U w w :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hle z hz)
          (pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _)
    _ = (∑ z ∈ C, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1)) *
          cubeForm ω U w w := by rw [Finset.sum_mul]
    _ ≤ partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) * cubeForm ω U w w := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun z _ _ => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _

theorem partitionSizeSum_nonneg (S : Finset (Vertex d)) (k : ℕ) :
    0 ≤ partitionSizeSum ω S k :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _

/-- The sizes of the partition cubes are at least one, so `size^{2d-2} ≤ size^{2d-1}`. -/
theorem partitionSizeSum_le_succ (hP : PartitionEvent ω) (S : Finset (Vertex d)) (hd : 0 < d) :
    partitionSizeSum ω S (2 * (d - 1)) ≤ partitionSizeSum ω S (2 * d - 1) := by
  refine Finset.sum_le_sum fun z _ => ?_
  rw [stoppingSize_goodCubes_eq hP z]
  exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)

/-- The sums of the sizes over the subcubes add up to the sum over the cube. -/
theorem sum_subcubesAt_partitionSizeSum {U : TriadicCube d} {n : ℕ} (hn : n ≤ U.scale) (k : ℕ) :
    ∑ V ∈ U.subcubesAt n, partitionSizeSum ω V.toIntegerCube.vertices k =
      partitionSizeSum ω U.toIntegerCube.vertices k := by
  unfold partitionSizeSum
  rw [← sum_triadicCubeAt_eq hn
    (fun _ x => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ k)]

/-- The energy of the coarsened minimizer of `μ`: `∑_U |∇[u]_𝒫|² ≤ 2 d² K⁴ |q|² S(U)²`. -/
theorem sum_gradNormIn_coarse_cubeMuMinimizer_le (hd : 0 < d) (hP : PartitionEvent ω)
    (U : TriadicCube d) (q : Fin d → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun x => cubeExtend ω U (cubeMuMinimizer ω U q) (partitionAnchor ω x)) x ^ 2 ≤
      2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 * (∑ i, q i ^ 2) *
        partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 := by
  have hS0 := partitionSizeSum_nonneg (ω := ω) U.toIntegerCube.vertices (2 * d - 1)
  have hR0 : 0 ≤ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 *
      (∑ i, q i ^ 2) * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (q i)
    positivity
  by_cases hU : PartitionResolved ω U
  · obtain ⟨hu, hvar⟩ := cubeMuMinimizer_spec hd hP hU q
    have hμ := cubeMu_eq_of_forall_cubeForm_eq hd hP hU hu hvar
    have hneg := neg_cubeMu_le_cubeMuBound_mul hd hP hU q
    have hvol := U.latticeVolume_pos
    have hB : cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q) ≤
        2 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
          partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) := by
      have hΛ : cubeMuBound ω U * U.latticeVolume ≤
          d * d * coarseGradConstant d ^ 2 *
            partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) := by
        rw [cubeMuBound, div_mul_cancel₀ _ hvol.ne']
        exact mul_le_mul_of_nonneg_left (partitionSizeSum_le_succ hP _ hd) (by positivity)
      rw [hμ] at hneg
      have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (q i)
      have h1 : cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q) ≤
          2 * (cubeMuBound ω U * U.latticeVolume) * ∑ i, q i ^ 2 := by
        rw [neg_div, neg_neg, div_le_iff₀ hvol] at hneg
        nlinarith
      calc cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q)
          ≤ 2 * (cubeMuBound ω U * U.latticeVolume) * ∑ i, q i ^ 2 := h1
        _ ≤ 2 * (d * d * coarseGradConstant d ^ 2 *
            partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1)) * ∑ i, q i ^ 2 := by gcongr
        _ = _ := by ring
    refine (sum_gradNormIn_coarse_sq_le_sizeSum hd hP hU _).trans ?_
    calc coarseGradConstant d ^ 2 * (partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) *
          cubeForm ω U (cubeMuMinimizer ω U q) (cubeMuMinimizer ω U q))
        ≤ coarseGradConstant d ^ 2 * (partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) *
          (2 * (d * d * coarseGradConstant d ^ 2) * (∑ i, q i ^ 2) *
            partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1))) := by gcongr
      _ = _ := by ring
  · have h0 : cubeMuMinimizer ω U q = 0 := by
      rw [cubeMuMinimizer, dif_neg fun h => hU h.2.2]
    rw [h0]
    simp only [map_zero, Pi.zero_apply]
    have hz : ∀ x, gradNormIn (nearestNeighborGraph d) U.toIntegerCube.vertices
        (fun _ => (0 : ℝ)) x ^ 2 = 0 := fun x => by simp [gradNormIn]
    simp only [hz, Finset.sum_const_zero]
    exact hR0

/-- **A majorant of the quantity of display (5.12) for `μ` by the partition sizes**:
`cubeMuRestrictError ≤ 16 d² K⁴ |q|² S(U)² / |U|`. -/
theorem cubeMuRestrictError_le_sizeSum (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ) :
    cubeMuRestrictError ω U n q ≤
      16 * d ^ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 *
        (∑ i, q i ^ 2) * partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) ^ 2 /
          U.latticeVolume := by
  set c := 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 * (∑ i, q i ^ 2)
    with hc
  have hc0 : 0 ≤ c := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (q i)
    positivity
  set S := partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) with hS
  have h := cubeRestrictError_le_energy (ω := ω) hn (cubeMuMinimizer ω U q)
    (fun V => cubeMuMinimizer ω V q)
  have hU := sum_gradNormIn_coarse_cubeMuMinimizer_le hd hP U q
  have hV : ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2 ≤
      c * S ^ 2 := by
    calc ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeMuMinimizer ω V q) (partitionAnchor ω x)) x ^ 2
        ≤ ∑ V ∈ U.subcubesAt n, c * partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) ^ 2 :=
          Finset.sum_le_sum fun V _ => sum_gradNormIn_coarse_cubeMuMinimizer_le hd hP V q
      _ ≤ ∑ V ∈ U.subcubesAt n,
            c * (partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) * S) := by
          refine Finset.sum_le_sum fun V hVm => mul_le_mul_of_nonneg_left ?_ hc0
          rw [sq]
          refine mul_le_mul_of_nonneg_left ?_ (partitionSizeSum_nonneg _ _)
          rw [hS, ← sum_subcubesAt_partitionSizeSum hn]
          exact Finset.single_le_sum (f := fun V => partitionSizeSum ω V.toIntegerCube.vertices
            (2 * d - 1)) (fun V _ => partitionSizeSum_nonneg _ _) hVm
      _ = c * S ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, sum_subcubesAt_partitionSizeSum hn, ← hS]
          ring
  have hvol := U.latticeVolume_pos
  refine h.trans ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hvol]
  have e : 16 * (d : ℝ) ^ 2 * (d * d * coarseGradConstant d ^ 2) * coarseGradConstant d ^ 2 *
      (∑ i, q i ^ 2) * S ^ 2 = 4 * d ^ 2 * (c * S ^ 2 + c * S ^ 2) := by
    rw [hc]
    ring
  rw [e]
  gcongr

/-- **A majorant of the quantity of display (5.12) for `ν` by the partition sizes**:
`cubeNuRestrictError ≤ 4 d² 3^d K² |ξ|₁² S(U)`. -/
theorem cubeNuRestrictError_le_sizeSum (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n : ℕ} (hn : n ≤ U.scale) (ξ : Fin d → ℝ) :
    cubeNuRestrictError ω U n ξ ≤
      4 * d ^ 2 * 3 ^ d * coarseGradConstant d ^ 2 * (∑ i, |ξ i|) ^ 2 *
        partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) := by
  set a : ℝ := 3 ^ d / 4 * (∑ i, |ξ i|) ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hsol : ∀ V : TriadicCube d, ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 * (partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) *
        (2 * V.latticeVolume * a)) := by
    intro V
    by_cases hV : PartitionResolved ω V
    · rw [cubeNuSolution_eq hP hV]
      refine (sum_gradNormIn_coarse_sq_le_sizeSum hd hP hV _).trans ?_
      obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) V ξ
      have hν := cubeNu_mul_latticeVolume_eq ξ hv hvar
      have hle := cubeNu_le (ω := ω) (U := V) ξ
      have hB : cubeForm ω V (cubeNuMaximizer ω V ξ) (cubeNuMaximizer ω V ξ) ≤
          2 * V.latticeVolume * a := by
        have := mul_le_mul_of_nonneg_right hle V.latticeVolume_pos.le
        rw [ha]
        nlinarith
      gcongr
      exact partitionSizeSum_nonneg _ _
    · have h0 : cubeNuSolution ω V ξ = 0 := by
        rw [cubeNuSolution, if_neg fun h => hV h.2]
      rw [h0]
      simp only [map_zero, Pi.zero_apply]
      have hz : ∀ x, gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
          (fun _ => (0 : ℝ)) x ^ 2 = 0 := fun x => by simp [gradNormIn]
      simp only [hz, Finset.sum_const_zero]
      have := V.latticeVolume_pos
      have := partitionSizeSum_nonneg (ω := ω) V.toIntegerCube.vertices (2 * d - 1)
      positivity
  set S := partitionSizeSum ω U.toIntegerCube.vertices (2 * d - 1) with hS
  have h := cubeRestrictError_le_energy (ω := ω) hn (cubeNuSolution ω U ξ)
    (fun V => cubeNuSolution ω V ξ)
  have hvol := U.latticeVolume_pos
  have hV : ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 * (S * (2 * U.latticeVolume * a)) := by
    calc ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2
        ≤ ∑ V ∈ U.subcubesAt n, coarseGradConstant d ^ 2 *
            (partitionSizeSum ω V.toIntegerCube.vertices (2 * d - 1) *
              (2 * U.latticeVolume * a)) := by
          refine Finset.sum_le_sum fun V hVm => (hsol V).trans ?_
          have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hVm
          have hle : V.latticeVolume ≤ U.latticeVolume := by
            rw [TriadicCube.latticeVolume, TriadicCube.latticeVolume, hVs]
            exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hn) d
          gcongr
          exact partitionSizeSum_nonneg _ _
      _ = coarseGradConstant d ^ 2 * (S * (2 * U.latticeVolume * a)) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul, sum_subcubesAt_partitionSizeSum hn, ← hS]
  refine h.trans ?_
  have hU := hsol U
  rw [← hS] at hU
  have e : 4 * (d : ℝ) ^ 2 * 3 ^ d * coarseGradConstant d ^ 2 * (∑ i, |ξ i|) ^ 2 * S =
      4 * d ^ 2 / U.latticeVolume * (coarseGradConstant d ^ 2 * (S * (2 * U.latticeVolume * a)) +
        coarseGradConstant d ^ 2 * (S * (2 * U.latticeVolume * a))) := by
    rw [ha]
    field_simp
    ring
  rw [e]
  have hc0' : (0 : ℝ) ≤ 4 * d ^ 2 / U.latticeVolume := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add hU hV) hc0'

end Rigidity.Percolation
