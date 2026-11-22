import Rigidity.Proofs.Percolation.PlanarMuGeneral
import Rigidity.Proofs.Percolation.PlanarFlatnessInputs

/-!
# Measurability of the quantities of Lemma 5.5 of Armstrong and Dario

The quantity of display (5.12) is built from the spatial sums `⟨∇[u(·, U, q)]_𝒫⟩_V · e_i` of the
coarsened gradient of a minimizer over a subcube `V ⊆ U` and from the coarse pairings
`⟨∇[u(·, V, q)]_𝒫⟩_V · e_i`. The first is the field pairing `ℓ_g u(·, U, q)` with the field
`g = e_i 1{edges inside V}` (`cubeGradSum_coarsen_eq_fieldPairing`), and by polarization
(`fieldPairing_eq_planarMuGen`) every such pairing of a minimizer of `μ` or a maximizer of `ν` is
`-|U|` times a combination of three minima `μ_{g,p}(U)` on the partition event and for a resolved
cube (and zero otherwise). These minima do not depend on the choice of the minimizer and are
measurable (`measurable_planarMuGen_indicator`). Hence `planarMuRestrictError` and
`planarNuRestrictError` are measurable functions of the configuration
(`measurable_planarMuRestrictError`, `measurable_planarNuRestrictError`), which is the
measurability part of the inputs `PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The field equal to `e_i` on the lattice edges `(x, x + e_i)` inside `V` and to zero
elsewhere. -/
noncomputable def subcubeField (V : TriadicCube 2) (i : Fin 2) : Vertex 2 → Fin 2 → ℝ :=
  fun x i' => if i' = i ∧ x ∈ V.toIntegerCube.vertices ∧
    x + unitVertex i ∈ V.toIntegerCube.vertices then 1 else 0

theorem fieldPairing_zero {U : TriadicCube 2} (u : ClusterFun ω U) : fieldPairing ω U 0 u = 0 := by
  rw [fieldPairing_apply]
  simp

/-- The spatial sum over the edges of a subcube `V ⊆ U` of the gradient of the coarsening of a
function on the cluster of `U` is its field pairing with `e_i 1{edges inside V}`. -/
theorem cubeGradSum_coarsen_eq_fieldPairing {U V : TriadicCube 2}
    (hVU : V.toIntegerCube.vertices ⊆ U.toIntegerCube.vertices) (w : ClusterFun ω U) (i : Fin 2) :
    cubeGradSum V (coarsen ω U w) i = fieldPairing ω U (subcubeField V i) w := by
  have hu : Rigidity.Proofs.Multiscale.unitVec i = unitVertex i := rfl
  simp only [cubeGradSum, Rigidity.Proofs.Multiscale.gradSum]
  rw [fieldPairing_apply]
  symm
  have hterm : ∀ x ∈ U.toIntegerCube.vertices, (∑ i' : Fin 2,
      if x + unitVertex i' ∈ U.toIntegerCube.vertices then
        subcubeField V i x i' * (clusterExtend ω U w (planarCoarseAnchor ω (x + unitVertex i')) -
          clusterExtend ω U w (planarCoarseAnchor ω x)) else 0) =
      if x ∈ V.toIntegerCube.vertices then
        (if x + Rigidity.Proofs.Multiscale.unitVec i ∈ V.toIntegerCube.vertices then
          coarsen ω U w (x + Rigidity.Proofs.Multiscale.unitVec i) - coarsen ω U w x else 0)
      else 0 := by
    intro x _
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [subcubeField, hi']) (by simp)]
    simp only [subcubeField, true_and, hu, coarsen]
    by_cases hxV : x ∈ V.toIntegerCube.vertices
    · by_cases hxi : x + unitVertex i ∈ V.toIntegerCube.vertices
      · rw [if_pos (hVU hxi), if_pos ⟨hxV, hxi⟩, if_pos hxV, if_pos hxi, one_mul]
      · simp [hxV, hxi]
    · simp [hxV]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.inter_eq_right.2 hVU]

/-- The lattice points of a subcube lie in those of the cube. -/
theorem toIntegerCube_vertices_subset_of_mem_subcubesAt {U V : TriadicCube 2} {n : ℕ}
    (hn : n ≤ U.scale) (hV : V ∈ subcubesAt U n) :
    V.toIntegerCube.vertices ⊆ U.toIntegerCube.vertices := fun x hx =>
  (U.mem_toIntegerCube_vertices x).2
    (subset_of_mem_subcubesAt hn hV ((V.mem_toIntegerCube_vertices x).1 hx))

theorem cubeGradSum_zero (V : TriadicCube 2) (i : Fin 2) : cubeGradSum V 0 i = 0 := by
  simp [cubeGradSum, Rigidity.Proofs.Multiscale.gradSum]

theorem coarsen_zero (U : TriadicCube 2) : coarsen ω U 0 = 0 := by
  funext x
  simp [coarsen]

/-- The pairing of a minimizer of `μ(U, q)` with a field, by polarization. -/
theorem fieldPairing_planarMuMinimizer_eq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) (g : Vertex 2 → Fin 2 → ℝ) :
    fieldPairing ω U g (planarMuMinimizer ω U q) = -U.volume *
      (planarMuGen ω U (g + fun _ => q) 0 - planarMuGen ω U g 0 -
        planarMuGen ω U (fun _ => q) 0) :=
  fieldPairing_eq_planarMuGen hP hU (planarMuMinimizer_spec hP hU q).1 (fun w hw => by
    rw [(planarMuMinimizer_spec hP hU q).2 w hw, fieldPairing_const, fluxPairing_zero,
      add_zero]) g

/-- The pairing of a maximizer of `ν(U, p)` with a field, by polarization. -/
theorem fieldPairing_planarNuMaximizer_eq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) (g : Vertex 2 → Fin 2 → ℝ) :
    fieldPairing ω U g (planarNuMaximizer ω U p) = -U.volume *
      (planarMuGen ω U (g + 0) p - planarMuGen ω U g 0 - planarMuGen ω U 0 p) :=
  fieldPairing_eq_planarMuGen hP hU (planarNuMaximizer_spec U p).1 (fun w hw => by
    rw [(planarNuMaximizer_spec U p).2 w hw, fieldPairing_zero, zero_add]) g

/-- The indicator `1{partition event, U resolved} μ_{g,p}(U)`. -/
noncomputable def planarMuGenInd (ω : Configuration 2) (U : TriadicCube 2)
    (g : Vertex 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) : ℝ :=
  if PlanarPartitionEvent ω ∧ PlanarResolved ω U then planarMuGen ω U g p else 0

theorem measurable_planarMuGenInd (U : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (p : Fin 2 → ℝ) : Measurable fun ω => planarMuGenInd ω U g p :=
  measurable_planarMuGen_indicator U g p

/-- The pairing of the minimizer of `μ(U, q)` (zero off the partition event and for an unresolved
cube) with a field is a combination of the indicators of three minima. -/
theorem fieldPairing_planarMuMinimizer_eq_ind (U : TriadicCube 2) (q : Fin 2 → ℝ)
    (g : Vertex 2 → Fin 2 → ℝ) :
    fieldPairing ω U g (planarMuMinimizer ω U q) = -U.volume *
      (planarMuGenInd ω U (g + fun _ => q) 0 - planarMuGenInd ω U g 0 -
        planarMuGenInd ω U (fun _ => q) 0) := by
  unfold planarMuGenInd
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
  · rw [if_pos h, if_pos h, if_pos h]
    exact fieldPairing_planarMuMinimizer_eq h.1 h.2 q g
  · rw [if_neg h, if_neg h, if_neg h]
    have h0 : planarMuMinimizer ω U q = 0 := by rw [planarMuMinimizer, dif_neg h]
    rw [h0, map_zero]
    ring

/-- The pairing of the maximizer of `ν(U, p)` (zero off the partition event and for an unresolved
cube) with a field is a combination of the indicators of three minima. -/
theorem fieldPairing_planarNuSolution_eq_ind (U : TriadicCube 2) (p : Fin 2 → ℝ)
    (g : Vertex 2 → Fin 2 → ℝ) :
    fieldPairing ω U g (planarNuSolution ω U p) = -U.volume *
      (planarMuGenInd ω U (g + 0) p - planarMuGenInd ω U g 0 - planarMuGenInd ω U 0 p) := by
  unfold planarMuGenInd planarNuSolution
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
  · rw [if_pos h, if_pos h, if_pos h, if_pos h]
    exact fieldPairing_planarNuMaximizer_eq h.1 h.2 p g
  · rw [if_neg h, if_neg h, if_neg h, if_neg h, map_zero]
    ring

theorem measurable_fieldPairing_planarMuMinimizer (U : TriadicCube 2) (q : Fin 2 → ℝ)
    (g : Vertex 2 → Fin 2 → ℝ) :
    Measurable fun ω => fieldPairing ω U g (planarMuMinimizer ω U q) := by
  simp only [fieldPairing_planarMuMinimizer_eq_ind]
  exact measurable_const.mul (((measurable_planarMuGenInd U _ 0).sub
    (measurable_planarMuGenInd U g 0)).sub (measurable_planarMuGenInd U _ 0))

theorem measurable_fieldPairing_planarNuSolution (U : TriadicCube 2) (p : Fin 2 → ℝ)
    (g : Vertex 2 → Fin 2 → ℝ) :
    Measurable fun ω => fieldPairing ω U g (planarNuSolution ω U p) := by
  simp only [fieldPairing_planarNuSolution_eq_ind]
  exact measurable_const.mul (((measurable_planarMuGenInd U _ p).sub
    (measurable_planarMuGenInd U g 0)).sub (measurable_planarMuGenInd U 0 p))

/-- **Measurability of the quantity of display (5.12) for `μ`.** -/
theorem measurable_planarMuRestrictError (U : TriadicCube 2) {n : ℕ} (hn : n ≤ U.scale)
    (q : Fin 2 → ℝ) : Measurable fun ω => planarMuRestrictError ω U n q := by
  unfold planarMuRestrictError
  refine measurable_const.mul (Finset.measurable_sum _ fun V hV => Finset.measurable_sum _
    fun j _ => ((Measurable.sub ?_ ?_).div_const _).pow_const 2)
  · simp only [cubeGradSum_coarsen_eq_fieldPairing
      (toIntegerCube_vertices_subset_of_mem_subcubesAt hn hV)]
    exact measurable_fieldPairing_planarMuMinimizer U q _
  · simp only [← fieldPairing_const]
    exact measurable_fieldPairing_planarMuMinimizer V q _

/-- **Measurability of the quantity of display (5.12) for `ν`.** -/
theorem measurable_planarNuRestrictError (U : TriadicCube 2) {n : ℕ} (hn : n ≤ U.scale)
    (ξ : Fin 2 → ℝ) : Measurable fun ω => planarNuRestrictError ω U n ξ := by
  unfold planarNuRestrictError
  refine measurable_const.mul (Finset.measurable_sum _ fun V hV => Finset.measurable_sum _
    fun j _ => ((Measurable.sub ?_ ?_).div_const _).pow_const 2)
  · simp only [cubeGradSum_coarsen_eq_fieldPairing
      (toIntegerCube_vertices_subset_of_mem_subcubesAt hn hV)]
    exact measurable_fieldPairing_planarNuSolution U ξ _
  · simp only [← fieldPairing_const]
    exact measurable_fieldPairing_planarNuSolution V ξ _

end Rigidity.Percolation
