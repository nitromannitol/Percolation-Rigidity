import Rigidity.Proofs.Cluster.PlanarRestrictErrorGood
import Rigidity.Proofs.Cluster.PlanarCoarseEnergyMoments
import Rigidity.Proofs.Percolation.PlanarOmegaPointwise

/-!
# A measurable majorant of the quantity of Lemma 5.5 with a second moment

Off the good event of the proof of Lemma 5.5 of Armstrong and Dario, the quantity of display
(5.12) is bounded crudely by the energies of the coarsened functions. By the Cauchy–Schwarz
inequality over the edges of a subcube `V`, `|⟨∇f⟩_V · e_i|² ≤ |V| ∑_{edges of V} |∇f|²`, and the
edges of the subcubes are edges of `U`; hence the quantity is at most
`4 |U|⁻¹ (∑_{x ∈ U} |∇[u_U]_𝒫|² + ∑_V ∑_{x ∈ V} |∇[u_V]_𝒫|²)` (`restrictError_le_energy`). For the
minimizers of `μ` and the maximizers of `ν` each energy is at most
`K |q|₁² |W| (∑_{z ∈ W} R(z)^{21})^{1/3}` pointwise, `R` the reach of the planar partition
(`ofReal_energy_planarMuMinimizer_le`, `ofReal_energy_planarNuSolution_le`; as in (4.24), (4.25)).
This gives the measurable majorant `M = 8 K |q|₁² (∑_{z ∈ U} R(z)^{21})^{1/3}` of the quantity,
with `E[M²] ≤ C |q|₁⁴ |U|^{2/3}` by Jensen's inequality
(`exists_planarMuRestrictError_majorant`, `exists_planarNuRestrictError_majorant`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- **Cauchy–Schwarz over the edges of a cube.** -/
theorem sq_cubeGradSum_le (V : TriadicCube 2) (f : Vertex 2 → ℝ) (i : Fin 2) :
    cubeGradSum V f i ^ 2 ≤ (V.toIntegerCube.vertices.card : ℝ) *
      ∑ x ∈ V.toIntegerCube.vertices, (if x + unitVertex i ∈ V.toIntegerCube.vertices then
        (f (x + unitVertex i) - f x) ^ 2 else 0) := by
  have h := sq_sum_le_card_mul_sum_sq (s := V.toIntegerCube.vertices)
    (f := fun x => if x + unitVertex i ∈ V.toIntegerCube.vertices then
      f (x + unitVertex i) - f x else 0)
  have e : cubeGradSum V f i = ∑ x ∈ V.toIntegerCube.vertices,
      (if x + unitVertex i ∈ V.toIntegerCube.vertices then f (x + unitVertex i) - f x else 0) :=
    rfl
  rw [e]
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- The squares of the spatial sums of the gradient over a cube are at most its size times the edge
energy. -/
theorem sum_sq_cubeGradSum_le (V : TriadicCube 2) (f : Vertex 2 → ℝ) :
    ∑ i : Fin 2, cubeGradSum V f i ^ 2 ≤
      (V.toIntegerCube.vertices.card : ℝ) * edgeEnergy V.toIntegerCube.vertices f := by
  have e : edgeEnergy V.toIntegerCube.vertices f = ∑ i : Fin 2, ∑ x ∈ V.toIntegerCube.vertices,
      (if x + unitVertex i ∈ V.toIntegerCube.vertices then (f (x + unitVertex i) - f x) ^ 2
        else 0) := by
    rw [edgeEnergy, Finset.sum_comm]
  rw [e, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sq_cubeGradSum_le V f i

/-- The edges of the subcubes are edges of the cube. -/
theorem sum_edgeEnergy_subcubes_le {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (f : Vertex 2 → ℝ) :
    ∑ V ∈ subcubesAt U n, edgeEnergy V.toIntegerCube.vertices f ≤
      edgeEnergy U.toIntegerCube.vertices f := by
  simp only [edgeEnergy]
  have h := sum_scaleCube_eq hn (fun V x => ∑ i : Fin 2,
    if x + unitVertex i ∈ V.toIntegerCube.vertices then (f (x + unitVertex i) - f x) ^ 2 else 0)
  rw [← h]
  refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun i _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    have hxU := (U.mem_toIntegerCube_vertices x).1 hx
    exact h2 ((U.mem_toIntegerCube_vertices _).2 (scaleCube_subset hn hxU
      (((scaleCube n x).mem_toIntegerCube_vertices _).1 h1)))
  · exact sq_nonneg _
  · exact le_rfl

/-- **The quantity of display (5.12) by the energies.** -/
theorem restrictError_le_energy {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (fU : Vertex 2 → ℝ) (fV : TriadicCube 2 → Vertex 2 → ℝ) :
    ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
        ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2 ≤
      4 / U.volume * (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 +
        ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) := by
  have hN := card_subcubesAt_mul hn
  have hvolU := U.volume_pos
  have hNpos : (0 : ℝ) < (subcubesAt U n).card := by
    rcases (Nat.cast_nonneg (α := ℝ) (subcubesAt U n).card).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hN
      exact hvolU.ne' hN.symm
  have h9 : (0 : ℝ) < 9 ^ n := by positivity
  have hterm : ∀ V ∈ subcubesAt U n, ∑ i : Fin 2,
      ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2 ≤
      2 / 9 ^ n * (edgeEnergy V.toIntegerCube.vertices fU +
        edgeEnergy V.toIntegerCube.vertices (fV V)) := by
    intro V hV
    have hVs : V.scale = n := scale_of_mem_subcubesAt hV
    have hvol : V.volume = (9 : ℝ) ^ n := by rw [TriadicCube.volume, hVs]
    have hcard : (V.toIntegerCube.vertices.card : ℝ) = 9 ^ n := by
      rw [card_toIntegerCube_vertices_eq, hVs]
    have h1 := sum_sq_cubeGradSum_le V fU
    have h2 := sum_sq_cubeGradSum_le V (fV V)
    rw [hcard] at h1 h2
    have hpt : ∀ i : Fin 2, ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2 ≤
        2 * (cubeGradSum V fU i ^ 2 + cubeGradSum V (fV V) i ^ 2) / (9 ^ n) ^ 2 := by
      intro i
      rw [div_pow, hvol]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      nlinarith [sq_nonneg (cubeGradSum V fU i + cubeGradSum V (fV V) i)]
    calc ∑ i : Fin 2, ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2
        ≤ ∑ i : Fin 2, 2 * (cubeGradSum V fU i ^ 2 + cubeGradSum V (fV V) i ^ 2) / (9 ^ n) ^ 2 :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = 2 * (∑ i : Fin 2, cubeGradSum V fU i ^ 2 + ∑ i : Fin 2, cubeGradSum V (fV V) i ^ 2) /
            (9 ^ n) ^ 2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (9 ^ n * edgeEnergy V.toIntegerCube.vertices fU +
            9 ^ n * edgeEnergy V.toIntegerCube.vertices (fV V)) / (9 ^ n) ^ 2 := by
          gcongr
      _ = 2 / 9 ^ n * (edgeEnergy V.toIntegerCube.vertices fU +
            edgeEnergy V.toIntegerCube.vertices (fV V)) := by
          field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hU := sum_edgeEnergy_subcubes_le hn fU
  have hEU := edgeEnergy_le_two_mul_sum_gradNormIn_sq U.toIntegerCube.vertices fU
  have hEV : ∑ V ∈ subcubesAt U n, edgeEnergy V.toIntegerCube.vertices (fV V) ≤
      2 * ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun V _ => edgeEnergy_le_two_mul_sum_gradNormIn_sq _ _
  have hE0 : 0 ≤ ∑ V ∈ subcubesAt U n, edgeEnergy V.toIntegerCube.vertices fU :=
    Finset.sum_nonneg fun V _ => edgeEnergy_nonneg _ _
  have hE1 : 0 ≤ ∑ V ∈ subcubesAt U n, edgeEnergy V.toIntegerCube.vertices (fV V) :=
    Finset.sum_nonneg fun V _ => edgeEnergy_nonneg _ _
  set A := ∑ x ∈ U.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 with hA
  set B := ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices,
    gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 with hB
  have hstep : ((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
        ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2 ≤
      ((subcubesAt U n).card : ℝ)⁻¹ * (2 / 9 ^ n * (2 * A + 2 * B)) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (inv_nonneg.2 hNpos.le)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  refine hstep.trans (le_of_eq ?_)
  rw [← hN]
  field_simp
  ring

/-- The constant of the pointwise bound of the energies of the coarsened minimizers. -/
noncomputable def energyConst : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
    (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) * (27 * 234256)

theorem energyConst_ne_top : energyConst ≠ ∞ := by
  rw [energyConst]
  finiteness

/-- **The energy of the coarsened minimizer of `μ`, pointwise**, by the moments of the reach. -/
theorem ofReal_energy_planarMuMinimizer_le (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (coarsen ω V (planarMuMinimizer ω V q)) x ^ 2) ≤
      energyConst * ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) *
        (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) := by
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · exact ofReal_coarse_minimizer_le_reachSum h.1 h.2 q (by norm_num)
  · have h0 : planarMuMinimizer ω V q = 0 := by rw [planarMuMinimizer, dif_neg h]
    rw [h0, coarsen_zero]
    simp [gradNormIn]

/-- **The energy of the coarsened maximizer of `ν`, pointwise**, by the moments of the reach. -/
theorem ofReal_energy_planarNuSolution_le (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
          (coarsen ω V (planarNuSolution ω V ξ)) x ^ 2) ≤
      energyConst * ENNReal.ofReal (18 * (|ξ 0| + |ξ 1|) ^ 2) *
        (V.toIntegerCube.vertices.card : ℝ≥0∞) *
          (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) := by
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω V
  · have hsol : planarNuSolution ω V ξ = planarNuMaximizer ω V ξ := by
      rw [planarNuSolution, if_pos h]
    rw [hsol]
    have h1 := ofReal_sum_gradNormIn_coarse_sq_le h.1 h.2 (planarNuMaximizer ω V ξ)
    have hvol := V.volume_pos
    have hNvol : (V.toIntegerCube.vertices.card : ℝ) = V.volume := (volume_eq_card V).symm
    have hB : ENNReal.ofReal (clusterForm ω V (planarNuMaximizer ω V ξ)
        (planarNuMaximizer ω V ξ)) ≤ ENNReal.ofReal (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2) *
        (V.toIntegerCube.vertices.card : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hν := planarNu_le (ω := ω) (U := V) ξ
      have he := planarNu_eq_planarNuMaximizer (ω := ω) V ξ
      rw [hNvol]
      rw [he] at hν
      rw [div_div, div_le_iff₀ (by positivity)] at hν
      linarith
    have hsup : (3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 ≤
        27 * (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) := by
      have h7 := sup_planarReach_pow_seven_le (ω := ω) V (show 1 ≤ 3 by norm_num)
      have h1R : 1 ≤ V.toIntegerCube.vertices.sup (planarReach ω) := by
        obtain ⟨z, hz⟩ := TriadicCube.toIntegerCube_vertices_nonempty V
        exact (one_le_planarReach h.1 z).trans (Finset.le_sup (f := planarReach ω) hz)
      rw [mul_pow]
      have : (3 : ℝ≥0∞) ^ 3 = 27 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ h1R (by norm_num : 3 ≤ 7)).trans h7)
        zero_le
    have hq : ENNReal.ofReal (9 / 2 * (|ξ 0| + |ξ 1|) ^ 2) ≤
        234256 * ENNReal.ofReal (18 * (|ξ 0| + |ξ 1|) ^ 2) := by
      rw [show (234256 : ℝ≥0∞) = ENNReal.ofReal 234256 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (|ξ 0| + |ξ 1|)])
    refine h1.trans ?_
    rw [energyConst]
    calc ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) *
          (3 * V.toIntegerCube.vertices.sup (planarReach ω)) ^ 3 *
          ENNReal.ofReal (clusterForm ω V (planarNuMaximizer ω V ξ) (planarNuMaximizer ω V ξ))
        ≤ ENNReal.ofReal ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2) *
          (27 * (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ))) *
          ((234256 * ENNReal.ofReal (18 * (|ξ 0| + |ξ 1|) ^ 2)) *
            (V.toIntegerCube.vertices.card : ℝ≥0∞)) := by
          gcongr
          exact hB.trans (mul_le_mul_of_nonneg_right hq zero_le)
      _ = _ := by ring
  · have h0 : planarNuSolution ω V ξ = 0 := by rw [planarNuSolution, if_neg h]
    rw [h0, coarsen_zero]
    simp [gradNormIn]

/-- The sum of the moments of the reach over a subcube is at most the sum over the cube. -/
theorem sum_reachSum_subcube_le {U V : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (hV : V ∈ subcubesAt U n) (m : ℕ) :
    ∑ z ∈ V.toIntegerCube.vertices, reachSum ω m z ≤
      ∑ z ∈ U.toIntegerCube.vertices, reachSum ω m z :=
  Finset.sum_le_sum_of_subset_of_nonneg (toIntegerCube_vertices_subset_of_mem_subcubesAt hn hV)
    fun _ _ _ => zero_le

/-- The sum of the sizes of the subcubes is the size of the cube. -/
theorem sum_card_subcubes {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale) :
    ∑ V ∈ subcubesAt U n, (V.toIntegerCube.vertices.card : ℝ≥0∞) =
      (U.toIntegerCube.vertices.card : ℝ≥0∞) := by
  have h := sum_scaleCube_eq hn (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h' : (∑ V ∈ subcubesAt U n, V.toIntegerCube.vertices.card : ℕ) =
      U.toIntegerCube.vertices.card := by exact_mod_cast h.symm
  rw [← h', Nat.cast_sum]

/-- **The majorant from the energies.** For functions `u_U` and `u_V` whose energies are bounded
pointwise by `K Q |W| X_W^{1/3}`, `X_W = ∑_{z ∈ W} R(z)^{21}`, the quantity of display (5.12) is at
most `8 K Q X_U^{1/3}`. -/
theorem ofReal_restrictError_le_majorant {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (fU : Vertex 2 → ℝ) (fV : TriadicCube 2 → Vertex 2 → ℝ) (c : ℝ≥0∞)
    (hU : ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2) ≤
      c * (U.toIntegerCube.vertices.card : ℝ≥0∞) *
        (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)))
    (hV : ∀ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤
      c * (V.toIntegerCube.vertices.card : ℝ≥0∞) *
        (∑ z ∈ V.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ))) :
    ENNReal.ofReal (((subcubesAt U n).card : ℝ)⁻¹ * ∑ V ∈ subcubesAt U n, ∑ i : Fin 2,
        ((cubeGradSum V fU i - cubeGradSum V (fV V) i) / V.volume) ^ 2) ≤
      8 * c * (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) := by
  set X := (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) with hX
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have hvol := U.volume_pos
  have hNvol : ((U.toIntegerCube.vertices.card : ℕ) : ℝ) = U.volume := (volume_eq_card U).symm
  have h1 := ENNReal.ofReal_le_ofReal (restrictError_le_energy hn fU fV)
  refine h1.trans ?_
  have hA0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : ∀ V ∈ subcubesAt U n, 0 ≤ ∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2 :=
    fun V _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.ofReal_mul (div_nonneg (by norm_num) hvol.le),
    ENNReal.ofReal_add hA0 (Finset.sum_nonneg hB0),
    ENNReal.ofReal_sum_of_nonneg hB0]
  have hVX : ∀ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤
      c * (V.toIntegerCube.vertices.card : ℝ≥0∞) * X := fun V hV' =>
    (hV V hV').trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow
      (sum_reachSum_subcube_le hn hV' _) (by positivity)) zero_le)
  have hsumV : ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2) ≤ c * N * X := by
    calc ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2)
        ≤ ∑ V ∈ subcubesAt U n, c * (V.toIntegerCube.vertices.card : ℝ≥0∞) * X :=
          Finset.sum_le_sum hVX
      _ = c * N * X := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sum_card_subcubes hn]
  have h4 : ENNReal.ofReal (4 / U.volume) * N = 4 := by
    rw [hNdef, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg (by norm_num) hvol.le),
      hNvol,
      div_mul_cancel₀ _ hvol.ne']
    simp
  calc ENNReal.ofReal (4 / U.volume) * (ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
        gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices fU x ^ 2) +
        ∑ V ∈ subcubesAt U n, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices (fV V) x ^ 2))
      ≤ ENNReal.ofReal (4 / U.volume) * (c * N * X + c * N * X) := by gcongr
    _ = 2 * (ENNReal.ofReal (4 / U.volume) * N) * c * X := by ring
    _ = 8 * c * X := by
        rw [h4]
        ring

/-- **Jensen's inequality for the cube root of the moments of the reach.** -/
theorem lintegral_reachSum_rpow_le (μ : Measure (Configuration 2)) [IsProbabilityMeasure μ]
    (U : TriadicCube 2) :
    ∫⁻ ω, ((∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ))) ^ 2 ∂μ ≤
      (∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z ∂μ) ^ (2 / 3 : ℝ) := by
  have hXm : Measurable fun ω => ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z :=
    Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * 3) z
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hXm.pow_const (2 / 3 : ℝ)).aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  have hpt : ∀ ω, ((∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^
      (1 / ((3 : ℕ) : ℝ))) ^ 2 = (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^
        (2 / 3 : ℝ) := fun ω => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [lintegral_congr fun ω => hpt ω]
  refine h.trans (le_of_eq ?_)
  have e : (1 / (3 / 2 : ℝ)) = 2 / 3 := by norm_num
  rw [e]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **A measurable majorant of the quantity of display (5.12) for `μ` with a second moment.** -/
theorem exists_planarMuRestrictError_majorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ ω, ENNReal.ofReal (planarMuRestrictError ω U n q) ≤ M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p) ≤
          C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ) := by
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * 3)
  refine ⟨(8 * energyConst * 18) ^ 2 * CT ^ (2 / 3 : ℝ), ?_, fun U n hn q => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (by norm_num) energyConst_ne_top) (by norm_num)))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCT)
  set c : ℝ≥0∞ := energyConst * ENNReal.ofReal (18 * (|q 0| + |q 1|) ^ 2) with hc
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) with hXdef
  have hXm : Measurable X :=
    (Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * 3) z).pow_const _
  refine ⟨fun ω => 8 * c * X ω, hXm.const_mul _, fun ω => ?_, ?_⟩
  · have h := ofReal_restrictError_le_majorant (ω := ω) hn
      (coarsen ω U (planarMuMinimizer ω U q)) (fun V => coarsen ω V (planarMuMinimizer ω V q)) c
      (ofReal_energy_planarMuMinimizer_le U q)
      (fun V _ => ofReal_energy_planarMuMinimizer_le V q)
    simp only [← coarsePairing_single_eq_cubeGradSum] at h
    exact h
  · have hpt : ∀ ω, (8 * c * X ω) ^ 2 = (8 * c) ^ 2 * X ω ^ 2 := fun ω => by ring
    simp only [hpt]
    rw [lintegral_const_mul _ (hXm.pow_const 2)]
    have hJ := lintegral_reachSum_rpow_le (latticeBondLaw 2 p) U
    have hEX : ∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p) ≤
        (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
      rw [lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * 3) z]
      calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p)
          ≤ ∑ _z ∈ U.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
        _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (8 * c) ^ 2 * ∫⁻ ω, X ω ^ 2 ∂(latticeBondLaw 2 p)
        ≤ (8 * c) ^ 2 * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (2 / 3 : ℝ) := by
          gcongr
          exact hJ.trans (ENNReal.rpow_le_rpow hEX (by norm_num))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hc,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
          simp only [ENNReal.ofReal_ofNat]
          ring

/-- **A measurable majorant of the quantity of display (5.12) for `ν` with a second moment.** -/
theorem exists_planarNuRestrictError_majorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ ω, ENNReal.ofReal (planarNuRestrictError ω U n ξ) ≤ M ω) ∧
        ∫⁻ ω, M ω ^ 2 ∂(latticeBondLaw 2 p) ≤
          C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2) ^ 2 *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (2 / 3 : ℝ) := by
  obtain ⟨CT, hCT, hT⟩ := exists_lintegral_tsum_ninefold_le hpc (7 * 3)
  refine ⟨(8 * energyConst * 18) ^ 2 * CT ^ (2 / 3 : ℝ), ?_, fun U n hn ξ => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (by norm_num) energyConst_ne_top) (by norm_num)))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCT)
  set c : ℝ≥0∞ := energyConst * ENNReal.ofReal (18 * (|ξ 0| + |ξ 1|) ^ 2) with hc
  set X : Configuration 2 → ℝ≥0∞ := fun ω =>
    (∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z) ^ (1 / ((3 : ℕ) : ℝ)) with hXdef
  have hXm : Measurable X :=
    (Finset.measurable_fun_sum _ fun z _ => measurable_reachSum (7 * 3) z).pow_const _
  refine ⟨fun ω => 8 * c * X ω, hXm.const_mul _, fun ω => ?_, ?_⟩
  · have h := ofReal_restrictError_le_majorant (ω := ω) hn
      (coarsen ω U (planarNuSolution ω U ξ)) (fun V => coarsen ω V (planarNuSolution ω V ξ)) c
      (ofReal_energy_planarNuSolution_le U ξ)
      (fun V _ => ofReal_energy_planarNuSolution_le V ξ)
    simp only [← coarsePairing_single_eq_cubeGradSum] at h
    exact h
  · have hpt : ∀ ω, (8 * c * X ω) ^ 2 = (8 * c) ^ 2 * X ω ^ 2 := fun ω => by ring
    simp only [hpt]
    rw [lintegral_const_mul _ (hXm.pow_const 2)]
    have hJ := lintegral_reachSum_rpow_le (latticeBondLaw 2 p) U
    have hEX : ∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p) ≤
        (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
      rw [lintegral_finsetSum _ fun z _ => measurable_reachSum (7 * 3) z]
      calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω, reachSum ω (7 * 3) z ∂(latticeBondLaw 2 p)
          ≤ ∑ _z ∈ U.toIntegerCube.vertices, CT := Finset.sum_le_sum fun z _ => hT z
        _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * CT := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (8 * c) ^ 2 * ∫⁻ ω, X ω ^ 2 ∂(latticeBondLaw 2 p)
        ≤ (8 * c) ^ 2 * ((U.toIntegerCube.vertices.card : ℝ≥0∞) * CT) ^ (2 / 3 : ℝ) := by
          gcongr
          exact hJ.trans (ENNReal.rpow_le_rpow hEX (by norm_num))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hc,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
          simp only [ENNReal.ofReal_ofNat]
          ring

end Rigidity.Proofs.Cluster
