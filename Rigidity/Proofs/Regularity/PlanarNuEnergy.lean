import Rigidity.Proofs.Regularity.PlanarAffineFromNu
import Rigidity.Proofs.Percolation.PlanarNuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarCubeEnergyBounds

/-!
# The energy and the coarsening error of the maximizers of `ν`

* `clusterForm_planarNuSolution_le`: on the partition event and for a resolved cube, the energy of
  the maximizer of `ν(V, p)` is at most `(9/2) |p|₁² |V|` (`ν(V, p) ≤ (9/4) |p|₁²` and
  `ν(V, p) |V| = B(v, v)/2`);
* `clusterForm_combo_le`: `B(a v₀ + b v₁) ≤ 2 a² B(v₀) + 2 b² B(v₁)`;
* `sum_gradNormIn_sq_eq_clusterForm`: the sum of the squared open gradients is the energy;
* `sum_sq_extend_sub_coarsen_le`: Lemma 3.2 of Armstrong and Dario (arXiv:1609.09431v2) with the
  reach scales bounded by `D`: `Σ_{C_*(V)} (v - [v]_𝒫)² ≤ K² D⁴ B(v, v)`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical

variable {ω : Configuration 2}

theorem clusterForm_planarNuSolution_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (p : Fin 2 → ℝ) :
    clusterForm ω V (planarNuSolution ω V p) (planarNuSolution ω V p) ≤
      9 / 2 * (|p 0| + |p 1|) ^ 2 * V.volume := by
  have e : planarNuSolution ω V p = planarNuMaximizer ω V p := by
    unfold planarNuSolution; rw [if_pos ⟨hP, hV⟩]
  rw [e]
  obtain ⟨hv, hvar⟩ := planarNuMaximizer_spec (ω := ω) V p
  have h1 := planarNu_mul_volume_eq p hv hvar
  have h2 := planarNu_le (ω := ω) (U := V) p
  have hvol := V.volume_pos
  have := mul_le_mul_of_nonneg_right h2 hvol.le
  linarith

theorem planarNuSolution_mem_clusterHarmonic (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (p : Fin 2 → ℝ) :
    planarNuSolution ω V p ∈ clusterHarmonic ω V := by
  unfold planarNuSolution; rw [if_pos ⟨hP, hV⟩]
  exact (planarNuMaximizer_spec V p).1

theorem clusterForm_combo_le {V : TriadicCube 2} (v₀ v₁ : ClusterFun ω V) (a b : ℝ) :
    clusterForm ω V (a • v₀ + b • v₁) (a • v₀ + b • v₁) ≤
      2 * a ^ 2 * clusterForm ω V v₀ v₀ + 2 * b ^ 2 * clusterForm ω V v₁ v₁ := by
  have h := clusterForm_self_nonneg (ω := ω) (a • v₀ - b • v₁)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul] at h ⊢
  have hs := clusterForm_symm (ω := ω) v₀ v₁
  nlinarith [hs]

/-- The sum of the squared open gradients on the cluster of `V` is the energy. -/
theorem sum_gradNormIn_sq_eq_clusterForm {V : TriadicCube 2} (v : ClusterFun ω V) :
    ∑ z ∈ clusterVertices ω V,
        gradNormIn (openGraph ω) (clusterVertices ω V) (clusterExtend ω V v) z ^ 2 =
      clusterForm ω V v v := by
  have hpt : ∀ z ∈ clusterVertices ω V,
      gradNormIn (openGraph ω) (clusterVertices ω V) (clusterExtend ω V v) z ^ 2 =
        (1 / 2) * ∑ y ∈ clusterVertices ω V, if (openGraph ω).Adj z y then
          (clusterExtend ω V v z - clusterExtend ω V v y) ^ 2 else 0 := by
    intro z _
    rw [gradNormIn, Real.sq_sqrt (mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => by
      split_ifs <;> positivity))]
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, clusterForm_apply]
  congr 1
  rw [← Finset.sum_coe_sort (clusterVertices ω V)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_coe_sort (clusterVertices ω V)]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold clusterFormTerm
  rw [clusterExtend_apply_of_mem _ z.2, clusterExtend_apply_of_mem _ y.2]
  split_ifs <;> ring

/-- **Lemma 3.2 with bounded reach scales**: `Σ_{C_*(V)} (v - [v]_𝒫)² ≤ K² D⁴ B(v, v)`. -/
theorem sum_sq_extend_sub_coarsen_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (v : ClusterFun ω V) {D : ℝ}
    (hD : ∀ z ∈ clusterVertices ω V, (3 : ℝ) ^ (planarCoarseData hP V hV).reachScale z ≤ D) :
    ∑ x ∈ clusterVertices ω V, (clusterExtend ω V v x - coarsen ω V v x) ^ 2 ≤
      planarCoarseConst ^ 2 * D ^ 4 * clusterForm ω V v v := by
  have h := planar_sum_abs_sub_coarseAnchor_rpow_le hP hV (clusterExtend ω V v) (s := 2)
    (by norm_num)
  have e1 : ∀ x ∈ clusterVertices ω V,
      |clusterExtend ω V v x - clusterExtend ω V v (planarCoarseAnchor ω x)| ^ (2 : ℝ) =
        (clusterExtend ω V v x - coarsen ω V v x) ^ 2 := fun x _ => by
    rw [Real.rpow_two, sq_abs]; rfl
  have e2 : ∀ z ∈ clusterVertices ω V,
      ((3 : ℝ) ^ (planarCoarseData hP V hV).reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ)) *
        gradNormIn (openGraph ω) (clusterVertices ω V) (clusterExtend ω V v) z ^ (2 : ℝ) =
      ((3 : ℝ) ^ (planarCoarseData hP V hV).reachScale z) ^ (4 : ℕ) *
        gradNormIn (openGraph ω) (clusterVertices ω V) (clusterExtend ω V v) z ^ 2 := fun z _ => by
    rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_two]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Real.rpow_two] at h
  have hconst : (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
      (2 * √((2 : ℕ) : ℝ))) = planarCoarseConst := rfl
  rw [hconst] at h
  refine h.trans ?_
  rw [mul_assoc, ← sum_gradNormIn_sq_eq_clusterForm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hD z hz) 4) (sq_nonneg _)

open Rigidity.Proofs.Multiscale (affineFun finsetMean) in
/-- **The flatness of a combination** of two coarsened functions, against the affine function of the
combined slope: `Σ_V (a g₀ + b g₁)² ≤ 2 |V| (a² flat₀ + b² flat₁)`. -/
theorem sum_sq_coarsen_combo_le {V : TriadicCube 2} (v₀ v₁ : ClusterFun ω V) (q : Fin 2 → ℝ) :
    ∑ x ∈ V.toIntegerCube.vertices,
        (coarsen ω V (q 0 • v₀ + q 1 • v₁) x - affineFun q x -
          (q 0 * finsetMean V.toIntegerCube.vertices
              (fun y => coarsen ω V v₀ y - affineFun (Pi.single 0 1) y) +
            q 1 * finsetMean V.toIntegerCube.vertices
              (fun y => coarsen ω V v₁ y - affineFun (Pi.single 1 1) y))) ^ 2 ≤
      2 * V.volume * (q 0 ^ 2 * planarFlatnessError V (coarsen ω V v₀) (Pi.single 0 1) +
        q 1 ^ 2 * planarFlatnessError V (coarsen ω V v₁) (Pi.single 1 1)) := by
  set m₀ := finsetMean V.toIntegerCube.vertices
    (fun y => coarsen ω V v₀ y - affineFun (Pi.single 0 1) y) with hm₀
  set m₁ := finsetMean V.toIntegerCube.vertices
    (fun y => coarsen ω V v₁ y - affineFun (Pi.single 1 1) y) with hm₁
  set g₀ : Vertex 2 → ℝ := fun x => coarsen ω V v₀ x - affineFun (Pi.single 0 1) x - m₀ with hg₀
  set g₁ : Vertex 2 → ℝ := fun x => coarsen ω V v₁ x - affineFun (Pi.single 1 1) x - m₁ with hg₁
  have hlin : ∀ x, coarsen ω V (q 0 • v₀ + q 1 • v₁) x - affineFun q x - (q 0 * m₀ + q 1 * m₁) =
      q 0 * g₀ x + q 1 * g₁ x := by
    intro x
    have hc : coarsen ω V (q 0 • v₀ + q 1 • v₁) x = q 0 * coarsen ω V v₀ x + q 1 * coarsen ω V v₁ x := by
      unfold coarsen
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have ha : affineFun q x = q 0 * affineFun (Pi.single 0 1) x + q 1 * affineFun (Pi.single 1 1) x := by
      simp [affineFun, Fin.sum_univ_two]
    rw [hc, ha, hg₀, hg₁]
    ring
  have hf₀ : ∑ x ∈ V.toIntegerCube.vertices, g₀ x ^ 2 =
      V.volume * planarFlatnessError V (coarsen ω V v₀) (Pi.single 0 1) := by
    unfold planarFlatnessError
    rw [← mul_assoc, mul_inv_cancel₀ V.volume_pos.ne', one_mul]
  have hf₁ : ∑ x ∈ V.toIntegerCube.vertices, g₁ x ^ 2 =
      V.volume * planarFlatnessError V (coarsen ω V v₁) (Pi.single 1 1) := by
    unfold planarFlatnessError
    rw [← mul_assoc, mul_inv_cancel₀ V.volume_pos.ne', one_mul]
  calc ∑ x ∈ V.toIntegerCube.vertices,
        (coarsen ω V (q 0 • v₀ + q 1 • v₁) x - affineFun q x - (q 0 * m₀ + q 1 * m₁)) ^ 2
      = ∑ x ∈ V.toIntegerCube.vertices, (q 0 * g₀ x + q 1 * g₁ x) ^ 2 :=
        Finset.sum_congr rfl fun x _ => by rw [hlin]
    _ ≤ ∑ x ∈ V.toIntegerCube.vertices, (2 * q 0 ^ 2 * g₀ x ^ 2 + 2 * q 1 ^ 2 * g₁ x ^ 2) :=
        Finset.sum_le_sum fun x _ => by
          nlinarith [sq_nonneg (q 0 * g₀ x - q 1 * g₁ x)]
    _ = 2 * q 0 ^ 2 * ∑ x ∈ V.toIntegerCube.vertices, g₀ x ^ 2 +
          2 * q 1 ^ 2 * ∑ x ∈ V.toIntegerCube.vertices, g₁ x ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hf₀, hf₁]; ring

end Rigidity.Proofs.Regularity
