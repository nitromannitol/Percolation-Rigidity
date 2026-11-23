import Rigidity.Proofs.Regularity.PlanarNuEnergy
import Rigidity.Proofs.Regularity.PlanarGradNormBound

/-!
# The approximation of affine functions on growing balls of the planar cluster

`affineApproximation_at_scale` builds, at the scale `3^{j+1}`, a function harmonic on
`𝒞_∞ ∩ B_{3^{j+1}}` close to `q · x`: the combination `q₀ v(·, □, e₀) + q₁ v(·, □, e₁)` of the
maximizers of `ν` on `□ = □_{j+3}`, minus a constant. Its distance to `q · x` is bounded by the
flatness errors (Lemma 5.8 of Armstrong and Dario, arXiv:1609.09431v2), the coarsening error
(Lemma 3.2 with bounded reach scales) and the energy bound of the maximizers.

`planarAffineApproximationAeTwo_of_nuFlatness` proves `PlanarAffineApproximationAeTwo`, the input of
Step 3 of Proposition 3.1 of Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1) for `k = 1`, from
(5.33) in expectation, the decay of `τ` and the minimal scales of Proposition 2.4.
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open Rigidity.Proofs.Multiscale (affineFun finsetMean)
open scoped Classical ENNReal

variable {ω : Configuration 2}

/-- **The approximation at one scale.** -/
theorem affineApproximation_at_scale (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (hinf : C.supp.Infinite) {j : ℕ} (hres : PlanarResolved ω ⟨j + 3, 0⟩)
    (hsc : ∀ x ∈ triadicCubeFinset 2 (j + 3) 0, (planarPartCube ω x).scale ≤ j) {D Fl κ' : ℝ}
    (hD : ∀ z ∈ clusterVertices ω ⟨j + 3, 0⟩,
      (3 : ℝ) ^ (planarCoarseData hP ⟨j + 3, 0⟩ hres).reachScale z ≤ D)
    (hfl : ∀ i : Fin 2, planarFlatnessError ⟨j + 3, 0⟩
      (coarsen ω ⟨j + 3, 0⟩ (planarNuSolution ω ⟨j + 3, 0⟩ (Pi.single i 1))) (Pi.single i 1) ≤ Fl)
    (hκ' : 0 < κ') (hcard : κ' ≤ (componentEuclideanBall C 0 ((3 : ℝ) ^ (j + 1))).card)
    (q : Fin 2 → ℝ) :
    ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ (j + 1)) ∧
      componentBallL2 C 0 (3 ^ (j + 1)) (fun x => v x - componentSlope C q x) ≤
        Real.sqrt (2 * (2 * (⟨j + 3, 0⟩ : TriadicCube 2).volume * ((q 0 ^ 2 + q 1 ^ 2) * Fl) +
          planarCoarseConst ^ 2 * D ^ 4 * (9 * (q 0 ^ 2 + q 1 ^ 2) *
            (⟨j + 3, 0⟩ : TriadicCube 2).volume)) / κ') := by
  set V : TriadicCube 2 := ⟨j + 3, 0⟩ with hVdef
  set v₀ := planarNuSolution ω V (Pi.single 0 1) with hv₀
  set v₁ := planarNuSolution ω V (Pi.single 1 1) with hv₁
  set v := q 0 • v₀ + q 1 • v₁ with hvdef
  set c := q 0 * finsetMean V.toIntegerCube.vertices
      (fun y => coarsen ω V v₀ y - affineFun (Pi.single 0 1) y) +
    q 1 * finsetMean V.toIntegerCube.vertices
      (fun y => coarsen ω V v₁ y - affineFun (Pi.single 1 1) y) with hc
  have hvH : v ∈ clusterHarmonic ω V :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (planarNuSolution_mem_clusterHarmonic hP hres _))
      (Submodule.smul_mem _ _ (planarNuSolution_mem_clusterHarmonic hP hres _))
  -- the inclusions
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hin : ∀ x : C, x ∈ componentEuclideanBall C 0 ((3 : ℝ) ^ (j + 1)) →
      x.val ∈ clusterVertices ω V ∧ V.IsInterior x.val := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx
    have hcoord : ∀ k, |((x.val k : ℤ) : ℝ)| < 3 * 3 ^ j := by
      intro k
      have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) k
      have e : (((0 : Vertex 2) k : ℤ) : ℝ) = 0 := by simp
      rw [e, sub_zero] at h1
      have : (3 : ℝ) ^ (j + 1) = 3 * 3 ^ j := by ring
      linarith
    have hcoordZ : ∀ k, |x.val k| < 3 * 3 ^ j := by
      intro k
      have := hcoord k
      have h' : ((|x.val k| : ℤ) : ℝ) < ((3 * 3 ^ j : ℤ) : ℝ) := by push_cast; exact this
      exact_mod_cast h'
    refine ⟨mem_clusterVertices_inner hP C hinf hsc x.2 fun k => ?_, fun y hy => ?_⟩
    · have := hcoordZ k
      have h0 : (0 : ℤ) < 3 ^ j := by positivity
      linarith
    · rw [mem_triadicCube_zero_iff]
      intro k
      have h1 := hcoordZ k
      have h2 := hy k
      have h0 : (1 : ℤ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
      have e : (3 : ℤ) ^ (j + 3) = 27 * 3 ^ j := by ring
      have a := abs_sub_abs_le_abs_sub (y k) (x.val k)
      rw [abs_sub_comm (y k) (x.val k)] at a
      rw [e]
      linarith
  refine ⟨fun x => clusterExtend ω V v x.val - c,
    harmonicOnBall_of_clusterHarmonic hP hres C hvH c hin, ?_⟩
  -- the energy and the coarsening error
  have hE : clusterForm ω V v v ≤ 9 * (q 0 ^ 2 + q 1 ^ 2) * V.volume := by
    have h1 := clusterForm_combo_le (ω := ω) v₀ v₁ (q 0) (q 1)
    have e0 : (|(Pi.single 0 1 : Fin 2 → ℝ) 0| + |(Pi.single 0 1 : Fin 2 → ℝ) 1|) = 1 := by
      simp
    have e1 : (|(Pi.single 1 1 : Fin 2 → ℝ) 0| + |(Pi.single 1 1 : Fin 2 → ℝ) 1|) = 1 := by
      simp
    have h2' : clusterForm ω V v₀ v₀ ≤ 9 / 2 * V.volume := by
      have := clusterForm_planarNuSolution_le hP hres (Pi.single 0 1)
      rw [e0] at this; simpa using this
    have h3' : clusterForm ω V v₁ v₁ ≤ 9 / 2 * V.volume := by
      have := clusterForm_planarNuSolution_le hP hres (Pi.single 1 1)
      rw [e1] at this; simpa using this
    have hq0 : 0 ≤ q 0 ^ 2 := sq_nonneg _
    have hq1 : 0 ≤ q 1 ^ 2 := sq_nonneg _
    nlinarith
  have hG := sum_sq_extend_sub_coarsen_le hP hres v hD
  have hG' : ∑ x ∈ clusterVertices ω V, (clusterExtend ω V v x - coarsen ω V v x) ^ 2 ≤
      planarCoarseConst ^ 2 * D ^ 4 * (9 * (q 0 ^ 2 + q 1 ^ 2) * V.volume) :=
    hG.trans (mul_le_mul_of_nonneg_left hE (by positivity))
  -- the flatness
  have hF := sum_sq_coarsen_combo_le (ω := ω) v₀ v₁ q
  have hF' : ∑ x ∈ clusterVertices ω V, (coarsen ω V v x - affineFun q x - c) ^ 2 ≤
      2 * V.volume * ((q 0 ^ 2 + q 1 ^ 2) * Fl) := by
    have hsub : clusterVertices ω V ⊆ V.toIntegerCube.vertices := Finset.filter_subset _ _
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
      (hF.trans ?_)
    have hvol := V.volume_pos
    have h0 := hfl 0
    have h1 := hfl 1
    have hq0 : 0 ≤ q 0 ^ 2 := sq_nonneg _
    have hq1 : 0 ≤ q 1 ^ 2 := sq_nonneg _
    have : q 0 ^ 2 * planarFlatnessError V (coarsen ω V v₀) (Pi.single 0 1) +
        q 1 ^ 2 * planarFlatnessError V (coarsen ω V v₁) (Pi.single 1 1) ≤
        (q 0 ^ 2 + q 1 ^ 2) * Fl := by nlinarith
    nlinarith
  exact componentBallL2_le_of_sums C v q c hκ' (fun x hx => (hin x hx).1) hcard hF' hG'

end Rigidity.Proofs.Regularity
