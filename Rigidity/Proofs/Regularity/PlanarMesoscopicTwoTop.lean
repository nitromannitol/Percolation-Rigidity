import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoSteps

/-!
# The coarsening at the top scale in the proof of Lemma 7.3 at `k = 2` in the plane

At the top scale `T = R / (8A)` of the iteration of Lemma 7.2 for the coarsening `U = [u]_𝒫` of a
function `u` harmonic on `𝒞_∞ ∩ B_R` (Armstrong and Dario, arXiv:1609.09431v2, proof of
Lemma 7.3, the passage from (7.19) to (7.20) and Step 2, (7.22)–(7.23)), the excesses of `U`
over the lattice harmonic quadratic functions and over the constants on `B_T` are bounded by the
excesses of `u` on the cluster ball
`B_R`, by the oscillation `G = R^{-1} inf_a R^{-1} ‖u - a‖_{ℓ²(𝒞_∞ ∩ B_R)}` and by the harmonic
approximation error at the scale `4T` (`ballExcess_two_top_le`, `ballExcess_zero_top_le`):
a lattice harmonic approximant `v` on `B_{4T}`, the `ℓ^∞`–`ℓ¹` bound of `v - W` for a harmonic
quadratic polynomial `W`, the `ℓ¹` bound of `U - W` through the anchors (with the moments of the
sizes of the partition cubes), and the bound of the slope of `W` by the oscillation of `W` on the
cluster ball (`coeff_le_componentBallL2_sub_const`).

The harmonic approximation error at `4T` is bounded through the crude bound of the coarse
oscillation at the scale `R/2 = 4AT` (`harmonicApproximation_error_le`): the partition cubes of
side at most `S'` give `D_0(U; R/2) ≤ 2 S' inf_a R^{-1} ‖u - a‖_{ℓ²(𝒞_∞ ∩ B_R)}`; with
`S' ≤ c R^{α/2}` this loss is absorbed by the factor `(4T)^{-α}` in the final estimate.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

theorem iSup_Icc_self_le {f : ℝ → ℝ} (a : ℝ) : (⨆ s : Set.Icc a a, f s) ≤ f a := by
  haveI : Nonempty (Set.Icc a a) := ⟨⟨a, le_rfl, le_rfl⟩⟩
  refine ciSup_le fun s => ?_
  rw [show (s : ℝ) = a from le_antisymm s.2.2 s.2.1]

/-- The anchors of the points of `B_ρ` stay in `B_R` when the cubes have side at most `S'`. -/
theorem anchor_bounds (hP : PlanarPartitionEvent ω) {ρ R S' : ℝ} (hS' : S' ≤ R / 8)
    (hρR : ρ ≤ R / 2) {y : Vertex 2}
    (hy : dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < ρ)
    (hside : (3 : ℝ) ^ (planarPartCube ω y).scale ≤ S') :
    dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
        (latticeEuclideanEmbedding (0 : Vertex 2)) < R ∧
      (∀ i, |((planarCoarseAnchor ω y i : ℤ) : ℝ)| ≤ R) ∧ ∀ i, |((y i : ℤ) : ℝ)| ≤ R := by
  have hcoord : ∀ i, |((planarCoarseAnchor ω y i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤ S' := fun i => by
    have h := (abs_coarseAnchor_sub_lt hP y i).le
    have e : ((planarPartCube ω y).side : ℝ) = (3 : ℝ) ^ (planarPartCube ω y).scale := by
      simp [TriadicCube.side]
    have h' : ((|planarCoarseAnchor ω y i - y i| : ℤ) : ℝ) ≤ ((planarPartCube ω y).side : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    rw [e] at h'
    exact h'.trans hside
  have hS0 : 0 ≤ S' := (abs_nonneg _).trans (hcoord 0)
  have hd : dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y)) (latticeEuclideanEmbedding y)
      ≤ Real.sqrt ((2 : ℕ) : ℝ) * S' :=
    dist_latticeEuclideanEmbedding_le hS0 fun i => hcoord i
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hdist : dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
      (latticeEuclideanEmbedding (0 : Vertex 2)) < R := by
    have := dist_triangle (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
      (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2))
    have hd' : dist (latticeEuclideanEmbedding (planarCoarseAnchor ω y))
        (latticeEuclideanEmbedding y) ≤ 3 / 2 * S' :=
      hd.trans (mul_le_mul_of_nonneg_right hs2 hS0)
    have := dist_nonneg (x := latticeEuclideanEmbedding y)
      (y := latticeEuclideanEmbedding (0 : Vertex 2))
    linarith
  refine ⟨hdist, fun i => ?_, fun i => ?_⟩
  · have := (abs_sub_le_dist_latticeEuclideanEmbedding (planarCoarseAnchor ω y) 0 i).trans
      hdist.le
    simpa using this
  · have := (abs_sub_le_dist_latticeEuclideanEmbedding y 0 i).trans hy.le
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at this
    linarith

/-- **The sum of the coarse error at the top scale.** -/
theorem sum_abs_coarse_sub_quad_top_le (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    {ρ R S' K₁ K₂ : ℝ} (hR : 0 < R) (hS' : S' ≤ R / 8) (hρR : ρ ≤ R / 2)
    (hsize : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R →
        (3 : ℝ) ^ (planarPartCube ω y).scale ≤ S')
    (hm₁ : ∑ y ∈ latticeBallPoints 0 R, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ K₁ * R ^ 2)
    (hm₂ : ∑ y ∈ latticeBallPoints 0 R, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤ K₂ * R ^ 2)
    (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∑ y ∈ latticeBallPoints 0 ρ,
        |coarseAtAnchor (uniqueInfiniteComponent h) u y - latticeQuadFun a p M y| ≤
      Real.sqrt (K₂ * R ^ 2) * (R * clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun x => latticeQuadFun a p M x.val)) +
        2 * (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * (K₁ * R ^ 2) := by
  classical
  set Λ := |p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hball : ∀ y ∈ latticeBallPoints 0 ρ,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < ρ :=
    fun y hy => mem_latticeBallPoints.1 hy
  have hρR' : ρ ≤ R := by linarith
  have hsub : latticeBallPoints 0 ρ ⊆ latticeBallPoints 0 R := fun y hy =>
    mem_latticeBallPoints.2 ((hball y hy).trans_le hρR')
  have hb := fun y hy => anchor_bounds hP hS' hρR (hball y hy)
    (hsize y ((hball y hy).trans_le hρR'))
  have h1 := sum_abs_coarse_sub_le hP h u (latticeQuadFun a p M) hΛ0
    (fun y hy => (hb y hy).1)
    (fun y hy => abs_quadratic_sub_le a p M (hb y hy).2.2 (hb y hy).2.1)
  have hm₂' : ∑ y ∈ latticeBallPoints 0 ρ, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤
      K₂ * R ^ 2 :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans hm₂
  have hm₁' : ∑ y ∈ latticeBallPoints 0 ρ, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ K₁ * R ^ 2 :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans hm₁
  have hcl : Real.sqrt (∑ x ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
      (u x - latticeQuadFun a p M x.val) ^ 2) =
      R * clusterBallVolumeL2 (uniqueInfiniteComponent h) R
        (u - fun x => latticeQuadFun a p M x.val) := by
    rw [clusterBallVolumeL2, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hR.le]
    field_simp
    rfl
  rw [hcl] at h1
  refine h1.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hm₂') (by
      have := clusterBallVolumeL2_nonneg' (uniqueInfiniteComponent h) R
        (u - fun x => latticeQuadFun a p M x.val)
      positivity)
  · exact mul_le_mul_of_nonneg_left hm₁' (by positivity)

theorem clusterBallVolumeL2_neg (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) :
    clusterBallVolumeL2 C r (-f) = clusterBallVolumeL2 C r f := by
  simp [clusterBallVolumeL2]

theorem clusterBallVolumeL2_sub_le (C : OpenComponent ω) (r : ℝ) (f g : C → ℝ) :
    clusterBallVolumeL2 C r (f - g) ≤ clusterBallVolumeL2 C r f + clusterBallVolumeL2 C r g := by
  rw [sub_eq_add_neg, ← clusterBallVolumeL2_neg C r g]
  exact clusterBallVolumeL2_add_le' C r f (-g)

/-- `‖·‖_{L̲²(C ∩ B_R)} ≤ √(72/κ) R^{-1} ‖·‖_{ℓ²(C ∩ B_R)}` under the density in cubes. -/
theorem componentBallL2_le_clusterBallVolumeL2 (C : OpenComponent ω) {ℓ κ R : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 (24 * Real.sqrt ((2 : ℕ) : ℝ)) ℓ κ)
    (hR : 6 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 ≤ R) (f : C → ℝ) :
    componentBallL2 C 0 R f ≤ Real.sqrt (72 / κ) * clusterBallVolumeL2 C R f := by
  have hcard := le_card_componentEuclideanBall C hκ.le hcube hR
  have hR0 : 0 < R := by
    have : 0 < 6 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 := by
      have := le_max_right ℓ 1; positivity
    linarith
  rw [clusterBallVolumeL2_eq C hR0.le]
  have hc : Real.sqrt (κ / 72) ≤ Real.sqrt (((componentEuclideanBall C 0 R).card : ℝ) / R ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hN0 := componentBallL2_nonneg C 0 R f
  have hprod : Real.sqrt (72 / κ) * Real.sqrt (κ / 72) = 1 := by
    rw [← Real.sqrt_mul (by positivity), show 72 / κ * (κ / 72) = 1 by field_simp, Real.sqrt_one]
  calc componentBallL2 C 0 R f = Real.sqrt (72 / κ) * Real.sqrt (κ / 72) * componentBallL2 C 0 R f := by
        rw [hprod, one_mul]
    _ ≤ Real.sqrt (72 / κ) * (Real.sqrt (((componentEuclideanBall C 0 R).card : ℝ) / R ^ 2) *
          componentBallL2 C 0 R f) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hN0) (Real.sqrt_nonneg _)

/-- The constant of `coeff_le_componentBallL2_sub_const`. -/
noncomputable def quadCoeffConst (κ : ℝ) : ℝ :=
  4 / Real.sqrt (capFraction 2 κ) * (1 + 4 / quadLowerConst 2 κ (capFraction 2 κ)) +
    4 / quadLowerConst 2 κ (capFraction 2 κ)

theorem quadCoeffConst_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ quadCoeffConst κ := by
  have hδ : 0 < capFraction 2 κ := capFraction_pos (by norm_num) hκ
  have hq : 0 < quadLowerConst 2 κ (capFraction 2 κ) := quadLowerConst_pos (by norm_num) hκ hδ
  unfold quadCoeffConst; positivity

/-- **The slope at the top scale.** -/
theorem slope_le_of_clusterCubeDensity (C : OpenComponent ω) {ℓ κ R : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 (quadLocality 2 (capFraction 2 κ)) ℓ κ)
    (hR : quadLocality 2 (capFraction 2 κ) * max ℓ 1 ≤ R) (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (u : C → ℝ) :
    (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R ≤
      2 * quadCoeffConst κ * Real.sqrt (72 / κ) *
        ((⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c)) +
          clusterBallVolumeL2 C R (u - fun x => latticeQuadFun a p M x.val)) := by
  have hδ : 0 < capFraction 2 κ := capFraction_pos (by norm_num) hκ
  have hΛ24 := le_quadLocality (d := 2) (by norm_num) hδ
  have hmax : 1 ≤ max ℓ 1 := le_max_right _ _
  have hcube24 := hcube.of_le C 0 hΛ24
  have h24 : 24 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 ≤ R :=
    (mul_le_mul_of_nonneg_right hΛ24 (by linarith)).trans hR
  have h6 : 6 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 ≤ R := by
    have : 0 ≤ Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 := by positivity
    linarith
  have hR0 : 0 < R := by
    have : 0 < 6 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1 := by positivity
    linarith
  have hcap := (clusterBallCapDensity_of_clusterCubeDensity C 0 R (by norm_num) hκ hcube24)
  have hcap' : ClusterBallCapDensity C 0 (24 * Real.sqrt ((2 : ℕ) : ℝ) * max ℓ 1) R
      (capFraction 2 κ) := hcap
  have hQ := quadCoeffConst_nonneg hκ
  have hs := Real.sqrt_nonneg (72 / κ)
  set Kc := 2 * quadCoeffConst κ * Real.sqrt (72 / κ) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set E := clusterBallVolumeL2 C R (u - fun x => latticeQuadFun a p M x.val) with hE
  have key : ∀ c : ℝ, (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R ≤
      Kc * E + Kc * clusterBallVolumeL2 C R (u - fun _ => c) := by
    intro c
    have h1 := coeff_le_componentBallL2_sub_const C hκ hcube hR hcap' h24 le_rfl hR0 a p M c
    have h2 := componentBallL2_le_clusterBallVolumeL2 C hκ hcube24 h6
      (fun x => latticeQuadFun a p M x.val - c)
    have e : (fun x : C => latticeQuadFun a p M x.val - c) =
        (u - fun _ => c) - (u - fun x => latticeQuadFun a p M x.val) := by
      funext x; simp only [Pi.sub_apply]; ring
    have h3 := clusterBallVolumeL2_sub_le C R (u - fun _ => c)
      (u - fun x => latticeQuadFun a p M x.val)
    rw [← e] at h3
    have hsplit : (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R ≤
        2 * ((|p 0| + |p 1|) * R + (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R ^ 2) := by
      have : 0 ≤ (|p 0| + |p 1|) * R := by positivity
      nlinarith
    have hN0 := componentBallL2_nonneg C 0 R (fun x => latticeQuadFun a p M x.val - c)
    calc (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R
        ≤ 2 * (quadCoeffConst κ * componentBallL2 C 0 R
            (fun x => latticeQuadFun a p M x.val - c)) := by
          rw [quadCoeffConst]; linarith
      _ ≤ 2 * (quadCoeffConst κ * (Real.sqrt (72 / κ) *
            clusterBallVolumeL2 C R (fun x => latticeQuadFun a p M x.val - c))) := by
          gcongr
      _ ≤ 2 * (quadCoeffConst κ * (Real.sqrt (72 / κ) *
            (clusterBallVolumeL2 C R (u - fun _ => c) + E))) := by
          gcongr
      _ = Kc * E + Kc * clusterBallVolumeL2 C R (u - fun _ => c) := by rw [hKc]; ring
  have := le_add_mul_iInf hKc0 key
  calc _ ≤ Kc * E + Kc * ⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c) := this
    _ = Kc * ((⨅ c : ℝ, clusterBallVolumeL2 C R (u - fun _ => c)) + E) := by ring

end Rigidity.Proofs.Regularity
