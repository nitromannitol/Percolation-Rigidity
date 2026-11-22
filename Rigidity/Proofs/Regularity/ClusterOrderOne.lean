import Rigidity.Proofs.Regularity.OrderOneEndpoint
import Rigidity.Proofs.Regularity.ClusterKIterationOne
import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth

/-!
# The endpoint iteration of order one on the balls of a cluster

This file provides the data of `Rigidity.Proofs.Regularity.OrderOneEndpointData` for the
normalized `L²` norms `componentBallL2 C 0 t` on the balls of an open cluster `C` centred at the
origin:

* `clusterHarmonicQuadratic C`: the restrictions to `C` of the harmonic quadratic polynomials
  `a + ⟪p, x⟫ + q_M(x)`, `tr M = 0`. For bond percolation the homogenized matrix is a multiple of
  the identity (Armstrong–Dario, arXiv:1609.09431v2, p. 3 and §5), so these are the
  `ā`-harmonic polynomials `Ā_2` of degree at most two;
* the affine functions `clusterAffineMap C (a, p) = a + ⟪p, x⟫`, the quadratic parts
  `clusterQuadMap C M = q_M` with `tr M = 0`, and the lift
  `clusterLiftMap C g (a, p) = a + ∑ᵢ pᵢ gᵢ` by functions `gᵢ` (for the infinite cluster, the
  corrected planes of slope `eᵢ`);
* the sizes `|a| + t ‖p‖` and `∑ᵢ ∑ⱼ |(Mᵢⱼ + Mⱼᵢ) / 2|`, and the harmonicity in `C ∩ B_r` at the
  vertices whose open-edge neighbours lie in `B_r`.

`orderOneEndpointData_cluster` proves the hypotheses of the endpoint iteration from the density of
the cluster in cubes (the comparison of the sizes with the norms uses
`le_ballExcess_clusterQuadratic` and `le_componentBallL2_affine`), the bound
`|gᵢ(x) - xᵢ| ≤ ε t / √d` on `C ∩ B_t`, the harmonicity of the `gᵢ` and the mesoscopic estimate
at degree two, which are hypotheses. `clusterLiftMap_mem_harmonicGrowthSpace`: the lifted affine
functions belong to `𝒜₁` when the `gᵢ` do.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

theorem latticeEuclideanEmbedding_zero :
    latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
  ext i
  change (((0 : Vertex d) i : ℤ) : ℝ) = (0 : EuclideanSpace ℝ (Fin d)) i
  simp

theorem norm_lt_of_mem_componentEuclideanBall {C : OpenComponent ω} {t : ℝ} {x : C}
    (hx : x ∈ componentEuclideanBall C 0 t) : ‖latticeEuclideanEmbedding x.val‖ < t := by
  rw [mem_componentEuclideanBall, latticeEuclideanEmbedding_zero, dist_zero_right] at hx
  exact hx

/-- The trace-free matrices. -/
def traceZeroMatrix (d : ℕ) : AddSubgroup (Matrix (Fin d) (Fin d) ℝ) where
  carrier := {M | M.trace = 0}
  add_mem' := by
    intro M M' hM hM'
    simp only [Set.mem_setOf_eq, Matrix.trace_add] at hM hM' ⊢
    rw [hM, hM', add_zero]
  zero_mem' := by
    show Matrix.trace (0 : Matrix (Fin d) (Fin d) ℝ) = 0
    simp
  neg_mem' := by
    intro M hM
    simp only [Set.mem_setOf_eq, Matrix.trace_neg] at hM ⊢
    rw [hM, neg_zero]

/-- The restrictions to a cluster of the harmonic quadratic polynomials
`x ↦ a + ⟪p, x⟫ + q_M(x)` with `tr M = 0`. -/
def clusterHarmonicQuadratic (C : OpenComponent ω) : AddSubgroup (C → ℝ) where
  carrier := {f | ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ),
    M.trace = 0 ∧ ∀ x, f x = a + inner ℝ p (latticeEuclideanEmbedding x.val) +
      quadForm M (latticeEuclideanEmbedding x.val)}
  add_mem' := by
    rintro f g ⟨a, p, M, hM, ha⟩ ⟨b, q, N, hN, hb⟩
    refine ⟨a + b, p + q, M + N, by rw [Matrix.trace_add, hM, hN, add_zero], fun x => ?_⟩
    simp only [Pi.add_apply, ha, hb, inner_add_left, quadForm, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib]
    ring
  zero_mem' := ⟨0, 0, 0, by simp, fun _ => by simp [quadForm]⟩
  neg_mem' := by
    rintro f ⟨a, p, M, hM, ha⟩
    refine ⟨-a, -p, -M, by rw [Matrix.trace_neg, hM, neg_zero], fun x => ?_⟩
    simp only [Pi.neg_apply, ha, inner_neg_left, quadForm, Matrix.neg_apply, neg_mul,
      Finset.sum_neg_distrib]
    ring

/-- The affine functions `(a, p) ↦ (x ↦ a + ⟪p, x⟫)` on a cluster. -/
noncomputable def clusterAffineMap (C : OpenComponent ω) :
    (ℝ × EuclideanSpace ℝ (Fin d)) →+ (C → ℝ) where
  toFun ℓ x := ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val)
  map_zero' := by funext x; simp
  map_add' ℓ ℓ' := by
    funext x
    simp only [Prod.fst_add, Prod.snd_add, inner_add_left, Pi.add_apply]
    ring

/-- The quadratic parts `M ↦ (x ↦ q_M(x))`, `tr M = 0`, on a cluster. -/
def clusterQuadMap (C : OpenComponent ω) : traceZeroMatrix d →+ (C → ℝ) where
  toFun M x := quadForm (M : Matrix (Fin d) (Fin d) ℝ) (latticeEuclideanEmbedding x.val)
  map_zero' := by funext x; simp [quadForm]
  map_add' M M' := by
    funext x
    simp only [AddSubgroup.coe_add, quadForm, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
      Pi.add_apply]

/-- The lift `(a, p) ↦ a + ∑ᵢ pᵢ gᵢ` of the affine functions by functions `gᵢ` on a cluster. -/
noncomputable def clusterLiftMap (C : OpenComponent ω) (g : Fin d → C → ℝ) :
    (ℝ × EuclideanSpace ℝ (Fin d)) →+ (C → ℝ) where
  toFun ℓ x := ℓ.1 + ∑ i, ℓ.2 i * g i x
  map_zero' := by funext x; simp
  map_add' ℓ ℓ' := by
    funext x
    simp only [Prod.fst_add, Prod.snd_add, PiLp.add_apply, add_mul, Finset.sum_add_distrib,
      Pi.add_apply]
    ring

/-- The size `|a| + t ‖p‖` of the affine function `a + ⟪p, x⟫` at the radius `t`. -/
noncomputable def affineSize (t : ℝ) (ℓ : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ :=
  |ℓ.1| + t * ‖ℓ.2‖

/-- The size `∑ᵢ ∑ⱼ |(Mᵢⱼ + Mⱼᵢ) / 2|` of the quadratic part `q_M`. -/
noncomputable def quadSize (M : traceZeroMatrix d) : ℝ :=
  ∑ i, ∑ j, |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j|

/-- Harmonicity in `C ∩ B_r`: the Laplacian vanishes at every vertex of `C ∩ B_r` all of whose
open-edge neighbours lie in `B_r`. -/
def ClusterBallHarmonic (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) : Prop :=
  ∀ z ∈ componentEuclideanBall C 0 r,
    (∀ w, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C 0 r) →
      componentLaplacian C f z = 0

/-- The constant of the comparison of the sizes with the norms on cluster balls. -/
noncomputable def clusterPolyConst (d : ℕ) (κ : ℝ) : ℝ :=
  2 / Real.sqrt (capFraction d κ) * (1 + d * (d ^ 2 / quadLowerConst d κ (capFraction d κ))) +
    d ^ 2 / quadLowerConst d κ (capFraction d κ)

/-- The volume constant of cluster balls from the density in cubes. -/
noncomputable def clusterVolumeConst (d : ℕ) (κ : ℝ) : ℝ := (5 * (6 * Real.sqrt d)) ^ d / κ

theorem clusterLiftMap_mem_harmonicGrowthSpace (C : OpenComponent ω) {g : Fin d → C → ℝ}
    (hg : ∀ i, g i ∈ harmonicGrowthSpace C 1) (ℓ : ℝ × EuclideanSpace ℝ (Fin d)) :
    clusterLiftMap C g ℓ ∈ harmonicGrowthSpace C 1 := by
  have e : clusterLiftMap C g ℓ = (fun _ => ℓ.1) + ∑ i, ℓ.2 i • g i := by
    funext x
    simp [clusterLiftMap, Finset.sum_apply]
  rw [e]
  exact add_mem (const_mem_harmonicGrowthSpace C 1 ℓ.1)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg i))

theorem componentLaplacian_sub (C : OpenComponent ω) (f φ : C → ℝ) (z : C) :
    componentLaplacian C (f - φ) z = componentLaplacian C f z - componentLaplacian C φ z := by
  unfold componentLaplacian
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem abs_symEntry_le_quadSize (M : traceZeroMatrix d) (i j : Fin d) :
    |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j| ≤ quadSize M := by
  unfold quadSize
  calc |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j| ≤
        ∑ j', |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j'| :=
        Finset.single_le_sum (f := fun j' => |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i' j'| :=
        Finset.single_le_sum
          (f := fun i' => ∑ j', |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem quadSize_le_of_forall_le (M : traceZeroMatrix d) {m : ℝ}
    (hm : ∀ i j, |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j| ≤ m) :
    quadSize M ≤ d ^ 2 * m := by
  unfold quadSize
  calc ∑ i, ∑ j, |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, m :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
    _ = d ^ 2 * m := by simp [Finset.sum_const]; ring

/-- **The hypotheses of the endpoint iteration on the balls of a cluster** centred at the origin,
for the radii `[X, R]` with `X` above the scale of the density of the cluster in cubes. -/
theorem orderOneEndpointData_cluster (C : OpenComponent ω) (hd : 0 < d) {κ ℓc X R A δ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hcube : ClusterCubeDensity C 0 (quadLocality d (capFraction d κ)) ℓc κ)
    (hX : quadLocality d (capFraction d κ) * max ℓc 1 ≤ X)
    {g : Fin d → C → ℝ} (hgharm : ∀ i, g i ∈ harmonicGrowthSpace C 1)
    (hg : ∀ t, X ≤ t → t ≤ R → ∀ i, ∀ x ∈ componentEuclideanBall C 0 t,
      |g i x - latticeEuclideanEmbedding x.val i| ≤ ε / Real.sqrt d * t)
    (hmeso : ∀ r w, 2 * X ≤ r → r ≤ R → ClusterBallHarmonic C r w → ∀ v, X ≤ v → v ≤ r / 2 →
      ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) v w ≤
        A * (v / r) ^ 3 * ballExcess (componentBallSeminorm C 0) (clusterHarmonicQuadratic C) r w +
          A * v ^ (-δ) * (v / r) * componentBallSeminorm C 0 r w) :
    OrderOneEndpointData (componentBallSeminorm C 0) (clusterHarmonicQuadratic C)
      (clusterAffineMap C) (clusterLiftMap C g) (clusterQuadMap C) affineSize quadSize
      (ClusterBallHarmonic C) X R A δ (Real.sqrt (clusterVolumeConst d κ)) ((d : ℝ) / 2) d
      (clusterPolyConst d κ) ε := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 hd
  set δc := capFraction d κ with hδc
  have hδ0 : 0 < δc := capFraction_pos hd hκ
  have hc₂ := quadLowerConst_pos hd hκ hδ0
  set c₂ := quadLowerConst d κ δc with hc₂def
  have hΛ := le_quadLocality hd hδ0
  set Λ := quadLocality d δc with hΛdef
  have hmax0 : 1 ≤ max ℓc 1 := le_max_right _ _
  have hΛ0 : 0 < Λ := by linarith
  have hX0 : 0 < X := lt_of_lt_of_le (mul_pos hΛ0 (by linarith)) hX
  have hcube24 := hcube.of_le C 0 hΛ
  have h24 : 24 * Real.sqrt d * max ℓc 1 ≤ X :=
    (mul_le_mul_of_nonneg_right hΛ (by linarith)).trans hX
  have h6 : 6 * Real.sqrt d * max ℓc 1 ≤ X := by
    have : 0 ≤ Real.sqrt d * max ℓc 1 := mul_nonneg hsd.le (by linarith)
    linarith
  have hvol := (clusterBallVolumeComparison_of_clusterCubeDensity C 0 R hd hκ hcube24).of_le h6
  have hcap : ClusterBallCapDensity C 0 X R δc :=
    (clusterBallCapDensity_of_clusterCubeDensity C 0 R hd hκ hcube24).of_le h24
  have hK0 : 0 ≤ clusterVolumeConst d κ := by unfold clusterVolumeConst; positivity
  -- the quadratic part on a ball
  have hquad : ∀ t, X ≤ t → ∀ M : traceZeroMatrix d,
      componentBallL2 C 0 t (clusterQuadMap C M) ≤ d * t ^ 2 * quadSize M := by
    intro t ht M
    have hq0 : 0 ≤ quadSize M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      abs_nonneg _
    apply componentBallL2_le_of_abs_le C 0 t (by positivity)
    intro x hx
    have hxt := norm_lt_of_mem_componentEuclideanBall hx
    have h1 := abs_quadForm_le (M : Matrix (Fin d) (Fin d) ℝ) hq0 (abs_symEntry_le_quadSize M)
      (latticeEuclideanEmbedding x.val)
    have h2 : ‖latticeEuclideanEmbedding x.val‖ ^ 2 ≤ t ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hxt.le 2
    calc |clusterQuadMap C M x| ≤ d * quadSize M * ‖latticeEuclideanEmbedding x.val‖ ^ 2 := h1
      _ ≤ d * quadSize M * t ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = d * t ^ 2 * quadSize M := by ring
  -- the affine part on a ball
  have haff : ∀ t, X ≤ t → ∀ ℓ : ℝ × EuclideanSpace ℝ (Fin d),
      componentBallL2 C 0 t (clusterAffineMap C ℓ) ≤ affineSize t ℓ := by
    intro t ht ℓ
    have ht0 : 0 < t := hX0.trans_le ht
    apply componentBallL2_le_of_abs_le C 0 t (by unfold affineSize; positivity)
    intro x hx
    have hxt := norm_lt_of_mem_componentEuclideanBall hx
    have h1 := abs_real_inner_le_norm ℓ.2 (latticeEuclideanEmbedding x.val)
    have h2 : ‖ℓ.2‖ * ‖latticeEuclideanEmbedding x.val‖ ≤ t * ‖ℓ.2‖ := by
      rw [mul_comm t]; exact mul_le_mul_of_nonneg_left hxt.le (norm_nonneg _)
    show |ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val)| ≤ |ℓ.1| + t * ‖ℓ.2‖
    exact (abs_add_le _ _).trans (by linarith)
  refine
    { sz_nonneg := ?_, nq_nonneg := ?_, nq_zero := ?_, nq_le_add := ?_, quad_le := ?_,
      affine_le := ?_, sz_le := ?_, le_poly := ?_, lift_le := ?_, mem_P₂ := ?_,
      exists_of_mem := ?_, mono := ?_, harm_anti := ?_, harm_sub := ?_, meso := hmeso }
  · intro t ℓ ht
    have : 0 ≤ t := hX0.le.trans ht
    unfold affineSize; positivity
  · intro M
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  · simp [quadSize, symEntry]
  · intro M M'
    unfold quadSize
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have e : symEntry (M' : Matrix (Fin d) (Fin d) ℝ) i j =
        symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j +
          symEntry ((M' - M : traceZeroMatrix d) : Matrix (Fin d) (Fin d) ℝ) i j := by
      simp only [AddSubgroup.coe_sub, symEntry, Matrix.sub_apply]
      ring
    rw [e]
    exact abs_add_le _ _
  · intro t ht _ M
    rw [componentBallSeminorm_apply]
    exact hquad t ht M
  · intro t ht _ ℓ
    rw [componentBallSeminorm_apply]
    exact haff t ht ℓ
  · intro t s ht hts _ ℓ
    have ht0 : 0 < t := hX0.trans_le ht
    have hst : 1 ≤ s / t := by rw [le_div_iff₀ ht0]; linarith
    unfold affineSize
    have h1 : |ℓ.1| ≤ s / t * |ℓ.1| := le_mul_of_one_le_left (abs_nonneg _) hst
    have h2 : s / t * (t * ‖ℓ.2‖) = s * ‖ℓ.2‖ := by field_simp
    linarith only [h1, h2]
  · intro t ht htR ℓ M
    have ht0 : 0 < t := hX0.trans_le ht
    rw [componentBallSeminorm_apply]
    set f := clusterAffineMap C ℓ + clusterQuadMap C M with hf
    have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
      ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
    obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun ij : Fin d × Fin d => |symEntry (M : Matrix (Fin d) (Fin d) ℝ) ij.1 ij.2|) hne
    set m := |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i₀ j₀| with hmdef
    have hm : ∀ i j, |symEntry (M : Matrix (Fin d) (Fin d) ℝ) i j| ≤ m :=
      fun i j => hmax (i, j) (Finset.mem_univ _)
    have hm0 : 0 ≤ m := abs_nonneg _
    have hw : ∀ x, f x = ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val) +
        quadForm (M : Matrix (Fin d) (Fin d) ℝ) (latticeEuclideanEmbedding x.val) := fun x => rfl
    have hq := le_ballExcess_clusterQuadratic C 0 (ρ := t) hd hκ hcube (hX.trans ht) hw hm
      hmdef.symm
    have hqf : c₂ * m * t ^ 2 ≤ componentBallL2 C 0 t f :=
      hq.trans ((ballExcess_le_self (componentBallSeminorm C 0) (clusterAffine C) t f).trans_eq
        (componentBallSeminorm_apply C 0 t f))
    have hnq : quadSize M ≤ d ^ 2 * m := quadSize_le_of_forall_le M hm
    have hnqf : t ^ 2 * quadSize M ≤ d ^ 2 / c₂ * componentBallL2 C 0 t f := by
      have h1 : t ^ 2 * quadSize M ≤ d ^ 2 * (m * t ^ 2) := by
        have := mul_le_mul_of_nonneg_left hnq (sq_nonneg t)
        linarith
      have h2 : d ^ 2 * (m * t ^ 2) ≤ d ^ 2 / c₂ * componentBallL2 C 0 t f := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc₂]
        have := mul_le_mul_of_nonneg_left hqf (sq_nonneg (d : ℝ))
        linarith
      exact h1.trans h2
    have hιf : componentBallL2 C 0 t (clusterAffineMap C ℓ) ≤
        (1 + d * (d ^ 2 / c₂)) * componentBallL2 C 0 t f := by
      have h1 : clusterAffineMap C ℓ = f + -clusterQuadMap C M := by rw [hf]; abel
      have h2 := componentBallL2_add_le C 0 t f (-clusterQuadMap C M)
      have h3 : componentBallL2 C 0 t (-clusterQuadMap C M) =
          componentBallL2 C 0 t (clusterQuadMap C M) := by
        have := componentBallSeminorm_apply C 0 t (-clusterQuadMap C M)
        rw [← this, map_neg_eq_map, componentBallSeminorm_apply]
      have h4 := hquad t ht M
      have h5 : (d : ℝ) * t ^ 2 * quadSize M ≤ d * (d ^ 2 / c₂ * componentBallL2 C 0 t f) := by
        have := mul_le_mul_of_nonneg_left hnqf hd0.le
        linarith
      rw [h1]
      linarith only [h2, h3, h4, h5]
    have hlowa := le_componentBallL2_affine C 0 hδ0 hcap ht htR ht0 ℓ.1 ℓ.2
    have he : (fun x : C => ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val -
        latticeEuclideanEmbedding 0)) = clusterAffineMap C ℓ := by
      funext x
      rw [latticeEuclideanEmbedding_zero, sub_zero]
      rfl
    rw [he] at hlowa
    have hsza : affineSize t ℓ ≤ 2 / Real.sqrt δc * componentBallL2 C 0 t (clusterAffineMap C ℓ) := by
      have hsδ : 0 < Real.sqrt δc := Real.sqrt_pos.2 hδ0
      unfold affineSize
      rw [div_mul_eq_mul_div, le_div_iff₀ hsδ]
      linarith only [hlowa]
    have hf0 : 0 ≤ componentBallL2 C 0 t f := componentBallL2_nonneg _ _ _ _
    have h2δ : 0 ≤ 2 / Real.sqrt δc := by positivity
    have h7 : 2 / Real.sqrt δc * componentBallL2 C 0 t (clusterAffineMap C ℓ) ≤
        2 / Real.sqrt δc * ((1 + d * (d ^ 2 / c₂)) * componentBallL2 C 0 t f) :=
      mul_le_mul_of_nonneg_left hιf h2δ
    unfold clusterPolyConst
    rw [← hδc, ← hc₂def]
    linarith only [hsza, h7, hnqf]
  · intro t ht htR ℓ
    rw [componentBallSeminorm_apply]
    apply componentBallL2_le_of_abs_le C 0 t (by
      have : 0 ≤ affineSize t ℓ := by
        have : 0 ≤ t := hX0.le.trans ht
        unfold affineSize; positivity
      positivity)
    intro x hx
    have hxt := norm_lt_of_mem_componentEuclideanBall hx
    have ht0 : 0 < t := hX0.trans_le ht
    have e : (clusterLiftMap C g ℓ - clusterAffineMap C ℓ) x =
        ∑ i, ℓ.2 i * (g i x - latticeEuclideanEmbedding x.val i) := by
      show (ℓ.1 + ∑ i, ℓ.2 i * g i x) - (ℓ.1 + inner ℝ ℓ.2 (latticeEuclideanEmbedding x.val)) = _
      rw [inner_eq_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 : |∑ i, ℓ.2 i * (g i x - latticeEuclideanEmbedding x.val i)| ≤
        ∑ i, |ℓ.2 i| * (ε / Real.sqrt d * t) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg t ht htR i x hx) (abs_nonneg _)
    have h2 : ∑ i, |ℓ.2 i| * (ε / Real.sqrt d * t) = (∑ i, |ℓ.2 i|) * (ε / Real.sqrt d * t) :=
      (Finset.sum_mul _ _ _).symm
    have h3 := sum_abs_le_sqrt_mul_norm ℓ.2
    have h4 : (∑ i, |ℓ.2 i|) * (ε / Real.sqrt d * t) ≤
        (Real.sqrt d * ‖ℓ.2‖) * (ε / Real.sqrt d * t) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : (Real.sqrt d * ‖ℓ.2‖) * (ε / Real.sqrt d * t) = ε * (t * ‖ℓ.2‖) := by
      field_simp
    have h6 : ε * (t * ‖ℓ.2‖) ≤ ε * affineSize t ℓ := by
      unfold affineSize
      exact mul_le_mul_of_nonneg_left (by linarith only [abs_nonneg ℓ.1]) hε
    linarith only [h1, h2, h4, h5, h6]
  · intro M
    exact ⟨0, 0, M, M.2, fun x => by simp [clusterQuadMap]⟩
  · rintro p ⟨a, β, M, hM, hp⟩
    refine ⟨(a, β), ⟨M, hM⟩, ?_⟩
    funext x
    rw [hp x]
    rfl
  · exact radiusMonotone_componentBallSeminorm C 0 hX0 hK0 hvol
  · intro r r' w hr'r hw z hz hzn
    have hsub := componentEuclideanBall_mono C 0 hr'r
    exact hw z (hsub hz) fun y hy => hsub (hzn y hy)
  · intro r w ℓ hw z hz hzn
    rw [componentLaplacian_sub, hw z hz hzn,
      ((mem_harmonicGrowthSpace_iff C 1 _).1 (clusterLiftMap_mem_harmonicGrowthSpace C hgharm ℓ)).1 z,
      sub_zero]

end Rigidity.Proofs.Regularity
