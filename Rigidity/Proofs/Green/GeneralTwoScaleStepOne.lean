import Rigidity.Proofs.Green.GeneralTwoScaleGaussian
import Rigidity.Proofs.Green.GeneralFluxWeakNormStatement
import Rigidity.Proofs.Green.BondHeat
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCoarseComparison

/-!
# Step 1 of Proposition 4.3 of Dario–Gu on `ℤ^d`: the equation of the two-scale expansion

Step 1 of the proof of Proposition 4.3 of Dario–Gu (lines 2245-2274 of the source) computes the
equation of the two-scale expansion
`h(t, x, y) = θ^{-1} (p̄(t, x - y) + Σ_k D_k p̄(t, · - y)(x) χ_{e_k}(x))` of (4.1) on the cluster.
With `P = p̄(t, · - y)` on the lattice, `a_i(x) = 1` on the open edges `{x, x + e_i}` and `0` on the
closed ones (`openCondD`), the flux `g_{k,i} = a_i (δ_{ik} + D_i χ_k)` of the corrected plane
`x_k + χ_k` (`openFluxD`) and `F_i = a_i (D_i D_i P - Σ_k χ_k D_i D_k P)` (`stepOneFD`):

* `openLaplacian_twoScaleD`: if `Σ_i (g_{k,i}(x - e_i) - g_{k,i}(x)) = 0` for every `k`, then
  `Δ(P + Σ_k D_k P χ_k)(x) = Σ_i (F_i(x - e_i) - F_i(x)) + Σ_{k,i} g̃_{k,i}(x) D_i D_k P(x)
  + (σ/2) Σ_k D_k D_k P(x)`;
* `sum_openFluxD_div_eq_zero`: the corrector equation in divergence form at the points of the
  cluster;
* `hasDerivAt_dgTwoScaleD_eq`: `∂_t h(t, x, y) = Δ h(t, ·, y)(x) + θ^{-1} G(t, x)` at `x ∈ 𝒞_∞`,
  with the source term `G = (∂_t P - (σ/2) Σ_k D_k D_k P) + Σ_k D_k ∂_t P χ_k
  - Σ_i (F_i(· - e_i) - F_i) - Σ_{k,i} g̃_{k,i} D_i D_k P` (`twoScaleSourceD`), the terms `f`,
  `D^* · F` and `ξ` of (4.25)-(4.26).

Compared with (4.26), the flux term pairs the centered flux `g̃` with the forward differences
`D_i D_k P`, the divergence term carries the corrector at the base point of each edge, and the
discrete Laplacian of `P` is `Σ_k D_k D_k P`; this is the planar computation of
`DarioGuTwoScaleStepOne` on `ℤ^d`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-- The conductance `a_i(x)` of the edge `{x, x + e_i}`: `1` if it is open, `0` otherwise. -/
noncomputable def openCondD (ω : Configuration d) (i : Fin d) (x : Vertex d) : ℝ :=
  if (openGraph ω).Adj x (x + Pi.single i 1) then 1 else 0

theorem abs_openCondD_le (ω : Configuration d) (i : Fin d) (x : Vertex d) :
    |openCondD ω i x| ≤ 1 := by
  unfold openCondD
  split_ifs <;> norm_num

theorem openCondD_nonneg (ω : Configuration d) (i : Fin d) (x : Vertex d) :
    0 ≤ openCondD ω i x := by
  unfold openCondD
  split_ifs <;> norm_num

theorem openCondD_sq (ω : Configuration d) (i : Fin d) (x : Vertex d) :
    openCondD ω i x ^ 2 = openCondD ω i x := by
  unfold openCondD
  split_ifs <;> norm_num

/-- The Laplacian of the open graph, direction by direction. -/
theorem openLaplacian_eq_sumD (ω : Configuration d) (u : Vertex d → ℝ) (x : Vertex d) :
    openLaplacian ω u x = ∑ i, (openCondD ω i x * (u (x + Pi.single i 1) - u x) +
      openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x)) := by
  rw [openLaplacian, sum_neighborFinset_openGraph_eq ω x (fun z => u z - u x),
    Rigidity.Proofs.Regularity.sum_nbrFinset]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc2 : openCondD ω i (x - Pi.single i 1) =
      if (openGraph ω).Adj x (x - Pi.single i 1) then 1 else 0 := by
    unfold openCondD
    rw [sub_add_cancel]
    by_cases h : (openGraph ω).Adj x (x - Pi.single i 1)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  rw [hc2]
  unfold openCondD unit
  split_ifs <;> ring

/-- The flux `g_{k,i}(x) = a_i(x) (δ_{ik} + D_i χ_k(x))` of the corrected plane `x_k + χ_k`. -/
noncomputable def openFluxD (ω : Configuration d) (χ : Fin d → Vertex d → ℝ) (k i : Fin d)
    (x : Vertex d) : ℝ :=
  openCondD ω i x * ((if i = k then 1 else 0) + (χ k (x + Pi.single i 1) - χ k x))

/-- The vector field `F_i = a_i (D_i D_i P - Σ_k χ_k D_i D_k P)` of the divergence term. -/
noncomputable def stepOneFD (ω : Configuration d) (χ : Fin d → Vertex d → ℝ) (P : Vertex d → ℝ)
    (i : Fin d) (z : Vertex d) : ℝ :=
  openCondD ω i z * (fwdDiffD i (fwdDiffD i P) z - ∑ k, χ k z * fwdDiffD i (fwdDiffD k P) z)

theorem centeredFluxD_eq (ω : Configuration d) (σ : ℝ) (χ : Fin d → Vertex d → ℝ)
    (k i : Fin d) (x : Vertex d) :
    centeredFluxD ω σ χ k i x = openFluxD ω χ k i x - σ / 2 * (if i = k then 1 else 0) := by
  unfold centeredFluxD openFluxD openCondD
  split_ifs <;> ring

/-- The algebra of one direction in Step 1. -/
theorem twoScale_edge_identity (A B C X Y Z : Fin d → ℝ) (a b p0 p1 pm Dii Dii' : ℝ) (i : Fin d)
    (h1 : p1 - p0 = B i) (h2 : pm - p0 = -C i) (h3 : Dii = A i - B i) (h4 : Dii' = B i - C i) :
    a * ((p1 + ∑ k, A k * X k) - (p0 + ∑ k, B k * Y k)) +
        b * ((pm + ∑ k, C k * Z k) - (p0 + ∑ k, B k * Y k)) =
      (b * (Dii' - ∑ k, Z k * (B k - C k)) - a * (Dii - ∑ k, Y k * (A k - B k))) +
        ∑ k, (A k * (a * ((if i = k then 1 else 0) + (X k - Y k))) -
          B k * (b * ((if i = k then 1 else 0) + (Y k - Z k)))) := by
  have hsplit : ∀ k, A k * (a * ((if i = k then 1 else 0) + (X k - Y k))) -
      B k * (b * ((if i = k then 1 else 0) + (Y k - Z k))) =
      (if i = k then a * A k - b * B k else 0) +
        (A k * (a * (X k - Y k)) - B k * (b * (Y k - Z k))) := by
    intro k
    split_ifs <;> ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : a * ((∑ k, A k * X k) - ∑ k, B k * Y k) +
      b * ((∑ k, C k * Z k) - ∑ k, B k * Y k) =
      -(b * ∑ k, Z k * (B k - C k)) + a * ∑ k, Y k * (A k - B k) +
        ∑ k, (A k * (a * (X k - Y k)) - B k * (b * (Y k - Z k))) := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3, h4]
  linear_combination key + a * h1 + b * h2

/-- One direction of the Laplacian of the two-scale expansion. -/
theorem twoScale_edge_term (ω : Configuration d) (χ : Fin d → Vertex d → ℝ) (P : Vertex d → ℝ)
    (x : Vertex d) (i : Fin d) :
    openCondD ω i x * ((P (x + Pi.single i 1) +
          ∑ k, fwdDiffD k P (x + Pi.single i 1) * χ k (x + Pi.single i 1)) -
        (P x + ∑ k, fwdDiffD k P x * χ k x)) +
      openCondD ω i (x - Pi.single i 1) * ((P (x - Pi.single i 1) +
          ∑ k, fwdDiffD k P (x - Pi.single i 1) * χ k (x - Pi.single i 1)) -
        (P x + ∑ k, fwdDiffD k P x * χ k x)) =
      (stepOneFD ω χ P i (x - Pi.single i 1) - stepOneFD ω χ P i x) +
        ∑ k, (fwdDiffD k P (x + Pi.single i 1) * openFluxD ω χ k i x -
          fwdDiffD k P x * openFluxD ω χ k i (x - Pi.single i 1)) := by
  have hxi : x - Pi.single i 1 + Pi.single i 1 = x := sub_add_cancel _ _
  have e1 : ∀ k, fwdDiffD i (fwdDiffD k P) (x - Pi.single i 1) =
      fwdDiffD k P x - fwdDiffD k P (x - Pi.single i 1) := fun k => by
    show fwdDiffD k P (x - Pi.single i 1 + Pi.single i 1) - _ = _
    rw [hxi]
  have e2 : P (x - Pi.single i 1) - P x = -fwdDiffD i P (x - Pi.single i 1) := by
    show _ = -(P (x - Pi.single i 1 + Pi.single i 1) - P (x - Pi.single i 1))
    rw [hxi]
    ring
  have e3 : ∀ k, openFluxD ω χ k i (x - Pi.single i 1) =
      openCondD ω i (x - Pi.single i 1) *
        ((if i = k then 1 else 0) + (χ k x - χ k (x - Pi.single i 1))) := fun k => by
    unfold openFluxD
    rw [hxi]
  unfold stepOneFD
  simp only [e1, e3]
  unfold openFluxD
  exact twoScale_edge_identity (fun k => fwdDiffD k P (x + Pi.single i 1))
    (fun k => fwdDiffD k P x) (fun k => fwdDiffD k P (x - Pi.single i 1))
    (fun k => χ k (x + Pi.single i 1)) (fun k => χ k x) (fun k => χ k (x - Pi.single i 1))
    (openCondD ω i x) (openCondD ω i (x - Pi.single i 1)) (P x) (P (x + Pi.single i 1))
    (P (x - Pi.single i 1)) (fwdDiffD i (fwdDiffD i P) x)
    (fwdDiffD i P x - fwdDiffD i P (x - Pi.single i 1)) i rfl e2 rfl rfl

/-- **Step 1 of Proposition 4.3 of Dario–Gu (spatial part)** on `ℤ^d`: the Laplacian of the open
graph of the two-scale expansion `P + Σ_k D_k P χ_k` at a point `x` where the corrector equation
holds. -/
theorem openLaplacian_twoScaleD (ω : Configuration d) (σ : ℝ) (χ : Fin d → Vertex d → ℝ)
    (P : Vertex d → ℝ) (x : Vertex d)
    (hχ : ∀ k, ∑ i, (openFluxD ω χ k i (x - Pi.single i 1) - openFluxD ω χ k i x) = 0) :
    openLaplacian ω (fun z => P z + ∑ k, fwdDiffD k P z * χ k z) x =
      ∑ i, (stepOneFD ω χ P i (x - Pi.single i 1) - stepOneFD ω χ P i x) +
        ∑ k, ∑ i, centeredFluxD ω σ χ k i x * fwdDiffD i (fwdDiffD k P) x +
        σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k P) x := by
  rw [openLaplacian_eq_sumD, Finset.sum_congr rfl fun i _ => twoScale_edge_term ω χ P x i,
    Finset.sum_add_distrib, add_assoc]
  congr 1
  have hk : ∀ k, ∑ i, (fwdDiffD k P (x + Pi.single i 1) * openFluxD ω χ k i x -
      fwdDiffD k P x * openFluxD ω χ k i (x - Pi.single i 1)) =
      ∑ i, centeredFluxD ω σ χ k i x * fwdDiffD i (fwdDiffD k P) x +
        σ / 2 * fwdDiffD k (fwdDiffD k P) x := by
    intro k
    have e : ∀ i, fwdDiffD k P (x + Pi.single i 1) * openFluxD ω χ k i x -
        fwdDiffD k P x * openFluxD ω χ k i (x - Pi.single i 1) =
        (centeredFluxD ω σ χ k i x * fwdDiffD i (fwdDiffD k P) x +
          σ / 2 * (if i = k then fwdDiffD i (fwdDiffD k P) x else 0)) -
          fwdDiffD k P x * (openFluxD ω χ k i (x - Pi.single i 1) - openFluxD ω χ k i x) := by
      intro i
      rw [centeredFluxD_eq]
      unfold fwdDiffD
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, ← Finset.mul_sum, hχ k,
      mul_zero, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  have hB : ∑ i, ∑ k, (fwdDiffD k P (x + Pi.single i 1) * openFluxD ω χ k i x -
      fwdDiffD k P x * openFluxD ω χ k i (x - Pi.single i 1)) =
      ∑ k, ∑ i, (fwdDiffD k P (x + Pi.single i 1) * openFluxD ω χ k i x -
        fwdDiffD k P x * openFluxD ω χ k i (x - Pi.single i 1)) := Finset.sum_comm
  rw [hB, Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem cast_add_single_apply (x : Vertex d) (i k : Fin d) :
    (((x + Pi.single i 1 : Vertex d) k : ℤ) : ℝ) = (x k : ℝ) + (if i = k then 1 else 0) := by
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg h, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm h)]
    simp

theorem cast_sub_single_apply (x : Vertex d) (i k : Fin d) :
    (((x - Pi.single i 1 : Vertex d) k : ℤ) : ℝ) = (x k : ℝ) - (if i = k then 1 else 0) := by
  by_cases h : i = k
  · subst h
    simp
  · rw [if_neg h, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h)]
    simp

theorem mem_supp_of_openAdjD {ω : Configuration d} {K : OpenComponent ω} {x z : Vertex d}
    (hx : x ∈ K.supp) (hadj : (openGraph ω).Adj x z) : z ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm

/-- **The corrector equation in divergence form** on `ℤ^d`: for `x` in the cluster,
`Σ_i (g_{k,i}(x - e_i) - g_{k,i}(x)) = -Δ(x_k + χ_k)(x) = 0`. -/
theorem sum_openFluxD_div_eq_zero {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
    {χ : Fin d → Vertex d → ℝ} (hχ : IsDGCorrectorD K y χ) {x : Vertex d} (hx : x ∈ K.supp)
    (k : Fin d) :
    ∑ i, (openFluxD ω χ k i (x - Pi.single i 1) - openFluxD ω χ k i x) = 0 := by
  set φ : K → ℝ := fun a => (a.val k : ℝ) + χ k a.val with hφ
  have hharm : componentLaplacian K φ ⟨x, hx⟩ = 0 := (hχ k).1.1.1 ⟨x, hx⟩
  rw [← Rigidity.Proofs.Regularity.openLaplacian_extend_eq_componentLaplacian K φ hx] at hharm
  have hcongr : openLaplacian ω (Rigidity.Section3.extend K φ) x =
      openLaplacian ω (fun z => (z k : ℝ) + χ k z) x := by
    unfold openLaplacian
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [SimpleGraph.mem_neighborFinset] at hz
    have hzK : z ∈ K.supp := mem_supp_of_openAdjD hx hz
    simp only [Rigidity.Section3.extend, dif_pos hzK, dif_pos hx, hφ]
  rw [hcongr, openLaplacian_eq_sumD] at hharm
  rw [← neg_eq_zero, ← hharm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [openFluxD, sub_add_cancel, cast_add_single_apply, cast_sub_single_apply]
  ring

/-! ### The equation of the two-scale expansion -/

/-- **Dario–Gu, (4.1)** on `ℤ^d`: the two-scale expansion
`h(t, x, y) = θ^{-1} (p̄(t, x - y) + Σ_k D_{e_k} p̄(t, · - y)(x) χ_{e_k}(x))`. -/
noncomputable def dgTwoScaleD (σ θ : ℝ) (χ : Fin d → Vertex d → ℝ) (t : ℝ) (x y : Vertex d) : ℝ :=
  θ⁻¹ * (latticeGaussianD σ t x y +
    ∑ k, fwdDiffD k (fun z => latticeGaussianD σ t z y) x * χ k x)

/-- The source term `G` of the equation of the two-scale expansion. -/
noncomputable def twoScaleSourceD (ω : Configuration d) (σ : ℝ) (χ : Fin d → Vertex d → ℝ)
    (t : ℝ) (y x : Vertex d) : ℝ :=
  (latticeGaussianTimeDerivD σ t x y -
      σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ t z y) x) +
    ∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ t z y) x * χ k x -
    ∑ i, (stepOneFD ω χ (fun z => latticeGaussianD σ t z y) i (x - Pi.single i 1) -
      stepOneFD ω χ (fun z => latticeGaussianD σ t z y) i x) -
    ∑ k, ∑ i, centeredFluxD ω σ χ k i x *
      fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ t z y) x

/-- The time derivative of the two-scale expansion. -/
theorem hasDerivAt_dgTwoScaleD_time {σ θ t : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (χ : Fin d → Vertex d → ℝ) (x y : Vertex d) :
    HasDerivAt (fun s => dgTwoScaleD σ θ χ s x y)
      (θ⁻¹ * (latticeGaussianTimeDerivD σ t x y +
        ∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ t z y) x * χ k x)) t := by
  unfold dgTwoScaleD fwdDiffD
  exact ((hasDerivAt_latticeGaussianD hσ ht x y).add
    (HasDerivAt.fun_sum fun k _ => ((hasDerivAt_latticeGaussianD hσ ht _ y).sub
      (hasDerivAt_latticeGaussianD hσ ht x y)).mul_const (χ k x))).const_mul θ⁻¹

theorem openLaplacian_const_mulD (ω : Configuration d) (c : ℝ) (u : Vertex d → ℝ)
    (x : Vertex d) : openLaplacian ω (fun z => c * u z) x = c * openLaplacian ω u x := by
  unfold openLaplacian
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Step 1 of Proposition 4.3 of Dario–Gu** on `ℤ^d`: at `x ∈ 𝒞_∞`,
`∂_t h(t, x, y) = Δ h(t, ·, y)(x) + θ^{-1} G(t, x)`. -/
theorem hasDerivAt_dgTwoScaleD_eq {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
    {χ : Fin d → Vertex d → ℝ} (hχ : IsDGCorrectorD K y χ) {σ θ t : ℝ} (hσ : 0 < σ)
    (ht : 0 < t) {x : Vertex d} (hx : x ∈ K.supp) :
    HasDerivAt (fun s => dgTwoScaleD σ θ χ s x y)
      (openLaplacian ω (fun z => dgTwoScaleD σ θ χ t z y) x +
        θ⁻¹ * twoScaleSourceD ω σ χ t y x) t := by
  refine (hasDerivAt_dgTwoScaleD_time hσ ht χ x y).congr_deriv ?_
  have hL := openLaplacian_twoScaleD ω σ χ (fun z => latticeGaussianD σ t z y) x
    (sum_openFluxD_div_eq_zero hχ hx)
  have e : (fun z => dgTwoScaleD σ θ χ t z y) = fun z => θ⁻¹ *
      (latticeGaussianD σ t z y +
        ∑ k, fwdDiffD k (fun z => latticeGaussianD σ t z y) z * χ k z) := by
    funext z
    rfl
  rw [e, openLaplacian_const_mulD, hL]
  unfold twoScaleSourceD
  ring

end Rigidity.Green.GeneralDim
