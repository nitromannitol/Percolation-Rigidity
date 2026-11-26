import Rigidity.Proofs.Corrector.GeneralCaseThree
import Rigidity.Proofs.S3.SublinearLiouville
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds

/-!
# Dario's identity (3.22) almost surely on `ℤᵈ`

The hypotheses of `edgeGrad_eq_smul_greenProj_of_div` other than the equation and the growth of
`v` hold almost surely on the infinite cluster of `ℤᵈ`, `d ≥ 2` (the argument of the planar file
`DarioCaseThreeAe`):

* `exists_eq_const_of_sublinearLiouville`: the Liouville theorem
  (`Rigidity.Proofs.S3.sublinearLiouvilleStep`, from the order-zero regularity of Armstrong and
  Dario, `armstrongDarioOrderZero_holds`) in the vertex form, through
  `componentSlopeAsymptotics_zero_of_sublinearOn`, `componentLaplacian_restrict_eq` and
  `laplacian_openGraph_eq_edgeDiv`;
* `ae_sublinearOn_of_isGradOf`: almost surely every potential of an `ℓ²` field grows sublinearly on
  the infinite cluster (finite energy, `localEnergy_le_of_isGradOf`, and
  `ae_abs_sub_partitionAnchor_le_of_finiteEnergy`);
* `ae_edgeGrad_eq_smul_greenProj_of_div`, `ae_edgeGrad_eq_smul_greenProj` (Dario, (3.22)): almost
  surely, for every source `ξ` with `∇·ξ = δ_x - δ_y` (for an open edge `a`, `ξ = 1_a`) and every
  `v` with `∇·∇v = c(δ_x - δ_y)` on the infinite cluster and sublinear growth there, `∇v = c Pξ`
  on the open edges of the cluster, with `∇∇G(e, ·) = greenProj ω (1_a)`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- Sublinear growth on the vertices of a component gives the slope asymptotics of slope zero. -/
theorem componentSlopeAsymptotics_zero_of_sublinearOn {ω : Configuration d}
    (C : OpenComponent ω) {f : Vertex d → ℝ} (hf : SublinearOn C.supp f) :
    componentSlopeAsymptotics C 0 (fun x => f x.val) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := hf (ε / 2) (by positivity)
  set F := componentEuclideanBall C 0 R₁ with hF
  set M := ∑ x ∈ F, |f x.val| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨max 1 (M / ε), lt_of_lt_of_le one_pos (le_max_left _ _), fun R hR x hx => ?_⟩
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRM : M / ε ≤ R := (le_max_right _ _).trans hR
  have hMR : M ≤ ε * R := by
    rw [div_le_iff₀ hε] at hRM
    linarith
  simp only [componentSlope, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
  have hx' : ‖latticeEuclideanEmbedding x.val‖ < R := by
    have := (mem_componentEuclideanBall C 0 R x).1 hx
    rwa [latticeEuclideanEmbedding_zero, dist_zero_right] at this
  by_cases hxR : R₁ ≤ ‖latticeEuclideanEmbedding x.val‖
  · have h1 := hR₁ x.val x.2 hxR
    have h2 : ε / 2 * ‖latticeEuclideanEmbedding x.val‖ ≤ ε / 2 * R :=
      mul_le_mul_of_nonneg_left hx'.le (by positivity)
    have h3 : ε / 2 * R ≤ ε * R := by nlinarith
    linarith
  · have hxF : x ∈ F := by
      rw [hF, mem_componentEuclideanBall, latticeEuclideanEmbedding_zero, dist_zero_right]
      exact lt_of_not_ge hxR
    have h1 : |f x.val| ≤ M :=
      Finset.single_le_sum (f := fun y : C => |f y.val|) (fun _ _ => abs_nonneg _) hxF
    linarith

/-- The Liouville theorem in vertex form. -/
theorem exists_eq_const_of_sublinearLiouville {ω : Configuration d}
    (hL : ∀ (h : HasUniqueInfiniteOpenComponent ω) (v : uniqueInfiniteComponent h → ℝ),
      (∀ x, componentLaplacian (uniqueInfiniteComponent h) v x = 0) →
      componentSlopeAsymptotics (uniqueInfiniteComponent h) 0 v → ∃ c : ℝ, ∀ x, v x = c)
    (h : HasUniqueInfiniteOpenComponent ω) (f : Vertex d → ℝ)
    (hf : ∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω f) z = 0)
    (hfs : SublinearOn (uniqueInfiniteComponent h).supp f) :
    ∃ k : ℝ, ∀ z ∈ (uniqueInfiniteComponent h).supp, f z = k := by
  obtain ⟨c, hc⟩ := hL h (fun x => f x.val)
    (fun x => by
      rw [componentLaplacian_restrict_eq, laplacian_openGraph_eq_edgeDiv]
      exact hf x.val x.2)
    (componentSlopeAsymptotics_zero_of_sublinearOn _ hfs)
  exact ⟨c, fun z hz => hc ⟨z, hz⟩⟩

/-- **Almost surely the potentials of `ℓ²` fields grow sublinearly on the infinite cluster.** -/
theorem ae_sublinearOn_of_isGradOf [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (η : EdgeField d)
      (W : Vertex d → ℝ), IsGradOf ω η W → SublinearOn (uniqueInfiniteComponent h).supp W := by
  filter_upwards [ae_abs_sub_partitionAnchor_le_of_finiteEnergy hd hpc] with ω hω
  intro h η W hW ε hε
  obtain ⟨R₀, hR₀⟩ := hω W (2 * ‖η‖ ^ 2) (localEnergy_le_of_isGradOf ω hW) (ε / 4)
    (by positivity)
  set K := |W (partitionAnchor ω 0)| with hK
  refine ⟨max (max (R₀ : ℝ) 1) (4 * K / ε), fun z hz hR => ?_⟩
  set e := ‖latticeEuclideanEmbedding z‖ with he
  have he1 : 1 ≤ e := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have hR0 : (R₀ : ℝ) ≤ e := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hKe : 4 * K / ε ≤ e := (le_max_right _ _).trans hR
  have hK' : K ≤ ε / 4 * e := by
    rw [div_le_iff₀ hε] at hKe
    linarith
  set R : ℕ := ⌈e⌉₊ with hRdef
  have hRe : (R : ℝ) ≤ e + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hRR₀ : R₀ ≤ R := Nat.cast_le.1 (hR0.trans (Nat.le_ceil e))
  have hzR : ∀ i, |z i| ≤ R := by
    intro i
    have h1 := abs_coord_le_norm z i
    have h2 : |((z i : ℤ) : ℝ)| ≤ (R : ℝ) := h1.trans (Nat.le_ceil e)
    exact_mod_cast h2
  have hinf : ω ∈ infiniteComponentEvent z := (mem_uniqueInfiniteComponent_iff h z).1 hz
  have hb := hR₀ R hRR₀ z hzR hinf
  have htri : |W z| ≤ |W z - W (partitionAnchor ω 0)| + K := by
    have := abs_sub_abs_le_abs_sub (W z) (W (partitionAnchor ω 0))
    linarith
  have hε4 : 0 ≤ ε / 4 := by positivity
  calc |W z| ≤ ε / 4 * R + ε / 4 * e := by linarith
    _ ≤ ε / 4 * (e + 1) + ε / 4 * e := by gcongr
    _ ≤ ε * e := by nlinarith

/-- **Dario, (3.22)**, almost surely, for any source field `ξ` with `∇·ξ = δ_x - δ_y`: for every
`v` with `∇·∇v = c(δ_x - δ_y)` on the infinite cluster and sublinear growth there, `∇v = c Pξ` on
the open edges of the cluster. -/
theorem ae_edgeGrad_eq_smul_greenProj_of_div [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (ξ : EdgeField d)
      (x y : Vertex d), (∀ z, edgeDiv ω ξ z = (if z = x then 1 else 0) - (if z = y then 1 else 0)) →
      ∀ (v : Vertex d → ℝ) (c : ℝ),
        (∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω v) z =
          c * ((if z = x then 1 else 0) - (if z = y then 1 else 0))) →
        SublinearOn (uniqueInfiniteComponent h).supp v →
        ∀ b : LatticeEdge d, EdgeOpen ω b → b.1 ∈ (uniqueInfiniteComponent h).supp →
          edgeGrad ω v b = c * greenProj ω ξ b := by
  filter_upwards [Rigidity.Proofs.S3.sublinearLiouvilleStep hd p hpc hp1
      Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds,
    ae_sublinearOn_of_isGradOf hd hpc] with ω hL hW
  intro h ξ x y hξ v c hv hvs b hb hb1
  have hb2 : edgeHead b ∈ (uniqueInfiniteComponent h).supp :=
    (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hb1 hb
  exact edgeGrad_eq_smul_greenProj_of_div ω hξ
    (fun f hf hfs => exists_eq_const_of_sublinearLiouville hL h f hf hfs) hv hvs
    (fun W hWg => hW h _ W hWg) hb hb1 hb2

/-- **Dario, (3.22)**, almost surely, for an open edge `a`: `∇v = c ∇∇G(e, ·)` with
`∇∇G(e, ·) = greenProj ω (1_a)`. -/
theorem ae_edgeGrad_eq_smul_greenProj [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ a : LatticeEdge d,
      EdgeOpen ω a → ∀ (v : Vertex d → ℝ) (c : ℝ),
        (∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω v) z =
          c * ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0))) →
        SublinearOn (uniqueInfiniteComponent h).supp v →
        ∀ b : LatticeEdge d, EdgeOpen ω b → b.1 ∈ (uniqueInfiniteComponent h).supp →
          edgeGrad ω v b = c * greenProj ω (lp.single 2 a 1) b := by
  filter_upwards [ae_edgeGrad_eq_smul_greenProj_of_div hd hpc hp1] with ω hω
  intro h a ha
  exact hω h _ a.1 (edgeHead a) (edgeDiv_single ω ha)

end Rigidity.Corrector.GeneralDim
