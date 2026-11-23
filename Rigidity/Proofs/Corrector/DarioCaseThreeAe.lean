import Rigidity.Proofs.Corrector.DarioCaseThree
import Rigidity.Proofs.Green.PlanarGreenColumnCorrector
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable

/-!
# Dario's identity (3.22) almost surely

The hypotheses of `edgeGrad_eq_smul_greenProj_of_liouville` other than the equation and the growth
of `v` hold almost surely on the planar infinite cluster:

* `exists_eq_const_of_sublinearLiouville`: main's Liouville theorem (`SublinearLiouville`, proved
  for `p_c(2) < p < 1` from the planar qualitative corrector input,
  `sublinearLiouville_two_of_correctorInput supercriticalBondCorrectorInputTwo_holds`) in the
  vertex form, through `componentLaplacian_restrict_eq` and `laplacian_openGraph_eq_edgeDiv`;
* `ae_sublinearOn_of_isGradOf`: almost surely every potential of an `ℓ²` field grows sublinearly on
  the infinite cluster (finite energy, `localEnergy_le_of_isGradOf`, and
  `ae_abs_sub_coarseAnchor_le_of_finiteEnergy`);
* `ae_edgeGrad_eq_smul_greenProj_of_div`, `ae_edgeGrad_eq_smul_greenProj` (Dario, (3.22)): almost
  surely, for every source `ξ` with `∇·ξ = δ_x - δ_y` (for an open edge `a`, `ξ = 1_a`) and every
  `v` with `∇·∇v = c(δ_x - δ_y)` on the infinite cluster and sublinear growth there, `∇v = c Pξ`
  on the open edges of the cluster, with `∇∇G(e, ·) = greenProj ω (1_a)`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation

/-- Main's Liouville theorem in vertex form. -/
theorem exists_eq_const_of_sublinearLiouville {ω : Configuration 2}
    (hL : ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ v : uniqueInfiniteComponent h → ℝ,
      (∀ x, componentLaplacian _ v x = 0) →
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : uniqueInfiniteComponent h,
        R ≤ Rigidity.Section5.eucl x.val → |v x| ≤ ε * Rigidity.Section5.eucl x.val) →
      ∃ c : ℝ, ∀ x, v x = c)
    (h : HasUniqueInfiniteOpenComponent ω) (f : Vertex 2 → ℝ)
    (hf : ∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω f) z = 0)
    (hfs : SublinearOn (uniqueInfiniteComponent h).supp f) :
    ∃ k : ℝ, ∀ z ∈ (uniqueInfiniteComponent h).supp, f z = k := by
  obtain ⟨c, hc⟩ := hL h (fun x => f x.val)
    (fun x => by
      rw [componentLaplacian_restrict_eq, laplacian_openGraph_eq_edgeDiv]
      exact hf x.val x.2)
    (fun ε hε => by
      obtain ⟨R, hR⟩ := hfs ε hε
      exact ⟨R, fun x hx => hR x.val x.2 hx⟩)
  exact ⟨c, fun z hz => hc ⟨z, hz⟩⟩

/-- **Almost surely the potentials of `ℓ²` fields grow sublinearly on the infinite cluster.** -/
theorem ae_sublinearOn_of_isGradOf {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (η : EdgeField)
      (W : Vertex 2 → ℝ), IsGradOf ω η W → SublinearOn (uniqueInfiniteComponent h).supp W := by
  filter_upwards [ae_abs_sub_coarseAnchor_le_of_finiteEnergy hpc] with ω hω
  intro h η W hW ε hε
  obtain ⟨R₀, hR₀⟩ := hω W (2 * ‖η‖ ^ 2) (localEnergy_le_of_isGradOf ω hW) (ε / 4)
    (by positivity)
  set K := |W (planarCoarseAnchor ω 0)| with hK
  refine ⟨max (max (R₀ : ℝ) 1) (4 * K / ε), fun z hz hR => ?_⟩
  set e := Rigidity.Section5.eucl z with he
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
    have h1 := Rigidity.Corrector.abs_coord_le_norm z i
    have h2 : |((z i : ℤ) : ℝ)| ≤ (R : ℝ) := h1.trans (Nat.le_ceil e)
    exact_mod_cast h2
  have hinf : ((openGraph ω).connectedComponentMk z).supp.Infinite :=
    (mem_uniqueInfiniteComponent_iff h z).1 hz
  have hb := hR₀ R hRR₀ z hzR hinf
  have htri : |W z| ≤ |W z - W (planarCoarseAnchor ω 0)| + K := by
    have := abs_sub_abs_le_abs_sub (W z) (W (planarCoarseAnchor ω 0))
    linarith
  have hε4 : 0 ≤ ε / 4 := by positivity
  calc |W z| ≤ ε / 4 * R + ε / 4 * e := by linarith
    _ ≤ ε / 4 * (e + 1) + ε / 4 * e := by gcongr
    _ ≤ ε * e := by nlinarith

/-- **Dario, (3.22)**, almost surely, for any source field `ξ` with `∇·ξ = δ_x - δ_y`: for every
`v` with `∇·∇v = c(δ_x - δ_y)` on the infinite cluster and sublinear growth there, `∇v = c Pξ` on
the open edges of the cluster. -/
theorem ae_edgeGrad_eq_smul_greenProj_of_div {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (ξ : EdgeField)
      (x y : Vertex 2), (∀ z, edgeDiv ω ξ z = (if z = x then 1 else 0) - (if z = y then 1 else 0)) →
      ∀ (v : Vertex 2 → ℝ) (c : ℝ),
        (∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω v) z =
          c * ((if z = x then 1 else 0) - (if z = y then 1 else 0))) →
        SublinearOn (uniqueInfiniteComponent h).supp v →
        ∀ b : LatticeEdge, EdgeOpen ω b → b.1 ∈ (uniqueInfiniteComponent h).supp →
          edgeGrad ω v b = c * greenProj ω ξ b := by
  filter_upwards [Rigidity.Green.sublinearLiouville_two_of_correctorInput
      Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds p hpc hp1,
    ae_sublinearOn_of_isGradOf hpc] with ω hL hW
  intro h ξ x y hξ v c hv hvs b hb hb1
  have hb2 : edgeHead b ∈ (uniqueInfiniteComponent h).supp :=
    (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hb1 hb
  exact edgeGrad_eq_smul_greenProj_of_div ω hξ
    (fun f hf hfs => exists_eq_const_of_sublinearLiouville hL h f hf hfs) hv hvs
    (fun W hWg => hW h _ W hWg) hb hb1 hb2

/-- **Dario, (3.22)**, almost surely, for an open edge `a`: `∇v = c ∇∇G(e, ·)` with
`∇∇G(e, ·) = greenProj ω (1_a)`. -/
theorem ae_edgeGrad_eq_smul_greenProj {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ a : LatticeEdge,
      EdgeOpen ω a → ∀ (v : Vertex 2 → ℝ) (c : ℝ),
        (∀ z ∈ (uniqueInfiniteComponent h).supp, edgeDiv ω (edgeGrad ω v) z =
          c * ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0))) →
        SublinearOn (uniqueInfiniteComponent h).supp v →
        ∀ b : LatticeEdge, EdgeOpen ω b → b.1 ∈ (uniqueInfiniteComponent h).supp →
          edgeGrad ω v b = c * greenProj ω (lp.single 2 a 1) b := by
  filter_upwards [ae_edgeGrad_eq_smul_greenProj_of_div hpc hp1] with ω hω
  intro h a ha
  exact hω h _ a.1 (edgeHead a) (edgeDiv_single ω ha)

end Rigidity.Corrector
