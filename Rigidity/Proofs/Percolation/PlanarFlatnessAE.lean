import Rigidity.Proofs.Percolation.PlanarFlatnessNu
import Rigidity.Proofs.Percolation.PlanarCoarseEnergyMajorant

/-!
# Lemma 5.8 of Armstrong and Dario without the energy inputs

The flatness bounds (5.32), (5.33) of `PlanarFlatnessMu`, `PlanarFlatnessNu` with the energy bounds
(4.24), (4.25) discharged by their measurable majorants (`PlanarCoarseEnergyMajorant`): the
majorants of the flatness errors now hold almost surely, and the inputs are Lemma 5.7 and
Lemma 5.5 only.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (cube centers subcube gradSum gradNormSq finsetMean affineFun)

/-- **Flatness of the coarsened minimizers of `μ`** (Armstrong and Dario, Lemma 5.8, display
(5.32), in dimension two), from Lemmas 5.7 and 5.5 and the energy bound (4.24). -/
theorem exists_planarMuFlatness_majorant_ae {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h57 : PlanarWeakConvergence p)
    (h55 : PlanarRestrictQuadCoarsenMu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin 2 → ℝ),
      ∃ Φ : Configuration 2 → ℝ, AEMeasurable Φ (latticeBondLaw 2 p) ∧ (∀ ω, 0 ≤ Φ ω) ∧
        (∀ᵐ ω ∂(latticeBondLaw 2 p), planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q))
            (planarAhomInvFinite p n *ᵥ q) ≤ Φ ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Φ ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (q 0 ^ 2 + q 1 ^ 2) * (9 : ℝ) ^ n *
            ((3 : ℝ) ^ (-(n : ℝ) / 10) +
              ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨C57, hC57, h57⟩ := h57
  obtain ⟨C55, hC55, h55⟩ := h55
  obtain ⟨Cg, hCg, hcg⟩ := exists_coarseEnergyMu_majorant hpc (δ := 1 / 10) (by norm_num)
  obtain ⟨CM, hCM, hpw⟩ := exists_planarMuFlatness_le_pointwise
  obtain ⟨K, hK, hKb⟩ := exists_abs_planarAhomInvFinite_le hpc
  obtain ⟨CA, hCA, hA⟩ := exists_sum_sq_planarAhomInvFinite_sub_le hpc
  refine ⟨81 * (CM * (Cg + 4 * K ^ 2)) +
    9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2)) +
    9 * (3 * CM * (C55 + C57) + CM * (3 * CA + 4 * K ^ 2)), by positivity, fun n q => ?_⟩
  obtain ⟨F, hFm, hF0, hFae, hFint⟩ := hcg ⟨n + 1, 0⟩ q
  have hQ0 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  have hΞQ := sum_sq_mulVec_le (hKb n) q
  have h10a : 9 * (n + 1) ≤ 10 * ((9 * (n + 1) + 9) / 10) := by omega
  have h10b : 10 * ((9 * (n + 1) + 9) / 10) ≤ 9 * (n + 1) + 9 := by omega
  have hn₀m : (9 * (n + 1) + 9) / 10 ≤ n + 1 := by omega
  have hn₀2 : ((n + 1 : ℕ) : ℝ) / 2 ≤ (((9 * (n + 1) + 9) / 10 : ℕ) : ℝ) := by
    have : ((9 * (n + 1) : ℕ) : ℝ) ≤ ((10 * ((9 * (n + 1) + 9) / 10) : ℕ) : ℝ) := by
      exact_mod_cast h10a
    push_cast at this ⊢
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsA : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      9 * (⟨n + 1, 0⟩ : TriadicCube 2).scale ≤ 10 * k ∧ k < (⟨n + 1, 0⟩ : TriadicCube 2).scale :=
    fun k hk => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
      exact ⟨by change 9 * (n + 1) ≤ 10 * k; omega, h2⟩
  have hne : ∀ k, (subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).Nonempty := fun k =>
    ⟨scaleCube k 0, Finset.mem_image_of_mem _
      (((⟨n + 1, 0⟩ : TriadicCube 2).mem_toIntegerCube_vertices 0).2 (by
        intro i
        change |2 * ((0 : Vertex 2) i - (3 : ℤ) ^ (n + 1) * (0 : Vertex 2) i)| < (3 : ℤ) ^ (n + 1)
        simp))⟩
  have mF : ∀ k, ∀ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, AEMeasurable (fun ω =>
      ∑ j : Fin 2, (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
      (latticeBondLaw 2 p) :=
    fun k V _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      ((aemeasurable_planarMuGradAvg hpc V q j).sub aemeasurable_const).pow_const 2
  have IB : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ∫⁻ ω, ENNReal.ofReal ((((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (C57 * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k _
    refine lintegral_ofReal_avg_le (hne k) (fun V _ ω => Finset.sum_nonneg fun _ _ =>
      sq_nonneg _) (mF k) fun V hV => ?_
    have hVs : V.scale = k := scale_of_mem_subcubesAt hV
    have h := h57 V q
    rw [hVs] at h
    exact h
  obtain ⟨Φ, hΦm, hΦ0, hXΦ, hΦint⟩ := exists_majorant_of_le_ae (μ := latticeBondLaw 2 p)
    (X := fun ω => planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarMuMinimizer ω ⟨n + 1, 0⟩ q)) (planarAhomInvFinite p n *ᵥ q))
    (f₀ := F)
    (f := fun k ω => planarMuRestrictError ω ⟨n + 1, 0⟩ k q)
    (g := fun k ω => (((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, ∑ j : Fin 2,
          (planarMuGradAvg ω V q j - (planarAhomInvFinite p k *ᵥ q) j) ^ 2)
    (s := Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1))
    (a₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) *
        ((planarAhomInvFinite p n *ᵥ q) 0 ^ 2 + (planarAhomInvFinite p n *ᵥ q) 1 ^ 2) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (3 * ∑ j : Fin 2,
            ((planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2 +
          ((9 : ℝ) ^ k)⁻¹ *
            ((planarAhomInvFinite p n *ᵥ q) 0 ^ 2 + (planarAhomInvFinite p n *ᵥ q) 1 ^ 2)))
    (b₀ := Cg * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ ((1 / 10 : ℝ) * (((n + 1 : ℕ) : ℕ) : ℝ)))
    (bf := fun k => C55 * (q 0 ^ 2 + q 1 ^ 2) *
      (∑ l ∈ Finset.Ico k (n + 1), planarTau p l + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => C57 * (q 0 ^ 2 + q 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (by positivity) (fun k _ => by positivity)
    (add_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity))))
    hF0 (fun k _ ω => planarMuRestrictError_nonneg ω _ k q)
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    hFm.aemeasurable (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 q).1)
    (fun k _ => aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun V hV => mF k V hV))
    (by
      filter_upwards [hFae] with ω hω
      refine (hpw (n + 1) ((9 * (n + 1) + 9) / 10) hn₀2 hn₀m ω q (planarAhomInvFinite p n *ᵥ q)
        (fun k => planarAhomInvFinite p k *ᵥ q)).trans ?_
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hω (by positivity)) le_rfl) le_rfl)
    hFint (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 q).2) IB
    (by positivity)
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun l _ =>
      planarTau_nonneg p l) (by positivity)))
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (planarTau_nonneg p k) (by positivity)))
  refine ⟨Φ, hΦm, hΦ0, hXΦ, hΦint.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  refine planarFlatness_arith (τ := planarTau p) (planarTau_nonneg p) hCM hCg hCA hC55 hC57 hQ0
    (by positivity) hΞQ (m := n + 1) (n := n) rfl h10b (Cc := fun k =>
      ∑ j : Fin 2, ((planarAhomInvFinite p k *ᵥ q) j - (planarAhomInvFinite p n *ᵥ q) j) ^ 2) ?_
  intro k hk
  have hkn : k ≤ n := by have := (Finset.mem_Ico.1 hk).2; omega
  refine (hA k n hkn q).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine add_le_add ?_ le_rfl
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
    fun l _ _ => planarTau_nonneg p l

/-- **Flatness of the coarsened maximizers of `ν`** (Armstrong and Dario, Lemma 5.8, display
(5.33), in dimension two), from Lemma 5.5 and the energy bound (4.25). -/
theorem exists_planarNuFlatness_majorant_ae {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (h55 : PlanarRestrictQuadCoarsenNu p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ξ : Fin 2 → ℝ),
      ∃ Φ : Configuration 2 → ℝ, AEMeasurable Φ (latticeBondLaw 2 p) ∧ (∀ ω, 0 ≤ Φ ω) ∧
        (∀ᵐ ω ∂(latticeBondLaw 2 p), planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤ Φ ω) ∧
        ∫⁻ ω, ENNReal.ofReal (Φ ω) ∂(latticeBondLaw 2 p) ≤
          ENNReal.ofReal (C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (9 : ℝ) ^ n *
            ((3 : ℝ) ^ (-(n : ℝ) / 10) +
              ((3 : ℝ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1), (3 : ℝ) ^ k * planarTau p k)) := by
  obtain ⟨Cn, hCn, hNab⟩ := exists_nablaAffineMajorant_le hpc
  obtain ⟨C55, hC55, h55⟩ := h55
  obtain ⟨Cg, hCg, hcg⟩ := exists_coarseEnergyNu_majorant hpc (δ := 1 / 10) (by norm_num)
  obtain ⟨CM, hCM, hpw⟩ := exists_planarNuFlatness_le_pointwise
  refine ⟨81 * (CM * (Cg + 4 * 1 ^ 2)) +
    9 * (3 * CM * (C55 + Cn) + CM * (3 * 0 + 4 * 1 ^ 2)) +
    9 * (3 * CM * (C55 + Cn) + CM * (3 * 0 + 4 * 1 ^ 2)), by positivity, fun n ξ => ?_⟩
  obtain ⟨F, hFm, hF0, hFae, hFint⟩ := hcg ⟨n + 1, 0⟩ ξ
  have hQ0 : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
  have hΞQ : ξ 0 ^ 2 + ξ 1 ^ 2 ≤ 4 * 1 ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by linarith
  have h10a : 9 * (n + 1) ≤ 10 * ((9 * (n + 1) + 9) / 10) := by omega
  have h10b : 10 * ((9 * (n + 1) + 9) / 10) ≤ 9 * (n + 1) + 9 := by omega
  have hn₀m : (9 * (n + 1) + 9) / 10 ≤ n + 1 := by omega
  have hn₀2 : ((n + 1 : ℕ) : ℝ) / 2 ≤ (((9 * (n + 1) + 9) / 10 : ℕ) : ℝ) := by
    have : ((9 * (n + 1) : ℕ) : ℝ) ≤ ((10 * ((9 * (n + 1) + 9) / 10) : ℕ) : ℝ) := by
      exact_mod_cast h10a
    push_cast at this ⊢
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsA : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      9 * (⟨n + 1, 0⟩ : TriadicCube 2).scale ≤ 10 * k ∧ k < (⟨n + 1, 0⟩ : TriadicCube 2).scale :=
    fun k hk => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
      exact ⟨by change 9 * (n + 1) ≤ 10 * k; omega, h2⟩
  have hne : ∀ k, (subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).Nonempty := fun k =>
    ⟨scaleCube k 0, Finset.mem_image_of_mem _
      (((⟨n + 1, 0⟩ : TriadicCube 2).mem_toIntegerCube_vertices 0).2 (by
        intro i
        change |2 * ((0 : Vertex 2) i - (3 : ℤ) ^ (n + 1) * (0 : Vertex 2) i)| < (3 : ℤ) ^ (n + 1)
        simp))⟩
  have IB : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ∫⁻ ω, ENNReal.ofReal ((((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ)
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (Cn * (ξ 0 ^ 2 + ξ 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4))) := by
    intro k _
    refine lintegral_ofReal_avg_le (hne k) (fun V _ ω => nablaAffineMajorant_nonneg V ξ ω)
      (fun V _ => (measurable_nablaAffineMajorant V ξ).aemeasurable) fun V hV => ?_
    have hVs : V.scale = k := scale_of_mem_subcubesAt hV
    refine (hNab V ξ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hVs]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (planarTau_nonneg p k))
      (by positivity)
  have hX : ∀ ω, planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ ≤
      (CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10)) *
        coarseEnergy ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
        (3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k) *
        (planarNuRestrictError ω ⟨n + 1, 0⟩ k ξ +
          ((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ)⁻¹ *
            ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ) +
      (CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) * (ξ 0 ^ 2 + ξ 1 ^ 2) +
        ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
          (3 * ∑ j : Fin 2, (ξ j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2))) := by
    intro ω
    refine (hpw (n + 1) ((9 * (n + 1) + 9) / 10) hn₀2 hn₀m ω ξ ξ (fun _ => ξ)).trans ?_
    refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)) le_rfl
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun V _ => le_nablaAffineMajorant V ξ ω)
      (by positivity)
  obtain ⟨Φ, hΦm, hΦ0, hXΦ, hΦint⟩ := exists_majorant_of_le_ae (μ := latticeBondLaw 2 p)
    (X := fun ω => planarFlatnessError ⟨n + 1, 0⟩
      (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ ξ)) ξ)
    (f₀ := F)
    (f := fun k ω => planarNuRestrictError ω ⟨n + 1, 0⟩ k ξ)
    (g := fun k ω => (((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k).card : ℝ))⁻¹ *
        ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) k, nablaAffineMajorant ω V ξ)
    (s := Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1))
    (a₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10))
    (a := fun k => 3 * CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k)
    (c₀ := CM * (9 : ℝ) ^ ((9 * (n + 1) + 9) / 10) * (ξ 0 ^ 2 + ξ 1 ^ 2) +
      ∑ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), CM * (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ k *
        (3 * ∑ j : Fin 2, (ξ j - ξ j) ^ 2 + ((9 : ℝ) ^ k)⁻¹ * (ξ 0 ^ 2 + ξ 1 ^ 2)))
    (b₀ := Cg * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ ((1 / 10 : ℝ) * (((n + 1 : ℕ) : ℕ) : ℝ)))
    (bf := fun k => C55 * (ξ 0 ^ 2 + ξ 1 ^ 2) *
      (∑ l ∈ Finset.Ico k (n + 1), planarTau p l + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (bg := fun k => Cn * (ξ 0 ^ 2 + ξ 1 ^ 2) * (planarTau p k + (3 : ℝ) ^ (-(k : ℝ) / 4)))
    (by positivity) (fun k _ => by positivity)
    (add_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (by positivity))))
    hF0
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (fun k _ ω => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun V _ => nablaAffineMajorant_nonneg V ξ ω))
    hFm.aemeasurable (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 ξ).1)
    (fun k _ => aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun V _ =>
      (measurable_nablaAffineMajorant V ξ).aemeasurable))
    (by
      filter_upwards [hFae] with ω hω
      refine (hX ω).trans ?_
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hω (by positivity)) le_rfl) le_rfl)
    hFint (fun k hk => (h55 ⟨n + 1, 0⟩ k (hsA k hk).1 (hsA k hk).2 ξ).2) IB
    (by positivity)
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (Finset.sum_nonneg fun l _ =>
      planarTau_nonneg p l) (by positivity)))
    (fun k _ => mul_nonneg (by positivity) (add_nonneg (planarTau_nonneg p k) (by positivity)))
  refine ⟨Φ, hΦm, hΦ0, hXΦ, hΦint.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  refine planarFlatness_arith (τ := planarTau p) (planarTau_nonneg p) hCM hCg le_rfl hC55 hCn hQ0
    hQ0 hΞQ (m := n + 1) (n := n) rfl h10b (Cc := fun _ => ∑ j : Fin 2, (ξ j - ξ j) ^ 2) ?_
  intro k _
  simp

end Rigidity.Percolation
