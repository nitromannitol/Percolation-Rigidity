import Rigidity.Proofs.Cluster.PlanarBoundN

/-!
# The minimal scales and Proposition 5.13 in the forms used in Section 6, in dimension two

Two consequences of `planarMinimalScales_holds` and `exists_planarBoundN_general`, stated in the
form of the inputs of the proof of Theorem 1 of Armstrong and Dario in dimension two:

* `planarMinimalScales_partition_holds`: for every `t ≥ 1` a minimal scale `𝓜_t ≤ O_s(C)` of the
  planar partition with `|□_m|⁻¹ ∑_{x ∈ □_m} size(□_𝒫(x))^t ≤ C` and
  `size(□_𝒫(x)) ≤ 3^{2m/(2+t)}` on `□_m` whenever `𝓜_t ≤ 3ᵐ` (both bounds of (2.12));
* `planarMesoscopicConvergence_holds`: Proposition 5.13 on the triadic subcubes of `□_m` of scale
  `⌈m/8⌉`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

/-- **Both bounds of (2.12) for the planar partition** (Armstrong and Dario, Proposition 2.4,
dimension two, `p > p_c(2)`). -/
theorem planarMinimalScales_partition_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ t : ℝ, 1 ≤ t → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, M ω ≤ 3 ^ m →
          (∑ x ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
              ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t) / 9 ^ m ≤ C ∧
            ∀ x ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
              (3 : ℝ) ^ (planarPartCube ω x).scale ≤ (3 : ℝ) ^ (2 * (m : ℝ) / (2 + t)) := by
  obtain ⟨A₀, sR, -, hmom⟩ := planarMinimalScales_holds hpc
  intro t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨K, r, θ, hK, hr, hθ, M, hMm, hM0, hMos, hM⟩ :=
    hmom t ht0 (2 / (2 + t)) (by positivity)
  refine ⟨r, max K θ, hr, lt_of_lt_of_le hθ (le_max_right _ _), M, hMm, hM0,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hr hθ (le_max_right _ _) hMm hMos, ?_⟩
  filter_upwards [hM] with ω hω m hm
  obtain ⟨-, -, h3, h4, -, -⟩ := hω m hm
  have hc : ((cube m (0 : Vertex 2)).card : ℝ) = 9 ^ m := by
    rw [card_cube, ← pow_mul, mul_comm, pow_mul]; norm_num
  refine ⟨?_, fun x hx => ?_⟩
  · have e : cube m (0 : Vertex 2) = (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices :=
      cube_zero_eq_vertices m
    rw [← e, div_le_iff₀ (by positivity)]
    rw [hc] at h3
    exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h := h4 x (mem_cube_zero_iff.2 hx)
    rw [three_rpow_natCast_mul] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    ring

/-- **Proposition 5.13 on the triadic cubes of scale `⌈m/8⌉`** (Armstrong and Dario,
Definition 5.12, Proposition 5.13 and (6.10)-(6.11), dimension two, `p > p_c(2)`). -/
theorem planarMesoscopicConvergence_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ s α C : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧
      ∃ N : Configuration 2 → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond 2 p N s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, N ω ≤ 3 ^ m →
          ∀ T : TriadicCube 2, T.scale = (m + 7) / 8 →
            T.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices → ∀ q ξ : Fin 2 → ℝ,
              |planarMu ω T q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
                  C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(α * m)) ∧
                |planarNu ω T ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
                  C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(α * m)) := by
  obtain ⟨K, β, r, θ, hK, hβ, hr, hθ, N, hNm, hN0, hNos, hN⟩ :=
    exists_planarBoundN_general hpc (L := 8) (by norm_num) (fun m => (m + 7) / 8)
      (fun m => ⟨by omega, by omega⟩)
  refine ⟨r, β / 8, max K θ, hr, by positivity, lt_of_lt_of_le hθ (le_max_right _ _), N, hNm,
    hN0, Rigidity.Proofs.S2.IsOsBond.mono_scale hr hθ (le_max_right _ _) hNm hNos, ?_⟩
  filter_upwards [hN] with ω hω m hm T hT hTU q ξ
  obtain ⟨-, -, hμb, hνb⟩ := ((hω m hm).1 T hT hTU).mono_scale (L := 8) (m := m) hK hβ
    (by norm_num) (by rw [hT]; omega)
  have he : (3 : ℝ) ^ (-(m : ℝ) * (β / ((8 : ℕ) : ℝ))) = (3 : ℝ) ^ (-(β / 8 * m)) := by
    congr 1; push_cast; ring
  rw [he] at hμb hνb
  refine ⟨(hμb q).trans ?_, (hνb ξ).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (by positivity)

end Rigidity.Proofs.Cluster
