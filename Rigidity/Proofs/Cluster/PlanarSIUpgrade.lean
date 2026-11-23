import Rigidity.Proofs.Cluster.PlanarSubcubeIndex
import Rigidity.Proofs.Cluster.PlanarSIStepTwo

/-!
# Lemma 5.11 of Armstrong and Dario in dimension two: the tail of `ρ(□_m)`

Steps 1 and 3 of the proof of Lemma 5.11 (`l.SIupgrade`), assembled with Step 2
(`planar_SIupgrade_step2`). For the cube `U = □_{n+3+j}` and its subcubes `V` of scale `n`, off
three events

* the reach of the planar partition exceeds `3^ℓ` somewhere on `U` (probability at most
  `9^{n+3+j} · 2 exp(-3^ℓ/θ)`), which gives the bound `ρ(V) ≤ C₁(ℓ)` of Step 1 and the
  deterministic errors of the subadditivity (5.47) (`planarRho_le_avg_of_planarReachLe`);
* some subcube is not in the good event of the stationary local versions (probability at most
  `9^{3+j} · 2 C exp(-c 3ⁿ)`), so that `ρ(V) = ρ_stat(V) ∧ C₁` on every subcube;
* the Chernoff event of Step 2 with the threshold `t = 2 (e - 1) (C + 1) (1 + C₁) 3^{-nα}`
  (probability at most `729 exp(-9ʲ 3^{-nα})`),

`ρ(U) ≤ t + K (ℓ + 1) 531441^ℓ 3^{-n/2}` (`exists_planarRho_tail`). Armstrong and Dario take a
constant `C₁` and remove the event `ρ(V) > C₁` through the minimal scales; here `C₁` grows like
`81^ℓ` and the event is that of the reach.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- The bound `C₁(ℓ)` of `ρ` on the subcubes, on the event that the reach is at most `3^ℓ`. -/
noncomputable def planarRhoCap (S : ℝ) (ℓ : ℕ) : ℝ := 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S)

/-- The threshold of Lemma 5.11 for `ρ(□_{n+3+j})`. -/
noncomputable def planarRhoThreshold (α C S : ℝ) (n ℓ : ℕ) : ℝ :=
  2 * (Real.exp 1 - 1) * (C + 1) * (1 + planarRhoCap S ℓ) * (3 : ℝ) ^ (-(n : ℝ) * α) +
    2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (ℓ + 1) * 531441 ^ ℓ / Real.sqrt ((3 : ℝ) ^ n)

theorem card_subcubesAt_index (n j : ℕ) :
    ((subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n).card : ℝ) =
      ((⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) *
        ((⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) := by
  have h := sum_subcubesAt_eq_sum_sum n j (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- **Lemma 5.11 of Armstrong and Dario, Steps 1 to 3** (dimension two, `p > p_c(2)`): the tail of
`ρ(□_{n+3+j})` at the threshold `planarRhoThreshold`, together with the event that the reach is
at most `3^ℓ` on the cube. -/
theorem exists_planarRho_tail {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C θ c : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ 0 < θ ∧ 0 < c ∧ ∃ C₂ : ℝ≥0∞, C₂ ≠ ∞ ∧
      ∀ {S : ℝ}, 0 ≤ S →
      (∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
        S * (|v 0| + |v 1|)) →
      ∀ n j ℓ : ℕ, ℓ ≤ n →
        latticeBondLaw 2 p {ω | ¬ (PlanarReachLe ω ⟨n + 3 + j, 0⟩ ℓ ∧
            planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarRhoThreshold α C S n ℓ)} ≤
          ENNReal.ofReal ((9 : ℝ) ^ (n + 3 + j) * (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ)))) +
            ENNReal.ofReal ((9 : ℝ) ^ (3 + j)) * (2 * C₂ * ENNReal.ofReal
              (Real.exp (-c * (3 : ℝ) ^ n))) +
            ENNReal.ofReal (729 * Real.exp (-((9 : ℝ) ^ j * (3 : ℝ) ^ (-(n : ℝ) * α)))) := by
  obtain ⟨α, C, hα0, hα, hC, hstep⟩ := planar_SIupgrade_step2 hpc
  obtain ⟨C₂, hC₂, c, hc, hgood⟩ := exists_measure_not_planarStatGood_le hpc
  obtain ⟨θ, hθ, hreach⟩ := exists_measure_not_planarReachLe_le hpc
  refine ⟨α, C, θ, c, hα0, hα, hC, hθ, hc, C₂, hC₂, fun {S} hS0 hS n j ℓ hℓn => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  have hnU : n ≤ (⟨n + 3 + j, 0⟩ : TriadicCube 2).scale := show n ≤ n + 3 + j by omega
  set A := (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hB
  have hAc : (A.card : ℝ) = 729 := by
    rw [hA, card_toIntegerCube_vertices_eq]; norm_num
  have hBc : (B.card : ℝ) = 9 ^ j := by rw [hB, card_toIntegerCube_vertices_eq]
  set C₁ := planarRhoCap S ℓ with hC₁
  have hC₁0 : 0 < C₁ := by rw [hC₁, planarRhoCap]; positivity
  set r : ℝ := (3 : ℝ) ^ (-(n : ℝ) * α) with hr
  have hr0 : 0 < r := by positivity
  set t : ℝ := 2 * (Real.exp 1 - 1) * (C + 1) * (1 + C₁) * r with ht
  set E₁ := {ω : Configuration 2 | ¬ PlanarReachLe ω (⟨n + 3 + j, 0⟩ : TriadicCube 2) ℓ}
    with hE₁
  set E₂ := ⋃ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n,
    {ω : Configuration 2 | ¬ PlanarStatGood ω V} with hE₂
  set E₃ := {ω : Configuration 2 | (A.card : ℝ) * ((B.card : ℝ) * t) <
    ∑ a ∈ A, ∑ b ∈ B, min (planarRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁} with hE₃
  have hsub : {ω | ¬ (PlanarReachLe ω (⟨n + 3 + j, 0⟩ : TriadicCube 2) ℓ ∧
      planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarRhoThreshold α C S n ℓ)} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    have hRL : PlanarReachLe ω (⟨n + 3 + j, 0⟩ : TriadicCube 2) ℓ := not_not.1 h1
    have hSG : ∀ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n, PlanarStatGood ω V :=
        fun V hV => by
      by_contra hV'
      exact h2 (Set.mem_iUnion₂.2 ⟨V, hV, hV'⟩)
    have hS3 : ∑ a ∈ A, ∑ b ∈ B, min (planarRhoStat p ⟨n, a + (27 : ℤ) • b⟩ ω) C₁ ≤
        (A.card : ℝ) * ((B.card : ℝ) * t) := not_lt.1 h3
    apply hω
    refine ⟨hRL, ?_⟩
    have havg := planarRho_le_avg_of_planarReachLe p hS hRL hℓn hnU
    have hmin : ∀ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n,
        planarRho p ω V = min (planarRhoStat p V ω) C₁ := by
      intro V hV
      rw [planarRhoStat_eq_of_good p (hSG V hV)]
      exact (min_eq_left (planarRho_le_of_planarReachLe p hS0 hS hRL
        (subset_of_mem_subcubesAt hnU hV) (by rw [scale_of_mem_subcubesAt hV]; exact hℓn))).symm
    have hsum : ∑ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n, planarRho p ω V ≤
        (A.card : ℝ) * ((B.card : ℝ) * t) := by
      rw [Finset.sum_congr rfl hmin]
      rw [sum_subcubesAt_eq_sum_sum n j (fun V => min (planarRhoStat p V ω) C₁)]
      exact hS3
    have hcard : ((subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n).card : ℝ) =
        (A.card : ℝ) * (B.card : ℝ) := card_subcubesAt_index n j
    have hcpos : (0 : ℝ) < (subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n).card := by
      rw [hcard, hAc, hBc]; positivity
    have havg' : (∑ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n, planarRho p ω V) /
        (subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n).card ≤ t := by
      rw [div_le_iff₀ hcpos, hcard]
      linarith
    unfold planarRhoThreshold
    rw [← hC₁, ← hr]
    linarith
  -- the three probabilities
  have hP₁ : μ E₁ ≤
      ENNReal.ofReal ((9 : ℝ) ^ (n + 3 + j) * (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ)))) :=
    hreach (⟨n + 3 + j, 0⟩ : TriadicCube 2) ℓ
  have hP₂ : μ E₂ ≤ ENNReal.ofReal ((9 : ℝ) ^ (3 + j)) *
      (2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n, μ {ω | ¬ PlanarStatGood ω V}
        ≤ ∑ _V ∈ subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n,
            2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun V hV => (hgood V).trans (by rw [scale_of_mem_subcubesAt hV])
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          have hcard : ((subcubesAt (⟨n + 3 + j, 0⟩ : TriadicCube 2) n).card : ℝ) =
              (A.card : ℝ) * (B.card : ℝ) := card_subcubesAt_index n j
          rw [hAc, hBc] at hcard
          rw [← ENNReal.ofReal_natCast, hcard, show (729 : ℝ) = 9 ^ 3 by norm_num, ← pow_add]
  have hP₃ : μ E₃ ≤ ENNReal.ofReal (729 * Real.exp (-((9 : ℝ) ^ j * r))) := by
    have h := hstep n j hC₁0 t
    rw [← hB, ← hr] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ E₃)]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    rw [hAc, hBc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have he : 1 ≤ Real.exp 1 - 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have hkey : C₁ * r ≤ t - (Real.exp 1 - 1) * (C * (1 + C₁) * r) := by
      rw [ht]
      have h1 : 0 ≤ (Real.exp 1 - 1) * (C + 2) * (1 + C₁) * r - C₁ * r := by
        have : C₁ * r ≤ (1 + C₁) * r := by nlinarith
        have : (1 + C₁) * r ≤ (Real.exp 1 - 1) * (C + 2) * (1 + C₁) * r := by
          have h2 : 1 ≤ (Real.exp 1 - 1) * (C + 2) := by nlinarith
          have : 0 ≤ (1 + C₁) * r := by positivity
          nlinarith
        linarith
      nlinarith
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ hC₁0]
    have h9 : (0 : ℝ) ≤ 9 ^ j := by positivity
    have := mul_le_mul_of_nonneg_left hkey h9
    nlinarith
  calc μ {ω | ¬ (PlanarReachLe ω (⟨n + 3 + j, 0⟩ : TriadicCube 2) ℓ ∧
        planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarRhoThreshold α C S n ℓ)}
      ≤ μ (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ μ E₁ + μ E₂ + μ E₃ := (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hP₁ hP₂) hP₃

end Rigidity.Proofs.Cluster
