import Rigidity.Proofs.Corrector.DarioStepTwoDomination

/-!
# The failure probability of the weight bound of a triadic cube at a given range

For the range `R`, the scale `m` with `2((3κ + 9)R + 1) + 1 ≤ 3^m` and the cube `⟨m + j, c⟩`, the
weight bound of the cube with constant `M = (e - 1) M₀ + 1` fails only if a vertex of the cube is
not good for the domination, or the finite-range weights exceed their bound on average. The first
event has probability at most `9^{m+j} C R⁴ e^{-c R^σ}`, the second at most
`9^m exp(-9^j / (K₀ R^{29})^q)` by the Chernoff bound over the residue classes modulo `3^m`
(`measure_not_weightGood_le_of_bounds`), with `K₀ R^{29}` bounding the finite-range weight
(`finiteWeightBound_le`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- The bound of the finite-range weight is at most `K₀ R^{29}`. -/
theorem finiteWeightBound_le {κ R : ℕ} (hκ : 1 ≤ κ) (hR : 1 ≤ R) :
    (2 * (R : ℝ) + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9) ≤
      (18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * (R : ℝ) ^ 29 := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hκx : (1 : ℝ) ≤ κ * R := by nlinarith
  calc (2 * (R : ℝ) + 1) ^ 2 * (2 * ((6 * κ * R + 1) ^ 2 * (5 + 24 * R)) ^ 9)
      ≤ (3 * (R : ℝ)) ^ 2 * (2 * ((7 * κ * R) ^ 2 * (29 * R)) ^ 9) := by
        gcongr
        · linarith
        · nlinarith
        · linarith
    _ = _ := by ring

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **The failure probability of the weight bound of a cube at a given range.** -/
theorem measure_not_weightGood_le_of_bounds {p : unitInterval} {κ R m j : ℕ} (hκ : 1 ≤ κ)
    (hR : 1 ≤ R) {i : Fin 2} {q M₀ C c σ : ℝ} (hq : 1 ≤ q) (hM₀ : 0 ≤ M₀) (hC : 0 ≤ C)
    (hmom : ∀ u, ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal M₀)
    (hdom : ∀ u, latticeBondLaw 2 p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ))))
    (hm : 2 * ((3 * κ + 9) * R + 1) + 1 ≤ 3 ^ m) (idx : Vertex 2) :
    latticeBondLaw 2 p {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω
        ⟨m + j, idx⟩} ≤
      ENNReal.ofReal (9 ^ (m + j) * (C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ))) +
        9 ^ m * Real.exp (-((9 : ℝ) ^ j * 1) /
          ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * (R : ℝ) ^ 29) ^ q)) := by
  set V := (⟨m + j, idx⟩ : TriadicCube 2).toIntegerCube.vertices with hV
  set X : Vertex 2 → Configuration 2 → ℝ := fun u ω => finiteWeight κ R ω u ^ q with hX
  set A : ℝ := ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * (R : ℝ) ^ 29) ^ q with hA
  have hq0 : 0 ≤ q := by linarith
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hA0 : 0 < A := by positivity
  have hcardV : ((V.card : ℕ) : ℝ) = 9 ^ (m + j) := card_toIntegerCube_vertices_eq _
  have hsub : {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω ⟨m + j, idx⟩} ⊆
      (⋃ u ∈ V, {ω | ¬ DomGood hG hGv κ R i ω u}) ∪
        {ω | ((V.card : ℕ) : ℝ) * ((Real.exp 1 - 1) * M₀ + 1) < ∑ u ∈ V, X u ω} := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_or,
      not_exists, not_and, not_not, not_lt] at hc
    exact hω (weightGood_of_domGood hG hGv hR hq0 (fun u hu => hc.1 u hu)
      (by rw [mul_comm]; exact hc.2))
  have h1 : latticeBondLaw 2 p (⋃ u ∈ V, {ω | ¬ DomGood hG hGv κ R i ω u}) ≤
      ENNReal.ofReal (9 ^ (m + j) * (C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun u _ => hdom u).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcardV]
  have h2 : latticeBondLaw 2 p
      {ω | ((V.card : ℕ) : ℝ) * ((Real.exp 1 - 1) * M₀ + 1) < ∑ u ∈ V, X u ω} ≤
      ENNReal.ofReal (9 ^ m * Real.exp (-((9 : ℝ) ^ j * 1) / A)) := by
    have hXm : ∀ u, Measurable (X u) := fun u => (measurable_finiteWeight κ R u).pow_const q
    have h0 : ∀ u ω, 0 ≤ X u ω := fun u ω => Real.rpow_nonneg (finiteWeight_nonneg hR ω u) q
    have hle : ∀ u ω, X u ω ≤ A := fun u ω =>
      Real.rpow_le_rpow (finiteWeight_nonneg hR ω u)
        ((finiteWeight_le hR ω u).trans (finiteWeightBound_le hκ hR)) hq0
    have hε : ∀ u, ∫ ω, X u ω ∂latticeBondLaw 2 p ≤ M₀ := by
      intro u
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (h0 u)) (hXm u).aestronglyMeasurable]
      refine ENNReal.toReal_le_of_le_ofReal hM₀ ((le_of_eq ?_).trans (hmom u))
      exact lintegral_congr fun ω =>
        (ENNReal.ofReal_rpow_of_nonneg (finiteWeight_nonneg hR ω u) hq0).symm
    have hloc : ∀ u (ω ω' : Configuration 2),
        (∀ e ∈ localBonds (↑(supBox u ((3 * κ + 9) * R + 1)) : Set (Vertex 2)), ω e = ω' e) →
          X u ω = X u ω' := fun u ω ω' h => by
      simp only [hX]
      rw [finiteWeight_eq_of_localBonds hR h]
    have hch := measureReal_sum_cube_gt_le p X hXm hloc hA0 h0 hle hε (j := j) hm idx
      ((Real.exp 1 - 1) * M₀ + 1)
    rw [show (Real.exp 1 - 1) * M₀ + 1 - (Real.exp 1 - 1) * M₀ = 1 by ring] at hch
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 hch
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end Grad

end Rigidity.Corrector
