import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Section5.TwoScaleSteps

/-!
# Planar corrected-plane gradient bound

The corrected-plane gradient estimate uses only the planar quantitative corrector input.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Section2 Rigidity.Section5 Rigidity.External
  Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- Neighbours in an open component are lattice neighbours. -/
private theorem exists_unit_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) :
    ∃ j : Fin 2, b.val = a.val + LatticeProb.unit j ∨ a.val = b.val + LatticeProb.unit j :=
  openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab)

/-- A unit step changes each coordinate by at most one and the `ℓ¹` norm by at most one. -/
private theorem l1_add_unit_le (x : Vertex 2) (j : Fin 2) :
    l1 (x + LatticeProb.unit j) ≤ l1 x + 1 ∧ l1 x ≤ l1 (x + LatticeProb.unit j) + 1 := by
  have hu : ∀ i, ((x + LatticeProb.unit j) i : ℝ) = (x i : ℝ) + if i = j then 1 else 0 := by
    intro i
    simp only [LatticeProb.unit, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  have key : ∀ i, |((x + LatticeProb.unit j) i : ℝ)| ≤ |(x i : ℝ)| + (if i = j then 1 else 0) ∧
      |(x i : ℝ)| ≤ |((x + LatticeProb.unit j) i : ℝ)| + (if i = j then 1 else 0) := by
    intro i
    rw [hu i]
    have h0 : (0 : ℝ) ≤ if i = j then 1 else 0 := by split_ifs <;> norm_num
    refine ⟨(abs_add_le _ _).trans (by rw [abs_of_nonneg h0]), ?_⟩
    have := abs_sub_abs_le_abs_sub (x i : ℝ) ((x i : ℝ) + if i = j then 1 else 0)
    rw [show (x i : ℝ) - ((x i : ℝ) + if i = j then 1 else 0) = -(if i = j then 1 else 0) by ring,
      abs_neg, abs_of_nonneg h0] at this
    linarith
  have hsum : ∑ i : Fin 2, (if i = j then (1 : ℝ) else 0) = 1 := by simp
  unfold l1
  constructor
  · calc ∑ i, |((x + LatticeProb.unit j) i : ℝ)|
        ≤ ∑ i, (|(x i : ℝ)| + if i = j then 1 else 0) := Finset.sum_le_sum fun i _ => (key i).1
      _ = ∑ i, |(x i : ℝ)| + 1 := by rw [Finset.sum_add_distrib, hsum]
  · calc ∑ i, |(x i : ℝ)|
        ≤ ∑ i, (|((x + LatticeProb.unit j) i : ℝ)| + if i = j then 1 else 0) :=
          Finset.sum_le_sum fun i _ => (key i).2
      _ = ∑ i, |((x + LatticeProb.unit j) i : ℝ)| + 1 := by rw [Finset.sum_add_distrib, hsum]

/-- The `ℓ¹` norm changes by at most one along an open edge. -/
private theorem l1_le_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) : l1 b.val ≤ l1 a.val + 1 := by
  obtain ⟨j, hj | hj⟩ := exists_unit_of_adj hab
  · rw [hj]; exact (l1_add_unit_le a.val j).1
  · have := (l1_add_unit_le b.val j).2
    rw [← hj] at this
    exact this

/-- Each coordinate changes by at most one along an open edge. -/
private theorem abs_coord_sub_le_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) (i : Fin 2) : |(a.val i : ℝ) - (b.val i : ℝ)| ≤ 1 := by
  have hu : ∀ j, |((LatticeProb.unit j : Vertex 2) i : ℝ)| ≤ 1 := by
    intro j
    simp only [LatticeProb.unit, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨j, hj | hj⟩ := exists_unit_of_adj hab
  · rw [hj, Pi.add_apply, Int.cast_add, sub_add_cancel_left, abs_neg]
    exact hu j
  · rw [hj, Pi.add_apply, Int.cast_add, add_sub_cancel_left]
    exact hu j

/-- The Euclidean norm of a vertex of `ℤ²` is at most its `ℓ¹` norm. -/
private theorem norm_latticeEuclideanEmbedding_le_l1 (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ l1 v := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |(v 0 : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |(v 1 : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (l1_nonneg v)]
  simp only [l1, Fin.sum_univ_two]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ))]

private theorem rpow_half_affine_le {A B u s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u)
    (hs : 0 < s) : (A + B * u) ^ (s / 2) ≤ (A + B) ^ s + 1 + u ^ s := by
  set v := max u 1 with hv
  have hv1 : 1 ≤ v := le_max_right _ _
  have huv : u ≤ v := le_max_left _ _
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have h1 : A + B * u ≤ (A + B) * v := by nlinarith
  have hsq : ∀ t : ℝ, 0 ≤ t → (t ^ (s / 2)) ^ 2 = t ^ s := by
    intro t ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  have h2 : (A + B * u) ^ (s / 2) ≤ (A + B) ^ (s / 2) * v ^ (s / 2) := by
    rw [← Real.mul_rpow hAB (by linarith)]
    exact Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h3 : (A + B) ^ (s / 2) * v ^ (s / 2) ≤ ((A + B) ^ s + v ^ s) / 2 := by
    rw [← hsq _ hAB, ← hsq v (by linarith)]
    nlinarith [sq_nonneg ((A + B) ^ (s / 2) - v ^ (s / 2))]
  have h4 : v ^ s ≤ u ^ s + 1 := by
    rcases le_total u 1 with h | h
    · rw [hv, max_eq_right h, Real.one_rpow]
      linarith [Real.rpow_nonneg hu s]
    · rw [hv, max_eq_left h]
      linarith
  have h5 := Real.rpow_nonneg hAB s
  have h6 := Real.rpow_nonneg hu s
  linarith

/-- Planar quantitative corrector bounds imply the corrected-plane gradient estimate. -/
theorem correctedPlaneGradientStep_two (hQ : CorrectorQuantitativeInputTwo) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s θ : ℝ, 0 < s ∧ 0 < θ ∧ ∃ Λ : Configuration 2 → ℝ, Measurable Λ ∧ IsOs 2 p Λ s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (i : Fin 2) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
          ∀ a b, (componentGraph (uniqueInfiniteComponent h)).Adj a b →
            |ℓ a - ℓ b| ≤ Λ ω * (1 + l1 a.val) := by
  obtain ⟨s, K, hs, hK, hM⟩ := hQ p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hae⟩ := hM 0
  have hΛm : Measurable fun ω => 1 + K * (M ω + 2) :=
    measurable_const.add (measurable_const.mul (hMm.add measurable_const))
  have hint : Integrable (fun ω => Real.exp (Real.rpow (1 + K * (M ω + 2)) (s / 2)))
      (latticeBondLaw 2 p) := by
    refine (hMos.1.const_mul (Real.exp ((1 + 2 * K + K * K) ^ s + 1))).mono'
      (hΛm.pow_const (s / 2)).exp.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have hMK : max (M ω / K) 0 = M ω / K := max_eq_left (div_nonneg (hM0 ω) hK.le)
    have hbound := rpow_half_affine_le (A := 1 + 2 * K) (B := K * K) (u := M ω / K)
      (by positivity) (by positivity) (div_nonneg (hM0 ω) hK.le) hs
    have heq : 1 + 2 * K + K * K * (M ω / K) = 1 + K * (M ω + 2) := by
      field_simp
      ring
    rw [heq] at hbound
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hMK, ← Real.exp_add]
    simp only [Real.rpow_eq_pow]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨θ, hθ, hΛos⟩ := exists_isOs_of_integrable (half_pos hs)
    (fun ω => by have := hM0 ω; positivity) hΛm hint
  refine ⟨s / 2, θ, half_pos hs, hθ, fun ω => 1 + K * (M ω + 2), hΛm, hΛos, ?_⟩
  filter_upwards [hae] with ω hω h i ℓ hℓ a b hab
  have e0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext k
    change ((0 : ℤ) : ℝ) = 0
    simp
  have hq : ∀ v : Vertex 2, ∑ k, (Pi.single i 1 : Fin 2 → ℝ) k * (v k : ℝ) = v i := by
    intro v
    simp [Pi.single_apply]
  have hq1 : ∑ k, |(Pi.single i 1 : Fin 2 → ℝ) k| = 1 := by
    simp [Pi.single_apply, apply_ite]
  have hM0ω := hM0 ω
  have hla := l1_nonneg a.val
  have hlb := l1_le_of_adj hab
  set r : ℝ := M ω + l1 a.val + 2 with hr
  have hball : ∀ v : Vertex 2, l1 v < r →
      ‖latticeEuclideanEmbedding v - latticeEuclideanEmbedding 0‖ < r := fun v hv => by
    rw [e0, sub_zero]
    exact (norm_latticeEuclideanEmbedding_le_l1 v).trans_lt hv
  have key := hω h (Pi.single i 1) ℓ hℓ r (by linarith) a b a b
    (hball _ (by linarith)) (hball _ (by linarith)) (hball _ (by linarith))
    (hball _ (by linarith)) hab
  simp only [hq, hq1, mul_one, Real.rpow_one] at key
  have hχ : |(ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))| ≤ K * r := by
    linarith [abs_nonneg ((ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ)))]
  have hcoord := abs_coord_sub_le_of_adj hab i
  have htri : |ℓ a - ℓ b| ≤ |(ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))| +
      |(a.val i : ℝ) - (b.val i : ℝ)| := by
    rw [show ℓ a - ℓ b = ((ℓ a - (a.val i : ℝ)) - (ℓ b - (b.val i : ℝ))) +
      ((a.val i : ℝ) - (b.val i : ℝ)) by ring]
    exact abs_add_le _ _
  have hprod : K * l1 a.val ≤ K * (M ω + 2) * l1 a.val := by
    have : K * l1 a.val * 1 ≤ K * l1 a.val * (M ω + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hK.le hla)
    linarith
  calc |ℓ a - ℓ b| ≤ K * r + 1 := by linarith
    _ = 1 + K * (M ω + 2) + K * l1 a.val := by rw [hr]; ring
    _ ≤ (1 + K * (M ω + 2)) * (1 + l1 a.val) := by nlinarith

end Rigidity.Proofs.Section5
