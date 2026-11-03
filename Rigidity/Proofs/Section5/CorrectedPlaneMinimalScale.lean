import Rigidity.Steps.Section5.LargeGradientSensitive

/-! # Step 5.27-Mh: the minimal scale `M_h` of the corrected plane `ℓ_{e₁}`

Proof of `CorrectedPlaneMinimalScaleStep` (eq. `def-Mh`, L2457-2462 of the corrected draft).
Theorem 2.5 (`CorrectorQuantitativeInput`) at the origin with exponent `α = 1/2` bounds the
oscillation of the corrector `χ = ℓ_{e₁} - x₁` on `𝒞_∞ ∩ B_ρ` by `C ρ^{1/2} ≤ ρ/4 + C²` for every
`ρ` beyond the minimal scale `M`. For `x` in the cone `x₁ ≥ |x₂|` and `y ∈ Q_r ∪ L_-`, the
increment `x₁ - y₁` of the plane beats this bound on the ball of radius `|x|₁ + |y|₁ + M + 3` as
soon as `x₁ > 3r + (M + 3)/2 + 2C²`. The ball also contains a neighbour of `x` in `𝒞_∞`, which
instantiates the gradient part of the input. -/

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.External
  Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- The Euclidean norm of a vertex of `ℤ²` is at most its `ℓ¹` norm. -/
private theorem norm_latticeEuclideanEmbedding_le_abs_add_abs (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ |(v 0 : ℝ)| + |(v 1 : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |(v 0 : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |(v 1 : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ))]

/-- Every vertex of an infinite open component has a neighbour in it. -/
private theorem exists_adj_of_supp_infinite {ω : Configuration 2} {C : OpenComponent ω}
    (hC : C.supp.Infinite) (y : C) : ∃ y' : C, (componentGraph C).Adj y y' := by
  obtain ⟨w, hw, hwy⟩ := hC.nontrivial.exists_ne y.val
  have hreach : (openGraph ω).Reachable y.val w :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw).symm)
  obtain ⟨q⟩ := hreach
  cases q with
  | nil => exact absurd rfl hwy
  | @cons _ v _ hadj _ =>
    have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp y.2 hadj
    exact ⟨⟨v, hv⟩, (C.toSimpleGraph_adj y.2 hv).2 hadj⟩

/-- The coordinates of neighbours in `𝒞_∞` differ by at most one. -/
private theorem abs_coord_le_of_adj {ω : Configuration 2} {C : OpenComponent ω} {a b : C}
    (hab : (componentGraph C).Adj a b) (j : Fin 2) :
    |(b.val j : ℝ)| ≤ |(a.val j : ℝ)| + 1 := by
  have hu : ∀ i : Fin 2, |((LatticeProb.unit i : Vertex 2) j : ℝ)| ≤ 1 := by
    intro i
    simp only [LatticeProb.unit, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨i, hi | hi⟩ := openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab)
  · have hb : (b.val j : ℝ) = (a.val j : ℝ) + ((LatticeProb.unit i : Vertex 2) j : ℝ) := by
      rw [hi]; push_cast [Pi.add_apply]; ring
    rw [hb]
    exact (abs_add_le _ _).trans (by linarith [hu i])
  · have hb : (b.val j : ℝ) = (a.val j : ℝ) - ((LatticeProb.unit i : Vertex 2) j : ℝ) := by
      rw [hi]; push_cast [Pi.add_apply]; ring
    rw [hb]
    exact (abs_sub _ _).trans (by linarith [hu i])

/-- `C ρ^{1/2} ≤ ρ/4 + C²` for `ρ ≥ 0`. -/
private theorem mul_rpow_half_le_quarter_add_sq {K ρ : ℝ} (hρ : 0 ≤ ρ) :
    K * ρ ^ (1 / 2 : ℝ) ≤ ρ / 4 + K ^ 2 := by
  rw [← Real.sqrt_eq_rpow]
  nlinarith [sq_nonneg (Real.sqrt ρ / 2 - K), Real.sq_sqrt hρ]

/-- **step:5.27-Mh** (eq. `def-Mh`, L2457-2462): almost surely, beyond a scale `M_h` independent
of the corrected plane, `ℓ_{e₁}` is larger at every point of the cone `x₁ ≥ |x₂|` than at every
point of `𝒞_∞ ∩ (Q_r ∪ L_-)`. -/
theorem correctedPlaneMinimalScaleStep : CorrectedPlaneMinimalScaleStep := by
  intro hQ p hpc hp1 r
  obtain ⟨s, K, -, -, hM⟩ := hQ 2 le_rfl p hpc hp1 (1 / 2) one_half_pos
  obtain ⟨M₀, -, hM₀, -, hae⟩ := hM 0
  filter_upwards [hae] with ω hω h
  refine ⟨3 * r + (M₀ ω + 3) / 2 + 2 * K ^ 2 + 1, fun ℓ hℓ x y hcone hx hy => ?_⟩
  obtain ⟨x', hxx'⟩ := exists_adj_of_supp_infinite (uniqueInfiniteComponent_infinite h) x
  have e0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    simp
  have hq : ∀ v : Vertex 2, ∑ i, (Pi.single 0 1 : Fin 2 → ℝ) i * (v i : ℝ) = v 0 := by
    intro v
    simp [Fin.sum_univ_two]
  have hq1 : ∑ i, |(Pi.single 0 1 : Fin 2 → ℝ) i| = 1 := by simp [Fin.sum_univ_two]
  set ρ : ℝ := (|(x.val 0 : ℝ)| + |(x.val 1 : ℝ)|) + (|(y.val 0 : ℝ)| + |(y.val 1 : ℝ)|) +
    M₀ ω + 3 with hρ
  have hM₀ω := hM₀ ω
  have hax := abs_nonneg (x.val 0 : ℝ)
  have hbx := abs_nonneg (x.val 1 : ℝ)
  have hay := abs_nonneg (y.val 0 : ℝ)
  have hby := abs_nonneg (y.val 1 : ℝ)
  have hball : ∀ v : Vertex 2, |(v 0 : ℝ)| + |(v 1 : ℝ)| < ρ →
      ‖latticeEuclideanEmbedding v - latticeEuclideanEmbedding 0‖ < ρ := fun v hv => by
    rw [e0, sub_zero]
    exact (norm_latticeEuclideanEmbedding_le_abs_add_abs v).trans_lt hv
  have hx'0 := abs_coord_le_of_adj hxx' 0
  have hx'1 := abs_coord_le_of_adj hxx' 1
  have key := hω h (Pi.single 0 1) ℓ hℓ ρ (by linarith) x y x x'
    (hball _ (by linarith)) (hball _ (by linarith)) (hball _ (by linarith))
    (hball _ (by linarith)) hxx'
  simp only [hq, hq1, mul_one] at key
  have hosc := (abs_le.1 (le_trans (le_add_of_nonneg_right (abs_nonneg _)) key)).1
  have hsq := mul_rpow_half_le_quarter_add_sq (K := K) (by linarith : (0 : ℝ) ≤ ρ)
  have hc : |(x.val 1 : ℝ)| ≤ (x.val 0 : ℝ) := by exact_mod_cast hcone
  have hxa : |(x.val 0 : ℝ)| = (x.val 0 : ℝ) := abs_of_nonneg (by linarith)
  rcases hy with hy | ⟨hy0, hy1⟩
  · have hy0 : |(y.val 0 : ℝ)| ≤ r := by exact_mod_cast hy 0
    have hy1 : |(y.val 1 : ℝ)| ≤ r := by exact_mod_cast hy 1
    have := le_abs_self (y.val 0 : ℝ)
    linarith
  · have hy0' : |(y.val 0 : ℝ)| = -(y.val 0 : ℝ) := abs_of_nonpos (by exact_mod_cast hy0)
    have hy1' : |(y.val 1 : ℝ)| = 0 := by simp [hy1]
    have hr : (0 : ℝ) ≤ r := r.cast_nonneg
    linarith

end Rigidity.Proofs.Section5
