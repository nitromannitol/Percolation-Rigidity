import Rigidity.Proofs.Partition.LambdaMoment
import Rigidity.Proofs.Partition.StochasticAverage

/-!
# The stochastic bound of `Λ_t`

Armstrong and Dario state after Proposition 2.1 that `Λ_t(U) ≤ 𝒪_{s/t}(C)`, as a consequence of
Proposition 2.1 (iii) and the averaging property of the `𝒪_s` notation. We prove, uniformly in
the finite set `U`, `Λ_t(U) ≤ 𝒪_{1/(t + d)}(C)` for the partition `𝒫` (for which `s = 1`): every
partition cube meeting `U` contains a point of `U`, so `Λ_t(U) ≤ |U|⁻¹ ∑_{z ∈ U} size(𝒫(z))^{t + d}`,
an average of `𝒪_{1/(t + d)}` variables. For `U` a single vertex `x`, `Λ_t(U) = size(𝒫(x))^{t + d}`,
so a bound uniform in `U` carries the exponent of `size^{t + d}`.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **`Λ_t(U) ≤ 𝒪_{1/(t+d)}(C)` uniformly in `U`.** For supercritical bond percolation on `ℤᵈ`,
`d ≥ 2`, and `t ∈ ℕ`, there is `C` such that for every nonempty finite set `U` of vertices,
`|U|⁻¹ ∑_{x ∈ cl(U)} 3^{t n(x)} ≤ 𝒪_{1/(t+d)}(C)`, `n(x)` the scale of the partition cube of `x`. -/
theorem exists_osBound_lambda [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (t : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Finset (Vertex d), U.Nonempty →
      OsBound (latticeBondLaw d p) (1 / ((t + d : ℕ) : ℝ)) C
        (fun ω => (∑ x ∈ partitionClosure ω U,
          (3 : ℝ) ^ (t * (partitionCube ω x).scale)) / U.card) := by
  obtain ⟨θ, hθ, hsize⟩ := exists_osBound_stoppingSize hd hpc
  have hn : 0 < t + d := by omega
  have hσ : 0 < 1 / ((t + d : ℕ) : ℝ) := by positivity
  have hσ1 : 1 / ((t + d : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hn
  obtain ⟨K, hK, hsum⟩ := osBound_sum_of_le_one hσ hσ1
  refine ⟨K * θ ^ (t + d), by positivity, fun U hU => ?_⟩
  have hpow : ∀ x : Vertex d, OsBound (latticeBondLaw d p) (1 / ((t + d : ℕ) : ℝ))
      (θ ^ (t + d))
      (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (t + d)) := fun x =>
    osBound_pow_of_nonneg (hsize x) (fun ω => TriadicCube.stoppingSize_nonneg _ x) hn
  have hS := hsum (latticeBondLaw d p) U
    (fun x ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) (x : Vertex d) ^ (t + d))
    (fun _ => θ ^ (t + d))
    (fun x => (TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes
      (x : Vertex d)).pow_const _)
    (fun _ => pow_pos hθ _) (fun x => hpow x)
  have hcard : (∑ _x : U, θ ^ (t + d)) = U.card * θ ^ (t + d) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  intro τ hτ
  apply le_trans (measure_mono_ae ?_) (hS τ hτ)
  filter_upwards [ae_partitionEvent hd hpc] with ω hP
  intro hω
  change τ * (K * θ ^ (t + d)) < max ((∑ x ∈ partitionClosure ω U,
    (3 : ℝ) ^ (t * (partitionCube ω x).scale)) / U.card) 0 at hω
  change τ * (K * ∑ _x : U, θ ^ (t + d)) < max (∑ x : U,
    TriadicCube.stoppingSize (TriadicCube.goodCubes ω) (x : Vertex d) ^ (t + d)) 0
  rw [hcard, Finset.sum_coe_sort U
    (fun x => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (t + d))]
  have hcl : (∑ x ∈ partitionClosure ω U, (3 : ℝ) ^ (t * (partitionCube ω x).scale)) ≤
      ∑ x ∈ U, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ^ (t + d) := by
    refine (sum_partitionClosure_le hP U t).trans
      (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
    rw [stoppingSize_goodCubes_eq hP z, ← pow_mul, Nat.mul_comm]
  have hcl0 : 0 ≤ ∑ x ∈ partitionClosure ω U, (3 : ℝ) ^ (t * (partitionCube ω x).scale) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [max_eq_left (div_nonneg hcl0 hUpos.le), lt_div_iff₀ hUpos] at hω
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  calc τ * (K * (U.card * θ ^ (t + d))) = τ * (K * θ ^ (t + d)) * U.card := by ring
    _ < _ := hω
    _ ≤ _ := hcl

end Rigidity.Percolation
