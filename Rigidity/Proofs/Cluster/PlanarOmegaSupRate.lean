import Rigidity.Proofs.Cluster.PlanarConvergenceRate
import Rigidity.Proofs.Percolation.PlanarDuality

/-!
# Lemma 5.10 of Armstrong and Dario in dimension two

For a triadic cube `U`, let `ω(U, q) = ν(U, ā⁻¹ q) - μ(U, q) - q · ā⁻¹ q` (with `μ` and `ν`
replaced by `0` off the event that the partition exists and resolves `U`, as Armstrong and Dario
set `u ≡ 0` there) and `ρ(U) = sup_q |q|⁻² ω(U, q)₊`. Lemma 5.10 of Armstrong and Dario
(display (5.42)) states

`E[sup_q |q|⁻² ω(□_n, q)₊] ≤ C 3^{-nα}`.

This is proved here for `p > p_c(2)` with no other hypothesis (`planar_omegadecayrate`), following
Step 4 of their proof: `q ↦ ω(U, q)` is quadratic (`isPlanarQuadratic_planarOmega`), so the
supremum is finite (`bddAbove_planarOmega_ratio`); by the comparison of `μ` and `ν`
(`sum_mul_le_planarNu_sub_planarMu`, Corollary 4.6 of Armstrong and Dario),
`ω(U, q) + K Y |q|² ≥ 0` for a random `Y` with `E[Y] ≤ C 3^{-n/2}`
(`planarComparisonError`), so that `ρ(U) ≤ 2 (ω(U, e₀) + ω(U, e₁)) + 4 K Y` (sums control suprema),
and the expectation of `ω(□_n, eᵢ)` is at most `C 3^{-nα}` by display (5.4) (`planar_convexp`).

The supremum is over an uncountable set; the bound is stated with a measurable majorant of `ρ(□_n)`
whose expectation is at most `C 3^{-nα}`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix ENNReal

variable {ω : Configuration 2}

theorem IsPlanarQuadratic.apply_zero {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g) :
    g 0 = 0 := by
  have h := hg 0 0 0 0
  simpa using h

theorem IsPlanarQuadratic.add {f g : (Fin 2 → ℝ) → ℝ} (hf : IsPlanarQuadratic f)
    (hg : IsPlanarQuadratic g) : IsPlanarQuadratic fun q => f q + g q := by
  intro r s a b
  dsimp only
  rw [hf, hg]
  ring

theorem IsPlanarQuadratic.sub {f g : (Fin 2 → ℝ) → ℝ} (hf : IsPlanarQuadratic f)
    (hg : IsPlanarQuadratic g) : IsPlanarQuadratic fun q => f q - g q := by
  intro r s a b
  dsimp only
  rw [hf, hg]
  ring

theorem IsPlanarQuadratic.neg {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g) :
    IsPlanarQuadratic fun q => -g q := by
  intro r s a b
  dsimp only
  rw [hg]
  ring

theorem isPlanarQuadratic_zero : IsPlanarQuadratic fun _ => (0 : ℝ) := by
  intro r s a b
  ring

theorem isPlanarQuadratic_dotProduct_mulVec (A : Matrix (Fin 2) (Fin 2) ℝ) :
    IsPlanarQuadratic fun q => ∑ i, q i * (A *ᵥ q) i := by
  intro r s a b
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem isPlanarQuadratic_planarNu (U : TriadicCube 2) : IsPlanarQuadratic (planarNu ω U) :=
  fun r s a b => planarNu_smul_add_smul U r s a b

theorem isPlanarQuadratic_planarMu (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) : IsPlanarQuadratic (planarMu ω U) :=
  fun r s a b => planarMu_smul_add_smul hP hU r s a b

/-- **A quadratic form is bounded by its values at `e₀`, `e₁` and `e₀ + e₁`.** -/
theorem IsPlanarQuadratic.abs_le {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (q : Fin 2 → ℝ) :
    |g q| ≤ (|g (Pi.single 0 1)| + |g (Pi.single 1 1)| +
      |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)|) *
        (q 0 ^ 2 + q 1 ^ 2) := by
  have h := hg (Pi.single 0 1) (Pi.single 1 1) (q 0) (q 1)
  rw [← eq_smul_single_add_smul_single q] at h
  rw [h]
  set a := g (Pi.single 0 1)
  set b := g (Pi.single 1 1)
  set c := g (Pi.single 0 1 + Pi.single 1 1) - a - b
  have h1 : |q 0 ^ 2 * a + q 1 ^ 2 * b + q 0 * q 1 * c| ≤
      q 0 ^ 2 * |a| + q 1 ^ 2 * |b| + |q 0 * q 1| * |c| := by
    calc |q 0 ^ 2 * a + q 1 ^ 2 * b + q 0 * q 1 * c| ≤
          |q 0 ^ 2 * a + q 1 ^ 2 * b| + |q 0 * q 1 * c| := abs_add_le _ _
      _ ≤ |q 0 ^ 2 * a| + |q 1 ^ 2 * b| + |q 0 * q 1 * c| := by
          gcongr
          exact abs_add_le _ _
      _ = q 0 ^ 2 * |a| + q 1 ^ 2 * |b| + |q 0 * q 1| * |c| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q 0)),
            abs_of_nonneg (sq_nonneg (q 1))]
  have h2 : |q 0 * q 1| ≤ q 0 ^ 2 + q 1 ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_abs (q 0), sq_abs (q 1), sq_nonneg (|q 0| - |q 1|), abs_nonneg (q 0),
      abs_nonneg (q 1)]
  have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg c)
  have h4 := mul_nonneg (sq_nonneg (q 1)) (abs_nonneg a)
  have h5 := mul_nonneg (sq_nonneg (q 0)) (abs_nonneg b)
  nlinarith

/-- The ratio `|q|⁻² g(q)₊` of a quadratic form is bounded. -/
theorem ratio_le_of_max_le {g : (Fin 2 → ℝ) → ℝ}
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ q, max (g q) 0 ≤ K * (q 0 ^ 2 + q 1 ^ 2)) (q : Fin 2 → ℝ) :
    max (g q) 0 / (q 0 ^ 2 + q 1 ^ 2) ≤ K := by
  by_cases hq : q 0 ^ 2 + q 1 ^ 2 = 0
  · rw [hq, div_zero]
    exact hK0
  · have hpos : 0 < q 0 ^ 2 + q 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hq)
    rw [div_le_iff₀ hpos]
    exact hK q

theorem IsPlanarQuadratic.max_le_mul {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g)
    (q : Fin 2 → ℝ) :
    max (g q) 0 ≤ (|g (Pi.single 0 1)| + |g (Pi.single 1 1)| +
      |g (Pi.single 0 1 + Pi.single 1 1) - g (Pi.single 0 1) - g (Pi.single 1 1)|) *
        (q 0 ^ 2 + q 1 ^ 2) :=
  max_le ((le_abs_self _).trans (IsPlanarQuadratic.abs_le hg q)) (by positivity)

/-- **The quantity `ω(U, q)` of Armstrong and Dario** (Section 5, before Lemma 5.3), in dimension
two: `ν(U, ā⁻¹ q) - μ(U, q) - q · ā⁻¹ q`, with `ν` and `μ` replaced by `0` off the event that the
partition exists and resolves `U`. -/
noncomputable def planarOmega (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2)
    (q : Fin 2 → ℝ) : ℝ :=
  ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      planarNu ω U ((planarAhom p)⁻¹ *ᵥ q) else 0) +
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then -planarMu ω U q else 0)) -
    ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i

/-- **The quantity `ρ(U) = sup_q |q|⁻² ω(U, q)₊`** of Armstrong and Dario (proof of Lemma 5.11 and
the left side of display (5.42)), in dimension two. -/
noncomputable def planarRho (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2) : ℝ :=
  ⨆ q : Fin 2 → ℝ, max (planarOmega p ω U q) 0 / (q 0 ^ 2 + q 1 ^ 2)

/-- `q ↦ ω(U, q)` is a quadratic form. -/
theorem isPlanarQuadratic_planarOmega (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2) :
    IsPlanarQuadratic (planarOmega p ω U) := by
  have hd := isPlanarQuadratic_dotProduct_mulVec (planarAhom p)⁻¹
  by_cases h : PlanarPartitionEvent ω ∧ PlanarResolved ω U
  · have e : planarOmega p ω U = fun q =>
        (planarNu ω U ((planarAhom p)⁻¹ *ᵥ q) + -planarMu ω U q) -
          ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [planarOmega, if_pos h]
    rw [e]
    exact IsPlanarQuadratic.sub
      (IsPlanarQuadratic.add ((isPlanarQuadratic_planarNu U).comp_mulVec _)
        (IsPlanarQuadratic.neg (isPlanarQuadratic_planarMu h.1 h.2))) hd
  · have e : planarOmega p ω U = fun q =>
        ((fun _ => (0 : ℝ)) q + (fun _ => (0 : ℝ)) q) - ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i := by
      funext q
      simp only [planarOmega, if_neg h]
    rw [e]
    exact IsPlanarQuadratic.sub
      (IsPlanarQuadratic.add isPlanarQuadratic_zero isPlanarQuadratic_zero) hd

/-- The supremum defining `ρ(U)` is finite. -/
theorem bddAbove_planarOmega_ratio (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2) :
    BddAbove (Set.range fun q : Fin 2 → ℝ => max (planarOmega p ω U q) 0 / (q 0 ^ 2 + q 1 ^ 2)) :=
  ⟨_, Set.forall_mem_range.2 fun q =>
    ratio_le_of_max_le (by positivity)
      (IsPlanarQuadratic.max_le_mul (isPlanarQuadratic_planarOmega p ω U)) q⟩

theorem planarRho_nonneg (p : unitInterval) (ω : Configuration 2) (U : TriadicCube 2) :
    0 ≤ planarRho p ω U := by
  have h := le_ciSup (bddAbove_planarOmega_ratio p ω U) 0
  rw [planarRho]
  simpa using h

theorem planarRho_le {p : unitInterval} {U : TriadicCube 2} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ q, max (planarOmega p ω U q) 0 ≤ B * (q 0 ^ 2 + q 1 ^ 2)) :
    planarRho p ω U ≤ B :=
  ciSup_le fun q => ratio_le_of_max_le hB0 hB q

/-- The random error of the comparison of `μ` and `ν` on `U` (the error of Corollary 4.6 of
Armstrong and Dario, in the form of `ofReal_sum_mul_le_of_partitionEvent`), per unit of
`|q|₁ |ξ|₁`. -/
noncomputable def planarComparisonError (ω : Configuration 2) (U : TriadicCube 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (3 : ℝ) ^ U.scale + 9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale))) +
    ENNReal.ofReal (9 * 162001 / ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
      ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 +
    ∑ z ∈ U.toIntegerCube.vertices,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z

theorem measurable_planarComparisonError (U : TriadicCube 2) :
    Measurable fun ω => planarComparisonError ω U :=
  (measurable_const.add ((Finset.measurable_sum _
      fun (k : Fin 2 × Bool × Vertex 2) _ => measurable_reachSum 4 k.2.2).const_mul _)).add
    (Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _)

/-- The comparison of `μ` and `ν` with the error `|q|₁ |ξ|₁ Y(U)`. -/
theorem ofReal_sum_mul_le_planarComparisonError (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (ξ q : Fin 2 → ℝ) (hξ : 0 < |ξ 0| + |ξ 1|) :
    ENNReal.ofReal (∑ i, q i * ξ i) ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (-planarMu ω U q) else 0) +
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarNu ω U ξ) else 0) +
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) * planarComparisonError ω U := by
  have hX0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine (ofReal_sum_mul_le_of_partitionEvent hP U ξ q hξ).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hX0,
    show 9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
        ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale)) =
      (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) *
        (9 * 162001 / ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) by ring,
    ENNReal.ofReal_mul hX0, planarComparisonError]
  ring

/-- **The comparison of `μ` and `ν` for `ω`**: `ω(U, q) ≥ -2 S Y(U) |q|²`, where `S` bounds the
`ℓ¹` norm of `ā⁻¹`. -/
theorem neg_le_planarOmega {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hP : PlanarPartitionEvent ω) (U : TriadicCube 2) (hZ : planarComparisonError ω U ≠ ∞)
    {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|)) (q : Fin 2 → ℝ) :
    -(2 * S * (planarComparisonError ω U).toReal * (q 0 ^ 2 + q 1 ^ 2)) ≤ planarOmega p ω U q := by
  have hY0 : 0 ≤ (planarComparisonError ω U).toReal := ENNReal.toReal_nonneg
  by_cases hq : q = 0
  · subst hq
    rw [IsPlanarQuadratic.apply_zero (isPlanarQuadratic_planarOmega p ω U)]
    simp
  set ξ := (planarAhom p)⁻¹ *ᵥ q with hξdef
  have hξ : 0 < |ξ 0| + |ξ 1| := by
    by_contra h
    have h := not_lt.1 h
    have h0 : ξ 0 = 0 := abs_eq_zero.1 (le_antisymm (by linarith [abs_nonneg (ξ 1)]) (abs_nonneg _))
    have h1 : ξ 1 = 0 := abs_eq_zero.1 (le_antisymm (by linarith [abs_nonneg (ξ 0)]) (abs_nonneg _))
    have hξ0 : ξ = 0 := funext fun i => by fin_cases i <;> assumption
    apply hq
    rw [← planarAhom_mulVec_inv_mulVec hpc q, ← hξdef, hξ0, Matrix.mulVec_zero]
  have hX0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hξ.le
  have h := ofReal_sum_mul_le_planarComparisonError hP U ξ q hξ
  set Iμ : ℝ≥0∞ := if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    ENNReal.ofReal (-planarMu ω U q) else 0 with hIμ
  set Iν : ℝ≥0∞ := if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    ENNReal.ofReal (planarNu ω U ξ) else 0 with hIν
  have hIμf : Iμ ≠ ∞ := by rw [hIμ]; split_ifs <;> simp
  have hIνf : Iν ≠ ∞ := by rw [hIν]; split_ifs <;> simp
  have hXZ : ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) * planarComparisonError ω U ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZ
  have h' := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hIμf, hIνf⟩, hXZ⟩)).1 h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hIμf, hIνf⟩) hXZ, ENNReal.toReal_add hIμf hIνf,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hX0] at h'
  have e1 : Iμ.toReal = if PlanarPartitionEvent ω ∧ PlanarResolved ω U then -planarMu ω U q
      else 0 := by
    rw [hIμ]
    split_ifs with hc
    · exact ENNReal.toReal_ofReal (neg_nonneg.2 (planarMu_nonpos hc.1 hc.2 q))
    · rfl
  have e2 : Iν.toReal = if PlanarPartitionEvent ω ∧ PlanarResolved ω U then planarNu ω U ξ
      else 0 := by
    rw [hIν]
    split_ifs
    · exact ENNReal.toReal_ofReal (planarNu_nonneg ξ)
    · rfl
  rw [e1, e2] at h'
  have hX : (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) ≤ 2 * S * (q 0 ^ 2 + q 1 ^ 2) := by
    have a := mul_le_mul_of_nonneg_left (hS q) (add_nonneg (abs_nonneg (q 0)) (abs_nonneg (q 1)))
    have b := mul_le_mul_of_nonneg_left (abs_add_abs_sq_le q) hS0
    calc (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) ≤ (|q 0| + |q 1|) * (S * (|q 0| + |q 1|)) := a
      _ = S * (|q 0| + |q 1|) ^ 2 := by ring
      _ ≤ S * (2 * (q 0 ^ 2 + q 1 ^ 2)) := b
      _ = 2 * S * (q 0 ^ 2 + q 1 ^ 2) := by ring
  have hXY := mul_le_mul_of_nonneg_right hX hY0
  simp only [planarOmega]
  rw [← hξdef]
  linarith

/-- **Sums control suprema** (Armstrong and Dario, Step 4 of the proof of Lemma 5.10, in dimension
two): `ρ(U) ≤ 2 (ω(U, e₀) + ω(U, e₁)) + 8 S Y(U)`. -/
theorem planarRho_le_of_partitionEvent {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hP : PlanarPartitionEvent ω) (U : TriadicCube 2) (hZ : planarComparisonError ω U ≠ ∞)
    {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|)) :
    planarRho p ω U ≤ 2 * (planarOmega p ω U (Pi.single 0 1) + planarOmega p ω U (Pi.single 1 1)) +
      8 * S * (planarComparisonError ω U).toReal := by
  set K := 2 * S * (planarComparisonError ω U).toReal with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hS0) ENNReal.toReal_nonneg
  have hF := (isPlanarQuadratic_planarOmega p ω U).add_sq K
  have hF0 : ∀ q : Fin 2 → ℝ, 0 ≤ planarOmega p ω U q + K * (q 0 ^ 2 + q 1 ^ 2) := fun q => by
    have := neg_le_planarOmega hpc hP U hZ hS0 hS q
    rw [hK]
    linarith
  have h1 : (Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 0 1 : Fin 2 → ℝ) 1 ^ 2 = 1 := by simp
  have h2 : (Pi.single 1 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 1 1 : Fin 2 → ℝ) 1 ^ 2 = 1 := by simp
  have hB0 : 0 ≤ 2 * (planarOmega p ω U (Pi.single 0 1) + planarOmega p ω U (Pi.single 1 1)) +
      4 * K := by
    have a := hF0 (Pi.single 0 1)
    have b := hF0 (Pi.single 1 1)
    rw [h1] at a
    rw [h2] at b
    linarith
  have e : 2 * (planarOmega p ω U (Pi.single 0 1) + planarOmega p ω U (Pi.single 1 1)) +
      8 * S * (planarComparisonError ω U).toReal =
      2 * (planarOmega p ω U (Pi.single 0 1) + planarOmega p ω U (Pi.single 1 1)) + 4 * K := by
    rw [hK]
    ring
  rw [e]
  refine planarRho_le hB0 fun q => ?_
  have hle := hF.le_of_nonneg hF0 q
  simp only [h1, h2] at hle
  have hq0 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
  have hKq : 0 ≤ K * (q 0 ^ 2 + q 1 ^ 2) := mul_nonneg hK0 hq0
  refine max_le ?_ ?_
  · nlinarith
  · exact mul_nonneg hB0 hq0

/-- **The expectation of the error of the comparison**: `E[Y(U)] ≤ C 3^{-n/2}`, `n` the scale of
`U`. -/
theorem exists_lintegral_planarComparisonError_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ U : TriadicCube 2,
      ∫⁻ ω, planarComparisonError ω U ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal (1 / Real.sqrt ((3 : ℝ) ^ U.scale)) := by
  obtain ⟨C₄, hC₄, h4⟩ := exists_lintegral_tsum_ninefold_le hpc 4
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  refine ⟨10 + 9 * 162001 * 4 * C₄ + C₆, by finiteness, fun U => ?_⟩
  have hsize : ((U.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ U.scale := by
    rw [show U.toIntegerCube.size = 3 ^ U.scale from rfl]
    push_cast
    ring
  have hcardB : ((boundaryIndex U).card : ℝ≥0∞) ≤ ENNReal.ofReal (4 * (3 : ℝ) ^ U.scale) := by
    rw [← ENNReal.ofReal_natCast, ← hsize]
    exact ENNReal.ofReal_le_ofReal (card_boundaryIndex_le U)
  have hm4 : Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal (9 * 162001 / ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
        ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 :=
    (Finset.measurable_sum _
      fun (k : Fin 2 × Bool × Vertex 2) _ => measurable_reachSum 4 k.2.2).const_mul _
  have hm6 : Measurable fun ω : Configuration 2 =>
      ∑ z ∈ U.toIntegerCube.vertices,
        ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z :=
    Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _
  have e4 : ∫⁻ ω, ENNReal.ofReal (9 * 162001 /
        ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
        ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal (9 * 162001 / ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
        (ENNReal.ofReal (4 * (3 : ℝ) ^ U.scale) * C₄) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum _ fun k _ => measurable_reachSum 4 k.2.2]
    gcongr
    calc ∑ k ∈ boundaryIndex U, ∫⁻ ω, reachSum ω 4 k.2.2 ∂(latticeBondLaw 2 p)
        ≤ ∑ _k ∈ boundaryIndex U, C₄ := Finset.sum_le_sum fun k _ => h4 k.2.2
      _ = ((boundaryIndex U).card : ℝ≥0∞) * C₄ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardB zero_le
  have e6 : ∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices,
        ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal ((9 : ℝ) ^ U.scale) *
        (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * C₆) := by
    rw [lintegral_finsetSum _ fun z _ => (measurable_reachSum 6 z).const_mul _]
    calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z
          ∂(latticeBondLaw 2 p)
        ≤ ∑ _z ∈ U.toIntegerCube.vertices,
            ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * C₆ :=
          Finset.sum_le_sum fun z _ => by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact mul_le_mul_of_nonneg_left (h6 z) zero_le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices U]; rfl
  have herr := duality_error_le zero_le_one (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 3 ^ U.scale)
    rfl C₄ C₆
  simp only [one_mul, mul_one, ENNReal.ofReal_one] at herr
  calc ∫⁻ ω, planarComparisonError ω U ∂(latticeBondLaw 2 p)
      = ENNReal.ofReal (1 / (3 : ℝ) ^ U.scale + 9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale))) +
          ∫⁻ ω, ENNReal.ofReal (9 * 162001 / ((3 : ℝ) ^ U.scale *
            Real.sqrt ((3 : ℝ) ^ U.scale))) * ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2
            ∂(latticeBondLaw 2 p) +
          ∫⁻ ω, ∑ z ∈ U.toIntegerCube.vertices,
            ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z
            ∂(latticeBondLaw 2 p) := by
        simp only [planarComparisonError]
        rw [lintegral_add_right _ hm6, lintegral_add_left measurable_const, lintegral_const,
          measure_univ, mul_one]
    _ ≤ _ := add_le_add (add_le_add le_rfl e4) e6
    _ ≤ _ := herr

/-- `E[ω(□_n, q)] ≤ C (|ā⁻¹ q|² + |q|²) 3^{-nα}`, from display (5.4). -/
theorem exists_integral_planarOmega_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin 2 → ℝ),
      Integrable (fun ω => planarOmega p ω ⟨n, 0⟩ q) (latticeBondLaw 2 p) ∧
      ∫ ω, planarOmega p ω ⟨n, 0⟩ q ∂(latticeBondLaw 2 p) ≤
        C * ((((planarAhom p)⁻¹ *ᵥ q) 0 ^ 2 + ((planarAhom p)⁻¹ *ᵥ q) 1 ^ 2) +
          (q 0 ^ 2 + q 1 ^ 2)) * (3 : ℝ) ^ (-(n : ℝ) * α) := by
  obtain ⟨α, C, hα0, hα, hC, h⟩ := planar_convexp hpc
  refine ⟨α, C, hα0, hα, hC, fun n q => ?_⟩
  set ξ := (planarAhom p)⁻¹ *ᵥ q with hξ
  have iν := integrable_planarNu_indicator p ⟨n, 0⟩ ξ
  have iμ := integrable_neg_planarMu_indicator hpc ⟨n, 0⟩ q
  have iνμ : Integrable (fun ω => (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      planarNu ω ⟨n, 0⟩ ξ else 0) + (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      -planarMu ω ⟨n, 0⟩ q else 0)) (latticeBondLaw 2 p) := iν.add iμ
  have hint : Integrable (fun ω => planarOmega p ω ⟨n, 0⟩ q) (latticeBondLaw 2 p) :=
    iνμ.sub (integrable_const _)
  refine ⟨hint, ?_⟩
  have hval : ∫ ω, planarOmega p ω ⟨n, 0⟩ q ∂(latticeBondLaw 2 p) =
      planarNuMean p n ξ + planarMuMean p n q - ∑ i, q i * ξ i := by
    simp only [planarOmega]
    rw [← hξ, integral_sub iνμ (integrable_const _), integral_add iν iμ, integral_const,
      probReal_univ, one_smul, ← planarNuMean_eq_integral, ← planarMuMean_eq_integral]
  have hb := h n ξ q
  have hdual : 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i = 1 / 2 * ∑ i, q i * ξ i := by
    rw [hξ, planarAhom_mulVec_inv_mulVec hpc q, ← hξ]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hdual] at hb
  rw [hval]
  have a1 := le_abs_self (planarMuMean p n q - 1 / 2 * ∑ i, q i * ξ i)
  have a2 := le_abs_self (planarNuMean p n ξ - 1 / 2 * ∑ i, q i * ξ i)
  linarith

/-- `3^{-n/2} ≤ 3^{-nα}` for `α ≤ 1/4`. -/
theorem one_div_sqrt_three_pow_le {α : ℝ} (hα : α ≤ 1 / 4) (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((3 : ℝ) ^ n) ≤ (3 : ℝ) ^ (-(n : ℝ) * α) := by
  have e : (1 : ℝ) / Real.sqrt ((3 : ℝ) ^ n) = (3 : ℝ) ^ (-(n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div,
      ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [e]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left (hα.trans (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2)) h0
  linarith

/-- `∫⁻ f⁺ ≤ (∫ f)⁺ + ∫⁻ f⁻` for an integrable real function. -/
theorem lintegral_ofReal_le_ofReal_integral_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal (∫ x, f x ∂μ) + ∫⁻ x, ENNReal.ofReal (-f x) ∂μ := by
  have e := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf
  have hfin1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hf.2.ne (lintegral_mono fun x => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hfin2 : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hf.2.ne (lintegral_mono fun x => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (neg_le_abs _))
  rw [e]
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ
      = ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal -
          (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal + (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal) := by
        rw [sub_add_cancel, ENNReal.ofReal_toReal hfin1]
    _ ≤ _ := by
        refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
        rw [ENNReal.ofReal_toReal hfin2]

/-- **Lemma 5.10 of Armstrong and Dario** (display (5.42), dimension two, `p > p_c(2)`, no other
hypothesis): there are `α ∈ (0, 1/4]` and `C` such that for every `n`, `ρ(□_n) =
sup_q |q|⁻² ω(□_n, q)₊` has a measurable majorant `M` (almost surely) with `E[M] ≤ C 3^{-nα}`. -/
theorem planar_omegadecayrate {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ n : ℕ, ∃ M : Configuration 2 → ℝ≥0∞,
      Measurable M ∧ (∀ᵐ ω ∂(latticeBondLaw 2 p), ENNReal.ofReal (planarRho p ω ⟨n, 0⟩) ≤ M ω) ∧
      ∫⁻ ω, M ω ∂(latticeBondLaw 2 p) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(n : ℝ) * α)) := by
  obtain ⟨α, C₁, hα0, hα, hC₁, hω⟩ := exists_integral_planarOmega_le hpc
  obtain ⟨CZ, hCZ, hZ⟩ := exists_lintegral_planarComparisonError_le hpc
  obtain ⟨S, hS0, hS⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((((planarAhom p)⁻¹ *ᵥ Pi.single 0 1) 0 ^ 2 +
      ((planarAhom p)⁻¹ *ᵥ Pi.single 0 1) 1 ^ 2) + 1) +
    ((((planarAhom p)⁻¹ *ᵥ Pi.single 1 1) 0 ^ 2 + ((planarAhom p)⁻¹ *ᵥ Pi.single 1 1) 1 ^ 2) + 1) :=
    ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have h8 : (0 : ℝ) ≤ 8 * S := by positivity
  refine ⟨α, 2 * C₁ * w + 2 * (8 * S) * CZ.toReal, hα0, hα, by positivity, fun n => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : Configuration 2 → ℝ, f = fun ω =>
      2 * (planarOmega p ω ⟨n, 0⟩ (Pi.single 0 1) + planarOmega p ω ⟨n, 0⟩ (Pi.single 1 1)) :=
    ⟨_, rfl⟩
  obtain ⟨hi0, hb0⟩ := hω n (Pi.single 0 1)
  obtain ⟨hi1, hb1⟩ := hω n (Pi.single 1 1)
  have hfi : Integrable f (latticeBondLaw 2 p) := by
    rw [hf]
    exact (hi0.add hi1).const_mul 2
  have hfm : Measurable f := by
    have m : ∀ q : Fin 2 → ℝ, Measurable fun ω => planarOmega p ω ⟨n, 0⟩ q := fun q =>
      ((measurable_planarNu_indicator_real ⟨n, 0⟩ _).add
        (measurable_neg_planarMu_indicator_real ⟨n, 0⟩ q)).sub measurable_const
    rw [hf]
    exact ((m _).add (m _)).const_mul 2
  have hZm := measurable_planarComparisonError ⟨n, 0⟩
  have hZfin : ∀ᵐ ω ∂(latticeBondLaw 2 p), planarComparisonError ω ⟨n, 0⟩ < ∞ :=
    ae_lt_top hZm (ne_top_of_le_ne_top (ENNReal.mul_ne_top hCZ ENNReal.ofReal_ne_top) (hZ _))
  have hgood : ∀ᵐ ω ∂(latticeBondLaw 2 p), PlanarPartitionEvent ω ∧
      planarComparisonError ω ⟨n, 0⟩ < ∞ := (ae_planarPartitionEvent hpc).and hZfin
  -- the pointwise bound
  have hpt : ∀ ω, PlanarPartitionEvent ω → planarComparisonError ω ⟨n, 0⟩ < ∞ →
      planarRho p ω ⟨n, 0⟩ ≤ f ω + 8 * S * (planarComparisonError ω ⟨n, 0⟩).toReal :=
    fun ω hP hZ' => by
      rw [hf]
      exact planarRho_le_of_partitionEvent hpc hP ⟨n, 0⟩ hZ'.ne hS0 hS
  have hneg : ∀ ω, PlanarPartitionEvent ω → planarComparisonError ω ⟨n, 0⟩ < ∞ →
      -f ω ≤ 8 * S * (planarComparisonError ω ⟨n, 0⟩).toReal := fun ω hP hZ' => by
    have := (planarRho_nonneg p ω ⟨n, 0⟩).trans (hpt ω hP hZ')
    linarith
  set t : ℝ := (3 : ℝ) ^ (-(n : ℝ) * α) with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨fun ω => ENNReal.ofReal (f ω) + ENNReal.ofReal (8 * S) * planarComparisonError ω ⟨n, 0⟩,
    (hfm.ennreal_ofReal).add (hZm.const_mul _), ?_, ?_⟩
  · filter_upwards [hgood] with ω hω'
    refine (ENNReal.ofReal_le_ofReal (hpt ω hω'.1 hω'.2)).trans ?_
    refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul h8, ENNReal.ofReal_toReal hω'.2.ne]
  · have hneg' : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (8 * S) * ∫⁻ ω, planarComparisonError ω ⟨n, 0⟩ ∂(latticeBondLaw 2 p) := by
      rw [← lintegral_const_mul _ hZm]
      refine lintegral_mono_ae ?_
      filter_upwards [hgood] with ω hω'
      refine (ENNReal.ofReal_le_ofReal (hneg ω hω'.1 hω'.2)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul h8, ENNReal.ofReal_toReal hω'.2.ne]
    have hint : ∫ ω, f ω ∂(latticeBondLaw 2 p) ≤ 2 * C₁ * w * t := by
      rw [hf, integral_const_mul, integral_add hi0 hi1]
      have e0 : ((Pi.single 0 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 0 1 : Fin 2 → ℝ) 1 ^ 2) = 1 := by
        simp
      have e1 : ((Pi.single 1 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single 1 1 : Fin 2 → ℝ) 1 ^ 2) = 1 := by
        simp
      rw [e0] at hb0
      rw [e1] at hb1
      have : C₁ * ((((planarAhom p)⁻¹ *ᵥ Pi.single 0 1) 0 ^ 2 +
            ((planarAhom p)⁻¹ *ᵥ Pi.single 0 1) 1 ^ 2) + 1) * t +
          C₁ * ((((planarAhom p)⁻¹ *ᵥ Pi.single 1 1) 0 ^ 2 +
            ((planarAhom p)⁻¹ *ᵥ Pi.single 1 1) 1 ^ 2) + 1) * t = C₁ * w * t := by
        rw [hw]
        ring
      linarith
    have hZU : ∫⁻ ω, planarComparisonError ω ⟨n, 0⟩ ∂(latticeBondLaw 2 p) ≤
        CZ * ENNReal.ofReal t :=
      (hZ _).trans (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (one_div_sqrt_three_pow_le hα n)) zero_le)
    have hsplit : ∫⁻ ω, (ENNReal.ofReal (f ω) + ENNReal.ofReal (8 * S) *
        planarComparisonError ω ⟨n, 0⟩) ∂(latticeBondLaw 2 p) =
        ∫⁻ ω, ENNReal.ofReal (f ω) ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (8 * S) * ∫⁻ ω, planarComparisonError ω ⟨n, 0⟩ ∂(latticeBondLaw 2 p) := by
      rw [lintegral_add_left hfm.ennreal_ofReal, lintegral_const_mul _ hZm]
    have hA := lintegral_ofReal_le_ofReal_integral_add hfi
    have hB : ENNReal.ofReal (8 * S) * ∫⁻ ω, planarComparisonError ω ⟨n, 0⟩ ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (8 * S * CZ.toReal * t) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * S * CZ.toReal by positivity),
        ENNReal.ofReal_mul h8, ENNReal.ofReal_toReal hCZ, mul_assoc]
      exact mul_le_mul_of_nonneg_left hZU zero_le
    rw [hsplit]
    calc ∫⁻ ω, ENNReal.ofReal (f ω) ∂(latticeBondLaw 2 p) +
          ENNReal.ofReal (8 * S) * ∫⁻ ω, planarComparisonError ω ⟨n, 0⟩ ∂(latticeBondLaw 2 p)
        ≤ ENNReal.ofReal (2 * C₁ * w * t) + ENNReal.ofReal (8 * S * CZ.toReal * t) +
            ENNReal.ofReal (8 * S * CZ.toReal * t) :=
          add_le_add (hA.trans (add_le_add (ENNReal.ofReal_le_ofReal hint) (hneg'.trans hB))) hB
      _ = ENNReal.ofReal ((2 * C₁ * w + 2 * (8 * S) * CZ.toReal) * t) := by
          have hc : 0 ≤ 8 * S * CZ.toReal * t := by positivity
          rw [← ENNReal.ofReal_add (by positivity) hc, ← ENNReal.ofReal_add (by positivity) hc]
          congr 1
          ring

end Rigidity.Proofs.Cluster
