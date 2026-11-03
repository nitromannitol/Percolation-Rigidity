import Rigidity.Proofs.S3.ChemicalDistance
import Rigidity.Steps.S3.ReductionToSlopeE1
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# Lemma 3.1: a nonconstant Lipschitz harmonic function is a corrected plane of nonzero slope

Step `step:lip-in-A1` of Lemma 3.1 (paper L808, L820-824 of the corrected draft). Almost surely,
the chemical distance on the infinite cluster `𝒞_∞` is subquadratic (`ae_componentDist_le`, from
Proposition 2.3), so an `L`-Lipschitz function `u` on `𝒞_∞` satisfies
`|u(x)| ≤ |u(o)| + |L| (2d + 1) 4^d (2R)^{3/2}` on `𝒞_∞ ∩ B_R`; a harmonic such `u` therefore lies
in `A₁`. By the classification of `A₁` (Theorem 2.5, `SupercriticalBondCorrectorInput`) it is a
corrected plane `ℓ_q`; corrected planes of a given slope are unique up to constants, so `q ≠ 0`
when `u` is not constant, and every corrected plane of slope `q` is `L`-Lipschitz.

The paper's sentence "a Lipschitz harmonic function lies in `A₁`" uses the comparison of the
chemical and Euclidean distances; here it is derived from Proposition 2.3 (see
`Rigidity.Proofs.S3.ChemicalDistance`), and a subquadratic comparison suffices.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory Filter LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.External Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- Subtracting a constant from a corrected plane gives a corrected plane of the same slope. -/
theorem isCorrectedPlane_sub_const {ω : Configuration d} {C : OpenComponent ω} {q : Fin d → ℝ}
    {u : C → ℝ} (hu : IsCorrectedPlane C q u) (c : ℝ) :
    IsCorrectedPlane C q (fun x => u x - c) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · have := (harmonicGrowthSpace C 1).add_mem hu.1 (const_mem_harmonicGrowthSpace C 1 (-c))
    convert this using 1
    funext x
    simp [sub_eq_add_neg]
  · obtain ⟨R₀, hR₀, hR⟩ := hu.2 (ε / 2) (by positivity)
    refine ⟨max R₀ (2 * |c| / ε + 1), lt_of_lt_of_le hR₀ (le_max_left _ _), fun R hR' x hx => ?_⟩
    have h1 := abs_le.mp (hR R ((le_max_left _ _).trans hR') x hx)
    have h2 := (div_lt_iff₀ hε).mp
      (show 2 * |c| / ε < R by linarith [(le_max_right R₀ (2 * |c| / ε + 1)).trans hR'])
    have h3 := abs_le.mp (show |c| ≤ ε / 2 * R by linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two corrected planes of the same slope differ by a constant, when the normalized corrected
plane is unique. -/
theorem sub_eq_sub_of_isCorrectedPlane {ω : Configuration d} {C : OpenComponent ω}
    {q : Fin d → ℝ} (hplane : ∀ o : C, ∃! w : C → ℝ, IsCorrectedPlane C q w ∧ w o = 0)
    {u v : C → ℝ} (hu : IsCorrectedPlane C q u) (hv : IsCorrectedPlane C q v) (o x : C) :
    v x - v o = u x - u o := by
  obtain ⟨w, -, hw⟩ := hplane o
  have h1 := hw (fun x => u x - u o) ⟨isCorrectedPlane_sub_const hu _, sub_self _⟩
  have h2 := hw (fun x => v x - v o) ⟨isCorrectedPlane_sub_const hv _, sub_self _⟩
  exact congrFun (h2.trans h1.symm) x

/-- The growth bound `(R^2)⁻¹ (A + B (2R)^{3/2}) → 0`. -/
theorem tendsto_inv_sq_mul_add_rpow (A B : ℝ) :
    Tendsto (fun R : ℝ => (R ^ (1 + 1))⁻¹ * (A + B * (2 * R) ^ (3 / 2 : ℝ))) atTop (nhds 0) := by
  have h1 : Tendsto (fun R : ℝ => (R ^ (1 + 1))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num))
  have h2 : Tendsto (fun R : ℝ => R ^ (-(1 / 2) : ℝ)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h := (h1.const_mul A).add (h2.const_mul (B * 2 ^ (3 / 2 : ℝ)))
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr' ((eventually_gt_atTop 0).mono fun R hR => ?_)
  beta_reduce
  rw [Real.mul_rpow (by norm_num) hR.le, show (3 / 2 : ℝ) = -(1 / 2) + 2 by norm_num,
    Real.rpow_add hR, Real.rpow_two]
  field_simp
  ring

/-- Almost surely, an `L`-Lipschitz function on an infinite open cluster grows at most like
`R^{3/2}` on Euclidean balls: it satisfies the growth condition of `A₁`. -/
theorem componentL2Subpolynomial_of_isLipschitzWith {ω : Configuration d} {N₀ : ℕ}
    (hdist : ∀ N : ℕ, N₀ ≤ N → ∀ C : OpenComponent ω, C.supp.Infinite → ∀ x y : C,
      x.val ∈ cubeAt 0 N → y.val ∈ cubeAt 0 N →
        ((componentGraph C).dist x y : ℝ) ≤ (2 * d + 1) * 4 ^ d * (N : ℝ) ^ (3 / 2 : ℝ))
    {C : OpenComponent ω} (hC : C.supp.Infinite) {L : ℝ} {u : C → ℝ}
    (hlip : IsLipschitzWith C L u) (o : C) : componentL2Subpolynomial C 1 u := by
  set A := |u o|
  set B := |L| * ((2 * d + 1) * 4 ^ d)
  set No := ∑ i, (o.val i).natAbs
  refine squeeze_zero' (eventually_atTop.mpr ⟨0, fun R hR => componentL2_scaled_nonneg C 1 u hR⟩)
    (eventually_atTop.mpr ⟨(N₀ : ℝ) + No + 1, fun R hR => ?_⟩) (tendsto_inv_sq_mul_add_rpow A B)
  have hR1 : 1 ≤ R := by linarith [(by positivity : (0 : ℝ) ≤ N₀ + No)]
  set N := ⌈R⌉₊
  have hNR : (N : ℝ) ≤ 2 * R := by
    have := Nat.ceil_lt_add_one (show 0 ≤ R by linarith)
    linarith
  have hRN : R ≤ N := Nat.le_ceil R
  have hN₀ : N₀ ≤ N := by
    exact_mod_cast (show (N₀ : ℝ) ≤ N by linarith [(Nat.cast_nonneg No : (0 : ℝ) ≤ No)])
  have hoN : o.val ∈ cubeAt 0 N := fun i => by
    have hi : (o.val i).natAbs ≤ No :=
      Finset.single_le_sum (f := fun i => (o.val i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have hNo : No ≤ N := by
      exact_mod_cast (show (No : ℝ) ≤ N by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)])
    simp only [Pi.zero_apply, sub_zero, Int.abs_eq_natAbs]
    exact_mod_cast hi.trans hNo
  refine mul_le_mul_of_nonneg_left (componentBallL2_le_of_abs_le C 0 R u (by positivity)
    fun x hx => ?_) (inv_nonneg.mpr (by positivity))
  have hxN : x.val ∈ cubeAt 0 N := fun i => by
    have hx' := (mem_componentEuclideanBall C 0 R x).mp hx
    rw [dist_eq_norm] at hx'
    have hi := PiLp.norm_apply_le
      (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding (0 : Vertex d)) i
    change |(x.val i : ℝ) - ((0 : Vertex d) i : ℝ)| ≤ _ at hi
    have : |((x.val i - (0 : Vertex d) i : ℤ) : ℝ)| ≤ N := by push_cast; linarith
    exact_mod_cast this
  have hd := hdist N hN₀ C hC x o hxN hoN
  have hpow : (N : ℝ) ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNR (by norm_num)
  have hdist0 : (0 : ℝ) ≤ (componentGraph C).dist x o := Nat.cast_nonneg _
  calc |u x| ≤ |u o| + |u x - u o| := by
        have := abs_sub_abs_le_abs_sub (u x) (u o)
        linarith
    _ ≤ A + |L| * (componentGraph C).dist x o := by
        gcongr
        exact (hlip x o).trans (mul_le_mul_of_nonneg_right (le_abs_self L) hdist0)
    _ ≤ A + |L| * ((2 * d + 1) * 4 ^ d * (2 * R) ^ (3 / 2 : ℝ)) := by
        gcongr
        exact hd.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ = A + B * (2 * R) ^ (3 / 2 : ℝ) := by ring

/-- **Step `step:lip-in-A1`** of Lemma 3.1 (paper L808, L820-824). For `d ≥ 2` and
`p_c(d) < p < 1`, given Proposition 2.3 (`WellConnectedInput`) and Theorem 2.5
(`SupercriticalBondCorrectorInput`): almost surely, a nonconstant `L`-Lipschitz harmonic function
on the infinite cluster is a corrected plane `ℓ_q` (plus a constant) with `q ≠ 0`, and every
corrected plane of slope `q` is `L`-Lipschitz. -/
theorem lipschitzMemA1Step [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput)
    (hcorrector : SupercriticalBondCorrectorInput) : LipschitzMemA1Step d p := by
  filter_upwards [ae_componentDist_le hd hpc hp1 hwc, hcorrector d hd p hpc hp1]
    with ω hdist hcorr
  intro h L u hharm hlip ⟨x₀, y₀, hne⟩
  obtain ⟨N₀, hN₀⟩ := hdist
  obtain ⟨hplane, hA1⟩ := hcorr h
  obtain ⟨q, hq, -⟩ := hA1 u ⟨hharm, componentL2Subpolynomial_of_isLipschitzWith hN₀
    (uniqueInfiniteComponent_infinite h) hlip x₀⟩
  refine ⟨q, ?_, h, fun v hv a b => ?_⟩
  · rintro rfl
    apply hne
    have := sub_eq_sub_of_isCorrectedPlane (hplane 0)
      (isCorrectedPlane_const (uniqueInfiniteComponent h) (u x₀)) hq x₀ y₀
    linarith
  · have ha := sub_eq_sub_of_isCorrectedPlane (hplane q) hq hv x₀ a
    have hb := sub_eq_sub_of_isCorrectedPlane (hplane q) hq hv x₀ b
    calc |v a - v b| = |u a - u b| := by congr 1; linarith
      _ ≤ _ := hlip a b

end Rigidity.Proofs.S3
