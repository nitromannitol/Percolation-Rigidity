import Rigidity.Steps.Section5.GoodEventLowerBound
import Rigidity.Steps.Section5.LongPathRenormalized
import Rigidity.Steps.Section5.FastDecayDichotomy
import LatticeProb.Prob.Percolation.LatticeRadialTail
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# Lemma 5.25: the second good event (eq. `PG2goesto1`)

`SecondGoodEventStep` of `Rigidity/Steps/Section5/GoodEventLowerBound.lean`: from the quantitative
part of Theorem 2.5, `G_2(x, K)` fails with probability at most `C exp(-c K^s)`.

Theorem 2.5 with exponent `α = 1/2` gives a minimal scale `M ≤ O_s(C)` such that, for `r ≥ M`,
the oscillation of the corrector `χ_{e₁} = ℓ_{e₁} - x₁` on `𝒞_∞ ∩ B_r(x)` is at most `C r^{1/2}`.
For `R' ≥ K` the cube `Q_{R'}(x)` lies in `B_r(x)`, `r = 5R'`, and `x₁` oscillates by at most `2R'`
on it, so `osc_{Q_{R'}(x) ∩ 𝒞_∞} ℓ_{e₁} ≤ C (5R')^{1/2} + 2R' ≤ 4R'` once `R' ≥ 2C²`. Hence
`G_2(x, K)` holds as soon as the cluster is unique and `M ≤ 5K`, for `K ≥ 2C²`, and the Markov
inequality for `exp((M/C)^s)` bounds `P(M > 5K) ≤ 2 exp(-(5K/C)^s)`.

**Carving defect.** `(eventG2 x K)ᶜ` contains the event that there is no unique infinite cluster,
so the bound of `SecondGoodEventStep` for every `K` forces `UniqueClusterAe p`, which the
quantitative input of Theorem 2.5 (vacuous without a unique infinite cluster) does not provide.
The step therefore carries the classical input `SupercriticalBondUniqueness` as a hypothesis and is
proved here (`secondGoodEventStep`); the bound itself is `secondGoodEvent_bound`, under
`UniqueClusterAe p`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5 Rigidity.External

/-- The coordinates of a point of `Q_{R}(x)` differ from those of `x` by at most `R`. -/
theorem abs_sub_le_of_mem_cubeAt {x y : Vertex 2} {R : ℕ} (hy : y ∈ Section5.cubeAt x R) (i : Fin 2) :
    |((y i - x i : ℤ) : ℝ)| ≤ R := by
  have h := hy i
  rw [← Int.cast_abs]
  exact_mod_cast h

/-- A point within `ℓ^∞` distance `R + 1` of `x` lies in the open Euclidean ball of radius `5R`
around `x`, for `R ≥ 1`. -/
theorem norm_embedding_sub_lt {x a : Vertex 2} {R : ℝ} (hR : 1 ≤ R)
    (ha : ∀ i, |((a i - x i : ℤ) : ℝ)| ≤ R + 1) :
    ‖latticeEuclideanEmbedding a - latticeEuclideanEmbedding x‖ < 5 * R := by
  rw [← latticeEuclideanEmbedding_sub]
  have h := eucl_le_l1 (a - x)
  change ‖latticeEuclideanEmbedding (a - x)‖ ≤ ∑ i, |(((a - x) i : ℤ) : ℝ)| at h
  simp only [Fin.sum_univ_two, Pi.sub_apply] at h
  linarith [ha 0, ha 1]

/-- Every vertex of an infinite open component has a neighbour in it. -/
theorem exists_adj_of_infinite {ω : Configuration 2} {C : OpenComponent ω} (hC : C.supp.Infinite)
    (y : C) : ∃ y' : C, (componentGraph C).Adj y y' := by
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

/-- `C (5R)^{1/2} ≤ 2R` for `R ≥ 2C²`. -/
theorem mul_rpow_half_le {C R : ℝ} (hC : 0 < C) (hR : 2 * C ^ 2 ≤ R) :
    C * (5 * R) ^ (1 / 2 : ℝ) ≤ 2 * R := by
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  rw [← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (5 * R) ≤ 2 * R / C := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hR0.le (show (0 : ℝ) ≤ 4 * R - 5 * C ^ 2 by nlinarith)]
  calc C * Real.sqrt (5 * R) ≤ C * (2 * R / C) := mul_le_mul_of_nonneg_left hsq hC.le
    _ = 2 * R := by field_simp

/-- The second good event holds when the cluster is unique, the conclusion of Theorem 2.5 holds
and the minimal scale is at most `5K`, for `K ≥ 2C²`. -/
theorem mem_eventG2_of_minimalScale_le {C : ℝ} (hC : 0 < C) {x : Vertex 2} {K : ℝ}
    (hK : 2 * C ^ 2 ≤ K) (hK1 : 1 ≤ K) {M : ℝ} {ω : Configuration 2}
    (hω : ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ (1 / 2 : ℝ))
    (hh : HasUniqueInfiniteOpenComponent ω) (hM : M ≤ 5 * K) : ω ∈ eventG2 x K := by
  refine ⟨hh, fun ℓ hℓ R' hR' y z hy hz => ?_⟩
  have hR'1 : (1 : ℝ) ≤ R' := hK1.trans hR'
  obtain ⟨y', hyy'⟩ := exists_adj_of_infinite (uniqueInfiniteComponent_infinite hh) y
  have hy1 := abs_sub_add_abs_sub_eq_one_of_adj hyy'
  have hyb : ∀ i, |((y.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := fun i =>
    (abs_sub_le_of_mem_cubeAt hy i).trans (by linarith)
  have hzb : ∀ i, |((z.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := fun i =>
    (abs_sub_le_of_mem_cubeAt hz i).trans (by linarith)
  have hy'b : ∀ i, |((y'.val i - x i : ℤ) : ℝ)| ≤ (R' : ℝ) + 1 := by
    intro i
    have hi : |y.val i - y'.val i| ≤ 1 := by
      fin_cases i
      · exact le_of_le_of_eq (le_add_of_nonneg_right (abs_nonneg _)) hy1
      · exact le_of_le_of_eq (le_add_of_nonneg_left (abs_nonneg _)) hy1
    have hi' : |((y.val i - y'.val i : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast hi
    have hyx := abs_sub_le_of_mem_cubeAt hy i
    push_cast at hi' hyx ⊢
    calc |(y'.val i : ℝ) - x i| ≤ |(y'.val i : ℝ) - y.val i| + |(y.val i : ℝ) - x i| :=
          abs_sub_le _ _ _
      _ ≤ 1 + R' := by rw [abs_sub_comm]; exact add_le_add hi' hyx
      _ = R' + 1 := add_comm _ _
  have hosc := hω hh (Pi.single 0 1) ℓ hℓ (5 * R') (hM.trans (by linarith)) y z y y'
    (norm_embedding_sub_lt hR'1 hyb) (norm_embedding_sub_lt hR'1 hzb)
    (norm_embedding_sub_lt hR'1 hyb) (norm_embedding_sub_lt hR'1 hy'b) hyy'
  simp only [Fin.sum_univ_two, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), one_mul, zero_mul, add_zero, abs_one,
    abs_zero, mul_one] at hosc
  have hroot := mul_rpow_half_le hC (show 2 * C ^ 2 ≤ (R' : ℝ) by linarith)
  have hy0 := abs_sub_le_of_mem_cubeAt hy 0
  have hz0 := abs_sub_le_of_mem_cubeAt hz 0
  push_cast at hy0 hz0
  have h1 := le_abs_self ((ℓ y - (y.val 0 : ℝ)) - (ℓ z - (z.val 0 : ℝ)))
  have h2 := abs_nonneg ((ℓ y - (y.val 0 : ℝ)) - (ℓ y' - (y'.val 0 : ℝ)))
  have h3 := le_abs_self ((y.val 0 : ℝ) - x 0)
  have h4 := neg_abs_le ((z.val 0 : ℝ) - x 0)
  linarith

/-- Markov's inequality for the stretched exponential moment of the minimal scale:
`P(M > t) ≤ 2 exp(-(t/C)^s)` for `t ≥ 0`. -/
theorem measure_lt_minimalScale_le {p : unitInterval} {M : Configuration 2 → ℝ} {s C t : ℝ}
    (hs : 0 < s) (hC : 0 < C) (ht : 0 ≤ t) (hM : IsOsBond 2 p M s C) :
    latticeBondLaw 2 p {ω | t < M ω} ≤ ENNReal.ofReal (2 * Real.exp (-((t / C) ^ s))) := by
  set μ := latticeBondLaw 2 p
  set ε := Real.exp ((t / C) ^ s)
  have hε : 0 < ε := Real.exp_pos _
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => (Real.exp_pos (Real.rpow (max (M ω / C) 0) s)).le) hM.1 ε
  have hsub : {ω | t < M ω} ⊆ {ω | ε ≤ Real.exp (Real.rpow (max (M ω / C) 0) s)} := by
    intro ω hω
    have h1 : t / C ≤ M ω / C := div_le_div_of_nonneg_right (le_of_lt hω) hC.le
    have h2 : 0 ≤ t / C := div_nonneg ht hC.le
    change Real.exp ((t / C) ^ s) ≤ Real.exp ((max (M ω / C) 0) ^ s)
    rw [max_eq_left (h2.trans h1)]
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow h2 h1 hs.le)
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : μ.real {ω | ε ≤ Real.exp (Real.rpow (max (M ω / C) 0) s)} ≤ 2 / ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact hmark.trans hM.2
  calc (μ {ω | ε ≤ Real.exp (Real.rpow (max (M ω / C) 0) s)}).toReal ≤ 2 / ε := hle
    _ = 2 * Real.exp (-((t / C) ^ s)) := by rw [Real.exp_neg, div_eq_mul_inv]

/-- Eq. `PG2goesto1`: under uniqueness of the infinite cluster, the second good event fails with
probability at most `C exp(-c K^s)`. -/
theorem secondGoodEvent_bound (hQ : CorrectorQuantitativeInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hUae : UniqueClusterAe p) :
    ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (K : ℝ), 1 ≤ K →
      latticeBondLaw 2 p (eventG2 x K)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * K ^ s))) := by
  obtain ⟨s, C, hs, hC, hQx⟩ := hQ 2 le_rfl p hpc hp1 (1 / 2) (by norm_num)
  set c := (5 / C) ^ s with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) s
  set K₁ := 2 * C ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine ⟨2 * Real.exp (c * K₁ ^ s), c, s, by positivity, hc, hs, fun x K hK => ?_⟩
  obtain ⟨M, -, -, hMos, hMae⟩ := hQx x
  set μ := latticeBondLaw 2 p
  have hexp1 : 1 ≤ Real.exp (c * K₁ ^ s) :=
    Real.one_le_exp (mul_nonneg hc.le (Real.rpow_nonneg hK₁0 s))
  rcases lt_or_ge K K₁ with hKK | hKK
  · refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have hKs : K ^ s ≤ K₁ ^ s := Real.rpow_le_rpow (by linarith) hKK.le hs.le
    have h1 : 1 ≤ Real.exp (c * K₁ ^ s - c * K ^ s) :=
      Real.one_le_exp (by nlinarith)
    calc (1 : ℝ) ≤ 2 * Real.exp (c * K₁ ^ s - c * K ^ s) := by linarith
      _ = 2 * Real.exp (c * K₁ ^ s) * Real.exp (-(c * K ^ s)) := by
        rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  · have hbad := ae_iff.mp (hMae.and hUae)
    have hsub : (eventG2 x K)ᶜ ⊆ {ω | ¬ ((∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin 2 → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ (1 / 2 : ℝ)) ∧ HasUniqueInfiniteOpenComponent ω)} ∪
        {ω | 5 * K < M ω} := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, not_lt] at hn
      exact hω (mem_eventG2_of_minimalScale_le hC hKK hK hn.1.1 hn.1.2 hn.2)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [hbad, zero_add]
    refine (measure_lt_minimalScale_le hs hC (by linarith) hMos).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (5 * K / C) ^ s = c * K ^ s := by
      rw [hc_def, ← Real.mul_rpow (by positivity) (by linarith)]
      ring_nf
    rw [hpow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.exp_pos _).le hexp1) (by norm_num)

/-- `SecondGoodEventStep` of Lemma 5.25 (its hypothesis `SupercriticalBondUniqueness` gives
`UniqueClusterAe p`, see the module docstring). -/
theorem secondGoodEventStep : SecondGoodEventStep :=
  fun hUq hQ p hpc hp1 => secondGoodEvent_bound hQ hpc hp1
    ((mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).mpr
      (hUq.2 2 le_rfl p hpc hp1))

end Rigidity.Proofs.Section5
