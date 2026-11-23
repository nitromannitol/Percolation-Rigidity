import Rigidity.Proofs.Regularity.PlanarStretchedScales
import Rigidity.Proofs.Cluster.PlanarRestrictBad
import Rigidity.Proofs.Cluster.PlanarRHProb
import Rigidity.Proofs.Percolation.PlanarReachDomination

/-!
# The bad event of Lemma 5.5 has a stretched-exponentially small probability

The bad event `restrictBad` of the proof of Lemma 5.5 of Armstrong and Dario
(arXiv:1609.09431v2) is a union of conditions on the planar partition, its reach and the partition
`𝓡` of Definition 3.7 over the cells of a cube. Every condition is dominated by a condition on the
stopping sizes of a partition into good cubes whose failure events are local and
stretched-exponentially unlikely: the reach by the stopping sizes of the coarsely good cubes
(`planarReach_le_stoppingSize`), `3^{s}` by the stopping sizes of the reverse Hölder cubes. The
averages of the powers of the stopping sizes over a triadic cube exceed a constant with a
stretched-exponentially small probability (`exists_measure_sum_stoppingSize_gt_le`, the general
form of Proposition 2.4), and so do the stopping sizes themselves.

`exists_restrictBad_os`: with the constants `A₂, A_τ, K` given by these averages, the bad event is
almost surely contained in a measurable event `E U n` of probability at most
`C exp(-c 3^{n σ})`. In the source the probability of the bad event is only needed to be
polynomially small, for Lemma 5.5 in expectation; the bound here is used for Lemma 5.5 with an
`O_s` majorant.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5
open scoped Classical ENNReal

/-- `(3^g)^σ ≥ 3^{-σ} (3^n)^{σ/6}` when `n ≤ 6 g + 6`. -/
theorem three_pow_rpow_ge {n g : ℕ} (hg : n ≤ 6 * g + 6) {σ : ℝ} (hσ : 0 ≤ σ) :
    (3 : ℝ) ^ (-σ) * ((3 : ℝ) ^ n) ^ (σ / 6) ≤ ((3 : ℝ) ^ g) ^ σ := by
  rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_natCast (3 : ℝ) g, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h : (n : ℝ) ≤ 6 * g + 6 := by exact_mod_cast hg
  nlinarith

/-- The stretched exponential at the scale `g` in terms of the scale `n`. -/
theorem exp_neg_three_pow_le {n g : ℕ} (hg : n ≤ 6 * g + 6) {c σ : ℝ} (hc : 0 ≤ c)
    (hσ : 0 ≤ σ) :
    Real.exp (-c * ((3 : ℝ) ^ g) ^ σ) ≤
      Real.exp (-(c * (3 : ℝ) ^ (-σ)) * ((3 : ℝ) ^ n) ^ (σ / 6)) := by
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left (three_pow_rpow_ge hg hσ) hc
  linarith

/-- The measurable event dominating the bad event of Lemma 5.5. -/
def restrictBadProxy (Gc Gr : Configuration 2 → Set (TriadicCube 2)) (C₂ Cτ Cr : ℝ)
    (τ ρ : ℕ) (U : TriadicCube 2) (n : ℕ) : Set (Configuration 2) :=
  (⋃ x ∈ U.toIntegerCube.vertices,
      {ω | (3 : ℝ) ^ (n / 2) < TriadicCube.stoppingSize (Gc ω) x}) ∪
    (⋃ z ∈ U.toIntegerCube.vertices, {ω | C₂ * 3 ^ (2 * ((n - n / 2) / 3)) <
      ∑ x ∈ cube ((n - n / 2) / 3) z, TriadicCube.stoppingSize (Gc ω) x ^ 2}) ∪
    (⋃ V ∈ subcubesAt U n, ⋃ c ∈ midCells V (n / 2),
      ({ω | Cτ * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gc ω) x ^ τ} ∪
        (⋃ z ∈ enl 1 c.1 c.2, {ω | (3 : ℝ) ^ c.1 < TriadicCube.stoppingSize (Gr ω) z}) ∪
        {ω | Cr * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gr ω) x ^ ρ}))

theorem measurableSet_restrictBadProxy {Gc Gr : Configuration 2 → Set (TriadicCube 2)}
    (hGc : ∀ T : TriadicCube 2, MeasurableSet {ω | T ∈ Gc ω})
    (hGr : ∀ T : TriadicCube 2, MeasurableSet {ω | T ∈ Gr ω}) (C₂ Cτ Cr : ℝ) (τ ρ : ℕ)
    (U : TriadicCube 2) (n : ℕ) : MeasurableSet (restrictBadProxy Gc Gr C₂ Cτ Cr τ ρ U n) := by
  have mc := fun x => TriadicCube.measurable_stoppingSize Gc hGc x
  have mr := fun x => TriadicCube.measurable_stoppingSize Gr hGr x
  unfold restrictBadProxy
  refine ((Finset.measurableSet_biUnion _ fun x _ => measurableSet_lt measurable_const (mc x)).union
    (Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun x _ => (mc x).pow_const 2))).union
    (Finset.measurableSet_biUnion _ fun V _ => Finset.measurableSet_biUnion _ fun c _ => ?_)
  exact ((measurableSet_lt measurable_const (Finset.measurable_sum _ fun x _ => (mc x).pow_const τ)).union
    (Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const (mr z))).union
    (measurableSet_lt measurable_const (Finset.measurable_sum _ fun x _ => (mr x).pow_const ρ))

/-- A sum of powers of the reach over a cube in terms of the stopping sizes. -/
theorem lt_sum_stoppingSize_of_lt {ω : Configuration 2}
    (hH : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))
    {C : ℝ} {k : ℕ} {y : Vertex 2} {τ : ℕ}
    (h : ENNReal.ofReal (max C 0 * (cube k y).card) < ∑ x ∈ cube k y, planarReach ω x ^ τ) :
    C * 3 ^ (2 * k) < ∑ x ∈ cube k y, TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ := by
  have h1 : ∑ x ∈ cube k y, planarReach ω x ^ τ ≤
      ENNReal.ofReal (∑ x ∈ cube k y, TriadicCube.stoppingSize (planarCoarseGood ω) x ^ τ) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ =>
      pow_nonneg (TriadicCube.stoppingSize_nonneg _ x) τ]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ x)]
    exact pow_le_pow_left₀ zero_le (planarReach_le_stoppingSize hH x) τ
  have h2 := lt_of_lt_of_le h h1
  rw [ENNReal.ofReal_lt_ofReal_iff'] at h2
  have hcard : ((cube k y).card : ℝ) = (3 : ℝ) ^ (2 * k) := by
    rw [card_cube, ← pow_mul, mul_comm]
  have h3 : C * (3 : ℝ) ^ (2 * k) ≤ max C 0 * ((cube k y).card : ℝ) := by
    rw [hcard]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  linarith [h2.1]

/-- **The bad event lies in its measurable proxy.** -/
theorem restrictBad_subset_proxy {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (hH : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))
    {A₀ : ℝ}
    (hu : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarRHGood A₀ ω))
    {t : ℝ} {ρ : ℕ} (htρ : t ≤ ρ) {C₂ Cτ Cr : ℝ} {τ : ℕ} {U : TriadicCube 2} {n : ℕ}
    (hω : ω ∈ restrictBad (fun ω => stoppingScale (planarRHGood A₀ ω)) t (max Cr 0) τ
      (max Cτ 0) (max C₂ 0) U n) :
    ω ∈ restrictBadProxy planarCoarseGood (fun ω => planarRHGood A₀ ω) C₂ Cτ Cr τ ρ U n := by
  simp only [restrictBad, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion] at hω
  simp only [restrictBadProxy, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
  rcases hω with (⟨-, x, hx, hlt⟩ | ⟨z, hz, hlt⟩) | ⟨V, hV, c, hc, hlt | hlt⟩
  · refine Or.inl (Or.inl ⟨x, hx, ?_⟩)
    have hx9 : x ∈ (planarPartCube ω x).ninefold.vertices :=
      Finset.mem_coe.1 (mem_ninefold_of_near (planarPartCube_spec hP x).1 fun i => by simp)
    have h1 := three_pow_scale_le_planarReach hP hx9
    have h2 := planarReach_le_stoppingSize hH x
    have h3 : (3 : ℝ) ^ (n / 2) < 3 ^ (planarPartCube ω x).scale :=
      pow_lt_pow_right₀ (by norm_num) hlt
    have h4 := h1.trans h2
    rw [show (3 : ℝ≥0∞) ^ (planarPartCube ω x).scale =
      ENNReal.ofReal ((3 : ℝ) ^ (planarPartCube ω x).scale) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num,
      ENNReal.ofReal_le_ofReal_iff (TriadicCube.stoppingSize_nonneg _ x)] at h4
    exact lt_of_lt_of_le h3 h4
  · exact Or.inl (Or.inr ⟨z, hz, lt_sum_stoppingSize_of_lt hH hlt⟩)
  · exact Or.inr ⟨V, hV, c, hc, Or.inl (Or.inl (lt_sum_stoppingSize_of_lt hH hlt))⟩
  · refine Or.inr ⟨V, hV, c, hc, ?_⟩
    rcases hlt with ⟨z, hz, hkz⟩ | hlt
    · refine Or.inl (Or.inr ⟨z, hz, ?_⟩)
      rw [stoppingSize_eq_stoppingScale hu]
      exact pow_lt_pow_right₀ (by norm_num) hkz
    · refine Or.inr ?_
      have hcard : ((cube c.1 c.2).card : ℝ) = (3 : ℝ) ^ (2 * c.1) := by
        rw [card_cube, ← pow_mul, mul_comm]
      have h1 : ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ stoppingScale (planarRHGood A₀ ω) x) ^ t ≤
          ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (planarRHGood A₀ ω) x ^ ρ := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [stoppingSize_eq_stoppingScale hu]
        calc ((3 : ℝ) ^ stoppingScale (planarRHGood A₀ ω) x) ^ t
            ≤ ((3 : ℝ) ^ stoppingScale (planarRHGood A₀ ω) x) ^ (ρ : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) htρ
          _ = ((3 : ℝ) ^ stoppingScale (planarRHGood A₀ ω) x) ^ ρ := Real.rpow_natCast _ ρ
      have h2 : Cr * (3 : ℝ) ^ (2 * c.1) ≤ max Cr 0 * ((cube c.1 c.2).card : ℝ) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith

end Rigidity.Proofs.Regularity
