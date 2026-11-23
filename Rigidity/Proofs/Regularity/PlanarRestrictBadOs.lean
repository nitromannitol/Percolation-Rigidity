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

/-- A union over a finite set of events of probability at most `b`. -/
theorem measure_biUnion_le_card_mul {α : Type*} {p : unitInterval} (S : Finset α)
    (f : α → Set (Configuration 2)) {b : ℝ} (h : ∀ a ∈ S, latticeBondLaw 2 p (f a) ≤
      ENNReal.ofReal b) :
    latticeBondLaw 2 p (⋃ a ∈ S, f a) ≤ ENNReal.ofReal (S.card * b) := by
  refine (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum h).trans (le_of_eq ?_))
  rw [Finset.sum_const, nsmul_eq_mul]
  rcases le_or_gt 0 b with hb | hb
  · rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_of_nonpos hb.le, ENNReal.ofReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hb.le), mul_zero]

/-- **The probability of the measurable proxy of the bad event of Lemma 5.5.** -/
theorem exists_measure_restrictBadProxy_le {p : unitInterval}
    {Gc Gr : Configuration 2 → Set (TriadicCube 2)} {θc sc θr sr : ℝ} (hθc : 0 < θc)
    (hsc : 0 < sc) (hθr : 0 < θr) (hsr : 0 < sr)
    (hmomc : ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (Gc ω) x / θc) ^ sc))
        (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (Gc ω) x / θc) ^ sc) ∂latticeBondLaw 2 p) ≤ 2)
    (hmomr : ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (Gr ω) x / θr) ^ sr))
        (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (Gr ω) x / θr) ^ sr) ∂latticeBondLaw 2 p) ≤ 2)
    {C₂ Cτ Cr : ℝ} {τ ρ : ℕ} {D₂ Dτ Dr : ℝ≥0∞} (hD₂ : D₂ ≠ ∞) (hDτ : Dτ ≠ ∞) (hDr : Dr ≠ ∞)
    {c₂ cτ cr σ₂ στ σr : ℝ} (hc₂ : 0 < c₂) (hcτ : 0 < cτ) (hcr : 0 < cr) (hσ₂ : 0 < σ₂)
    (hστ : 0 < στ) (hσr : 0 < σr)
    (h2 : ∀ R : TriadicCube 2, latticeBondLaw 2 p {ω | C₂ * 3 ^ (2 * R.scale) <
      ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (Gc ω) x ^ 2} ≤
        D₂ * ENNReal.ofReal (Real.exp (-c₂ * ((3 : ℝ) ^ R.scale) ^ σ₂)))
    (hτ : ∀ R : TriadicCube 2, latticeBondLaw 2 p {ω | Cτ * 3 ^ (2 * R.scale) <
      ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (Gc ω) x ^ τ} ≤
        Dτ * ENNReal.ofReal (Real.exp (-cτ * ((3 : ℝ) ^ R.scale) ^ στ)))
    (hr : ∀ R : TriadicCube 2, latticeBondLaw 2 p {ω | Cr * 3 ^ (2 * R.scale) <
      ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (Gr ω) x ^ ρ} ≤
        Dr * ENNReal.ofReal (Real.exp (-cr * ((3 : ℝ) ^ R.scale) ^ σr))) :
    ∃ C c σ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < σ ∧ ∀ (U : TriadicCube 2) (n : ℕ),
      9 * U.scale ≤ 10 * n → n < U.scale →
      latticeBondLaw 2 p (restrictBadProxy Gc Gr C₂ Cτ Cr τ ρ U n) ≤
        ENNReal.ofReal (C * Real.exp (-c * ((3 : ℝ) ^ n) ^ σ)) := by
  set μ := latticeBondLaw 2 p with hμ
  -- the rates and the exponents
  set aA := (θc ^ sc)⁻¹ * (3 : ℝ) ^ (-sc) with haA
  set aB := c₂ * (3 : ℝ) ^ (-σ₂) with haB
  set aC := cτ * (3 : ℝ) ^ (-στ) with haC
  set aD := (θr ^ sr)⁻¹ * (3 : ℝ) ^ (-sr) with haD
  set aE := cr * (3 : ℝ) ^ (-σr) with haE
  set a := min aA (min aB (min aC (min aD aE))) with ha
  set σ := min (sc / 6) (min (σ₂ / 6) (min (στ / 6) (min (sr / 6) (σr / 6)))) with hσ
  have ha0 : 0 < a := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  have hσ0 : 0 < σ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  obtain ⟨K, hK, hKb⟩ := exists_rpow_mul_exp_le (a := (4 : ℝ)) ha0 hσ0
  set D : ℝ := 4 + D₂.toReal + Dτ.toReal + Dr.toReal with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * K, a / 2, σ, mul_nonneg hD0 hK, by positivity, hσ0, fun U n hmn hnm => ?_⟩
  set X : ℝ := (3 : ℝ) ^ n with hX
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  set E : ℝ := Real.exp (-a * X ^ σ) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  -- the comparison of a stretched exponential at a smaller scale
  have hcmp : ∀ (g : ℕ) {c' σ' : ℝ}, n ≤ 6 * g + 6 → 0 ≤ c' → 0 ≤ σ' →
      a ≤ c' * (3 : ℝ) ^ (-σ') → σ ≤ σ' / 6 → Real.exp (-c' * ((3 : ℝ) ^ g) ^ σ') ≤ E := by
    intro g c' σ' hg hc' hσ' hac hσσ
    exact (exp_neg_three_pow_le hg hc' hσ').trans (exp_neg_rpow_anti hX1 ha0.le hac hσσ)
  have hn9 : 9 ≤ n := by omega
  -- the first part
  have hA : μ (⋃ x ∈ U.toIntegerCube.vertices,
      {ω | (3 : ℝ) ^ (n / 2) < TriadicCube.stoppingSize (Gc ω) x}) ≤
      ENNReal.ofReal (U.toIntegerCube.vertices.card * (2 * E)) := by
    refine measure_biUnion_le_card_mul _ _ fun x _ => ?_
    refine (measure_lt_le_of_exp_rpow_moment μ hθc hsc (hmomc x).1 (hmomc x).2
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.div_rpow (by positivity) hθc.le, div_eq_inv_mul, ← neg_mul]
    exact hcmp (n / 2) (by omega) (by positivity) hsc.le (min_le_left _ _) (min_le_left _ _)
  -- the second part
  have hB : μ (⋃ z ∈ U.toIntegerCube.vertices, {ω | C₂ * 3 ^ (2 * ((n - n / 2) / 3)) <
      ∑ x ∈ cube ((n - n / 2) / 3) z, TriadicCube.stoppingSize (Gc ω) x ^ 2}) ≤
      ENNReal.ofReal (U.toIntegerCube.vertices.card * (D₂.toReal * E)) := by
    refine measure_biUnion_le_card_mul _ _ fun z _ => ?_
    set R : TriadicCube 2 := ⟨(n - n / 2) / 3, idx ((n - n / 2) / 3) z⟩ with hR
    have hverts : R.toIntegerCube.vertices = cube ((n - n / 2) / 3) z := Finset.ext fun x => by
      rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
    have h := h2 R
    rw [hverts] at h
    refine h.trans ?_
    conv_lhs => rw [← ENNReal.ofReal_toReal hD₂]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
    exact hcmp ((n - n / 2) / 3) (by omega) hc₂.le hσ₂.le
      ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  -- the third part
  set B : ℝ := Dτ.toReal * E + (9 : ℝ) ^ (n / 2) * (2 * E) + Dr.toReal * E with hBdef
  have hcell : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V (n / 2),
      μ ({ω | Cτ * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gc ω) x ^ τ} ∪
        (⋃ z ∈ enl 1 c.1 c.2, {ω | (3 : ℝ) ^ c.1 < TriadicCube.stoppingSize (Gr ω) z}) ∪
        {ω | Cr * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gr ω) x ^ ρ}) ≤
      ENNReal.ofReal B := by
    intro V _ c hc
    have hc1 : c.1 = n / 2 - 1 := fst_of_mem_midCells hc
    set R : TriadicCube 2 := ⟨c.1, idx c.1 c.2⟩ with hR
    have hverts : R.toIntegerCube.vertices = cube c.1 c.2 := Finset.ext fun x => by
      rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
    have hg : n ≤ 6 * c.1 + 6 := by rw [hc1]; omega
    have k1 : μ {ω | Cτ * 3 ^ (2 * c.1) <
        ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gc ω) x ^ τ} ≤
        ENNReal.ofReal (Dτ.toReal * E) := by
      have h := hτ R
      rw [hverts] at h
      refine h.trans ?_
      conv_lhs => rw [← ENNReal.ofReal_toReal hDτ]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
      exact hcmp _ hg hcτ.le hστ.le
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have k2 : μ (⋃ z ∈ enl 1 c.1 c.2, {ω | (3 : ℝ) ^ c.1 < TriadicCube.stoppingSize (Gr ω) z}) ≤
        ENNReal.ofReal ((9 : ℝ) ^ (n / 2) * (2 * E)) := by
      refine (measure_biUnion_le_card_mul (b := 2 * E) _ _ fun z _ => ?_).trans (le_of_eq ?_)
      · refine (measure_lt_le_of_exp_rpow_moment μ hθr hsr (hmomr z).1 (hmomr z).2
          (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [Real.div_rpow (by positivity) hθr.le, div_eq_inv_mul, ← neg_mul]
        exact hcmp _ hg (by positivity) hsr.le
          ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
            (min_le_left _ _))))
          ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
            (min_le_left _ _))))
      · congr 1
        rw [card_enl, hc1]
        have : n / 2 - 1 + 1 = n / 2 := by omega
        rw [this, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm (n / 2) 2]
    have k3 : μ {ω | Cr * 3 ^ (2 * c.1) <
        ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gr ω) x ^ ρ} ≤
        ENNReal.ofReal (Dr.toReal * E) := by
      have h := hr R
      rw [hverts] at h
      refine h.trans ?_
      conv_lhs => rw [← ENNReal.ofReal_toReal hDr]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
      exact hcmp _ hg hcr.le hσr.le
        ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_right _ _))))
        ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
          (min_le_right _ _))))
    calc μ _ ≤ μ _ + μ _ := measure_union_le _ _
      _ ≤ (μ _ + μ _) + μ _ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ (ENNReal.ofReal (Dτ.toReal * E) + ENNReal.ofReal ((9 : ℝ) ^ (n / 2) * (2 * E))) +
          ENNReal.ofReal (Dr.toReal * E) := add_le_add (add_le_add k1 k2) k3
      _ = ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hC : μ (⋃ V ∈ subcubesAt U n, ⋃ c ∈ midCells V (n / 2),
      ({ω | Cτ * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gc ω) x ^ τ} ∪
        (⋃ z ∈ enl 1 c.1 c.2, {ω | (3 : ℝ) ^ c.1 < TriadicCube.stoppingSize (Gr ω) z}) ∪
        {ω | Cr * 3 ^ (2 * c.1) < ∑ x ∈ cube c.1 c.2, TriadicCube.stoppingSize (Gr ω) x ^ ρ})) ≤
      ENNReal.ofReal (U.toIntegerCube.vertices.card * B) := by
    have hB0 : 0 ≤ B := by positivity
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ V ∈ subcubesAt U n, μ (⋃ c ∈ midCells V (n / 2), _)
        ≤ ∑ V ∈ subcubesAt U n, (V.toIntegerCube.vertices.card : ℝ≥0∞) * ENNReal.ofReal B := by
          refine Finset.sum_le_sum fun V hV => ?_
          refine (measure_biUnion_le_card_mul _ _ (hcell V hV)).trans ?_
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          have hVs : V.scale = n := scale_of_mem_subcubesAt hV
          gcongr
          exact_mod_cast card_midCells_le (by omega : n / 2 < V.scale)
      _ = (U.toIntegerCube.vertices.card : ℝ≥0∞) * ENNReal.ofReal B := by
          rw [← Finset.sum_mul, sum_card_subcubes hnm.le]
      _ = ENNReal.ofReal (U.toIntegerCube.vertices.card * B) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  -- the sum
  have hN : (U.toIntegerCube.vertices.card : ℝ) ≤ X ^ 3 := by
    rw [card_toIntegerCube_vertices_eq, hX, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num,
      ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h9 : (9 : ℝ) ^ (n / 2) ≤ X := by
    rw [hX, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hfinal : (U.toIntegerCube.vertices.card : ℝ) * (2 * E) +
      U.toIntegerCube.vertices.card * (D₂.toReal * E) + U.toIntegerCube.vertices.card * B ≤
      D * K * Real.exp (-(a / 2) * X ^ σ) := by
    have hNn : (0 : ℝ) ≤ U.toIntegerCube.vertices.card := Nat.cast_nonneg _
    have hD₂0 : 0 ≤ D₂.toReal := ENNReal.toReal_nonneg
    have hDτ0 : 0 ≤ Dτ.toReal := ENNReal.toReal_nonneg
    have hDr0 : 0 ≤ Dr.toReal := ENNReal.toReal_nonneg
    have e1 : (U.toIntegerCube.vertices.card : ℝ) * (2 * E) +
        U.toIntegerCube.vertices.card * (D₂.toReal * E) + U.toIntegerCube.vertices.card * B =
        U.toIntegerCube.vertices.card * ((2 + D₂.toReal + Dτ.toReal + Dr.toReal) * E +
          (9 : ℝ) ^ (n / 2) * (2 * E)) := by
      rw [hBdef]; ring
    have e2 : (2 + D₂.toReal + Dτ.toReal + Dr.toReal) * E + (9 : ℝ) ^ (n / 2) * (2 * E) ≤
        X * (D * E) := by
      have := mul_le_mul_of_nonneg_right h9 (by positivity : (0 : ℝ) ≤ 2 * E)
      have h2 : (2 + D₂.toReal + Dτ.toReal + Dr.toReal) * E ≤
          X * ((2 + D₂.toReal + Dτ.toReal + Dr.toReal) * E) :=
        le_mul_of_one_le_left (by positivity) hX1
      rw [hD]; nlinarith
    have hX4 : X ^ (4 : ℝ) * E ≤ K * Real.exp (-(a / 2) * X ^ σ) := hKb X hX1
    have e4 : X ^ (4 : ℝ) = X ^ 3 * X := by
      rw [show (4 : ℝ) = ((3 + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [e4] at hX4
    rw [e1]
    calc (U.toIntegerCube.vertices.card : ℝ) * ((2 + D₂.toReal + Dτ.toReal + Dr.toReal) * E +
          (9 : ℝ) ^ (n / 2) * (2 * E))
        ≤ X ^ 3 * (X * (D * E)) := mul_le_mul hN e2 (by positivity) (by positivity)
      _ = D * (X ^ 3 * X * E) := by ring
      _ ≤ D * (K * Real.exp (-(a / 2) * X ^ σ)) := mul_le_mul_of_nonneg_left hX4 hD0
      _ = D * K * Real.exp (-(a / 2) * X ^ σ) := by ring
  calc μ (restrictBadProxy Gc Gr C₂ Cτ Cr τ ρ U n) ≤ μ _ + μ _ := measure_union_le _ _
    _ ≤ (μ _ + μ _) + μ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (U.toIntegerCube.vertices.card * (2 * E)) +
          ENNReal.ofReal (U.toIntegerCube.vertices.card * (D₂.toReal * E))) +
          ENNReal.ofReal (U.toIntegerCube.vertices.card * B) := add_le_add (add_le_add hA hB) hC
    _ = ENNReal.ofReal (U.toIntegerCube.vertices.card * (2 * E) +
          U.toIntegerCube.vertices.card * (D₂.toReal * E) + U.toIntegerCube.vertices.card * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

end Rigidity.Proofs.Regularity
