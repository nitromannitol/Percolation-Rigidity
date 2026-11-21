import Rigidity.Proofs.Partition.GeneralMinimalScaleMain
import Rigidity.Proofs.Partition.MinimalScaleCombined

/-!
# Armstrong and Dario, Propositions 2.1 and 2.4, for general partitions

Let `G` be a random collection of good triadic cubes, measurable, whose failure events are
determined by the open edges inside the threefold enlargements (Armstrong and Dario, (2.1)) and
have probability at most `C exp(-c 3^{n s})` at scale `n`, `0 < s ≤ 1` ((2.2)). Then almost surely
the maximal stopping cubes of `G` partition `ℤᵈ`, the size of the partition cube of a vertex has a
uniform stretched-exponential moment and the partition is approximately local (Proposition 2.1,
from the stopping construction); and there is one random scale `M` with a stretched-exponential
moment such that, whenever `M < 3ᵐ`, `∑_{x ∈ Q_m} size(x)^τ ≤ C' 3^{d m}` and every partition
cube meeting `Q_m` has side at most `3^{α m}` (Proposition 2.4, with `τ = t + d` and
`α = d / (d + t)`).
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 2.1**, for a general random collection of good cubes with
stretched-exponential failure probabilities. -/
theorem partition_estimates_general (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω}) {C1 c s0 : ℝ} (hC1 : 0 ≤ C1)
    (hc : 0 < c) (hs0 : 0 < s0)
    (hq : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))) :
    (∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (G ω) x / θ) ^ s0)) μ ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (G ω) x / θ) ^ s0) ∂μ) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      μ {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * ((3 : ℝ) ^ s0) ^ n))) := by
  have hprob : ∀ T : TriadicCube d, μ {ω | T ∉ G ω} ≤
      ENNReal.ofReal C1 * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
    intro T
    rw [← ENNReal.ofReal_mul hC1]
    exact hq T
  refine ⟨TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ G (ENNReal.ofReal C1)
      ENNReal.ofReal_ne_top s0 c hs0 hc hprob,
    TriadicCube.uniform_stoppingSize_exp_moment μ G hGm (ENNReal.ofReal C1)
      ENNReal.ofReal_ne_top s0 c hs0 hc hprob, ?_⟩
  exact TriadicCube.exists_measure_localGoodCentered_boundaryInterior_discrepancy_le hd μ G
    (ENNReal.ofReal C1) ENNReal.ofReal_ne_top ((3 : ℝ) ^ s0) c
    (Real.one_lt_rpow (by norm_num) hs0) hc (fun T => by
      have h := hprob T
      rwa [← Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num)] at h)

/-- Markov's inequality for a stretched-exponential moment bounded by two. -/
theorem measure_lt_le_of_exp_rpow_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} {θ s0 : ℝ} (hθ : 0 < θ)
    (hs0 : 0 < s0) (hint : Integrable (fun ω => Real.exp ((f ω / θ) ^ s0)) μ)
    (hle : (∫ ω, Real.exp ((f ω / θ) ^ s0) ∂μ) ≤ 2) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < f ω} ≤ ENNReal.ofReal (2 * Real.exp (-((t / θ) ^ s0))) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos ((f ω / θ) ^ s0)).le) hint
    (Real.exp ((t / θ) ^ s0))
  have hsub : {ω | t < f ω} ⊆ {ω | Real.exp ((t / θ) ^ s0) ≤ Real.exp ((f ω / θ) ^ s0)} := by
    intro ω hω
    apply Real.exp_le_exp.2
    exact Real.rpow_le_rpow (div_nonneg ht hθ.le)
      (div_le_div_of_nonneg_right (le_of_lt hω) hθ.le) hs0.le
  have hpos := Real.exp_pos ((t / θ) ^ s0)
  have hreal : μ.real {ω | Real.exp ((t / θ) ^ s0) ≤ Real.exp ((f ω / θ) ^ s0)} ≤
      2 * Real.exp (-((t / θ) ^ s0)) := by
    rw [Real.exp_neg, le_mul_inv_iff₀ hpos]
    linarith
  calc μ {ω | t < f ω} ≤ μ {ω | Real.exp ((t / θ) ^ s0) ≤ Real.exp ((f ω / θ) ^ s0)} :=
        measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | Real.exp ((t / θ) ^ s0) ≤ Real.exp ((f ω / θ) ^ s0)}) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((t / θ) ^ s0))) := ENNReal.ofReal_le_ofReal hreal

/-- The exceptional events of the bound on the largest cube of a general partition. -/
theorem exists_events_stoppingSize_le_general (μ : Measure (Configuration d))
    [IsProbabilityMeasure μ] (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω}) {θ s0 : ℝ} (hθ : 0 < θ)
    (hs0 : 0 < s0)
    (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (G ω) x / θ) ^ s0)) μ ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (G ω) x / θ) ^ s0) ∂μ) ≤ 2)
    (A : ℕ → TriadicCube d) (hA : ∀ m, (A m).scale = m) {α : ℝ} (hα : 0 < α) :
    ∃ E : ℕ → Set (Configuration d), (∀ m, MeasurableSet (E m)) ∧
      (∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ m, μ (E m) ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ (α * s0)))) ∧
      ∀ (ω : Configuration d) (m : ℕ), ω ∉ E m → ∀ x ∈ (A m).vertices,
        TriadicCube.stoppingSize (G ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  classical
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (G ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x => TriadicCube.measurable_stoppingSize _ hGm x
  set E : ℕ → Set (Configuration d) :=
    fun m => {ω | ∃ x ∈ (A m).vertices, ((3 : ℝ) ^ m) ^ α < f x ω} with hEdef
  have hE_eq : ∀ m, E m =
      ⋃ x ∈ (A m).toIntegerCube.vertices, {ω | ((3 : ℝ) ^ m) ^ α < f x ω} := by
    intro m
    ext ω
    simp only [hEdef, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
      TriadicCube.mem_toIntegerCube_vertices]
  have hEm : ∀ m, MeasurableSet (E m) := by
    intro m
    rw [hE_eq]
    exact Finset.measurableSet_biUnion _ fun x _ => measurableSet_lt measurable_const (hfm x)
  have hαs : 0 < α * s0 := mul_pos hα hs0
  have hθs : 0 < θ ^ s0 := Real.rpow_pos_of_pos hθ s0
  set C' : ℝ := 2 * (((⌈(d : ℝ) / (α * s0)⌉₊).factorial : ℝ) /
    (1 / θ ^ s0 / 2) ^ ⌈(d : ℝ) / (α * s0)⌉₊) with hC'def
  have hE : ∀ m, μ (E m) ≤ ENNReal.ofReal C' *
      ENNReal.ofReal (Real.exp (-(1 / θ ^ s0 / 2) * ((3 : ℝ) ^ m) ^ (α * s0))) := by
    intro m
    have hcard : ((A m).toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
      rw [IntegerCube.card_vertices]
      change (((3 ^ (A m).scale) ^ d : ℕ) : ℝ) = _
      rw [hA m]
      push_cast
      ring
    have hpow : (((3 : ℝ) ^ m) ^ α / θ) ^ s0 = ((3 : ℝ) ^ m) ^ (α * s0) / θ ^ s0 := by
      rw [Real.div_rpow (by positivity) hθ.le, ← Real.rpow_mul (by positivity)]
    calc μ (E m) ≤ ∑ x ∈ (A m).toIntegerCube.vertices, μ {ω | ((3 : ℝ) ^ m) ^ α < f x ω} := by
          rw [hE_eq]
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ (A m).toIntegerCube.vertices,
            ENNReal.ofReal (2 * Real.exp (-((((3 : ℝ) ^ m) ^ α / θ) ^ s0))) :=
          Finset.sum_le_sum fun x _ =>
            measure_lt_le_of_exp_rpow_moment μ hθ hs0 (hmom x).1 (hmom x).2 (by positivity)
      _ = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d *
            (2 * Real.exp (-(((3 : ℝ) ^ m) ^ (α * s0) / θ ^ s0)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard, hpow]
      _ ≤ ENNReal.ofReal (C' * Real.exp (-(1 / θ ^ s0 / 2) * ((3 : ℝ) ^ m) ^ (α * s0))) :=
          ENNReal.ofReal_le_ofReal (pow_mul_exp_neg_rpow_le hαs hθs m)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
  exact ⟨E, hEm, ⟨C', 1 / θ ^ s0 / 2, by positivity, by positivity, hE⟩,
    fun ω m hω x hx => not_lt.1 fun hlt => hω ⟨x, hx, hlt⟩⟩

/-- The exceptional events of the bound on `∑_{x ∈ Q_m} size(x)^τ` for a general partition. -/
theorem exists_events_sum_stoppingSize_le (hd : 0 < d) (p : unitInterval)
    (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) :
    ∃ E : ℕ → Set (Configuration d), (∀ m, MeasurableSet (E m)) ∧
      (∃ (C : ℝ≥0∞) (c' s : ℝ), C ≠ ∞ ∧ 0 < c' ∧ 0 < s ∧ ∀ m, latticeBondLaw d p (E m) ≤
        C * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s))) ∧
      ∃ Cf : ℝ, ∀ (ω : Configuration d) (m : ℕ), ω ∉ E m →
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          TriadicCube.stoppingSize (G ω) x ^ τ ≤ Cf * 3 ^ (d * m) := by
  classical
  set μ := latticeBondLaw d p with hμdef
  have hae : ∀ᵐ ω ∂μ, ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched μ G (ENNReal.ofReal C1)
      ENNReal.ofReal_ne_top s0 c hs0 hc (fun R => by
        rw [← ENNReal.ofReal_mul hC1]
        exact hq R)
  have hd1 : 1 ≤ d := hd
  set K : ℕ := 2 * (d + τ + 1) with hKdef
  have hK : 0 < K := by omega
  obtain ⟨j0, hj0⟩ :=
    exists_large_scale_exp_rpow_le (Real.exp 1 * 25 ^ d * C1) c s0 (by positivity) hc hs0 (τ + 1)
  set Cfin : ℝ := (j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d + 1 with hCfin
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (G ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x => TriadicCube.measurable_stoppingSize _ hGm x
  set E : ℕ → Set (Configuration d) := fun m =>
    {ω | Cfin * 3 ^ (d * m) < ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ}
    with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m =>
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun x _ => (hfm x).pow_const τ)
  -- the scale inequalities
  have hexpK : ∀ m j, j < m / K → (τ + 1) * (j + 1) + d * j + m / K ≤ d * m := by
    intro m j hj
    have h1 : (j + 1) * K ≤ m := (Nat.le_div_iff_mul_le hK).1 hj
    have h2 : m / K * K ≤ m := Nat.div_mul_le_self m K
    have h3 : m ≤ d * m := Nat.le_mul_of_pos_left m (by omega)
    have hKe : K = 2 * (d + τ + 1) := hKdef
    rw [hKe] at h1
    have h2' : m / K * (2 * (d + τ + 1)) ≤ m := by
      calc m / K * (2 * (d + τ + 1)) = m / K * K := by rw [← hKe]
        _ ≤ m := h2
    have ha : (τ + 1) * (j + 1) + d * j + d = (j + 1) * (d + τ + 1) := by ring
    have hb : m / K ≤ m / K * (d + τ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hc1 : (j + 1) * (2 * (d + τ + 1)) = 2 * ((j + 1) * (d + τ + 1)) := by ring
    have hd1' : m / K * (2 * (d + τ + 1)) = 2 * (m / K * (d + τ + 1)) := by ring
    omega
  set Big : ℕ → Set (Configuration d) := fun m =>
    {ω | ∃ T : TriadicCube d, m / K ≤ T.scale ∧ T ∉ G ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} with hBigdef
  set Mid : ℕ → Set (Configuration d) := fun m =>
    ⋃ j ∈ Finset.Ico j0 (m / K), ⋃ r : Fin d → Fin 3,
      {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classCount (fun T => T ∉ G ω) (originCube d m) m j r}
    with hMiddef
  set PE : Set (Configuration d) :=
    {ω | ∀ x : Vertex d, ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)}
    with hPEdef
  have hsub : ∀ m, E m ⊆ PEᶜ ∪ (Big m ∪ Mid m) := by
    intro m ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hP, hBig, hMid⟩ := hcon
    have hfar : ∀ T : TriadicCube d, m / K ≤ T.scale → T ∉ G ω →
        ∀ x ∈ (⟨m, 0⟩ : TriadicCube d).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side :=
      fun T hT hbad x hx hnear => hBig ⟨T, hT, hbad, x, hx, hnear⟩
    have hmid : ∀ j, j0 ≤ j → j < m / K → ∀ r,
        classCount (fun T => T ∉ G ω) (originCube d m) m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) := by
      intro j hj0' hjJ r
      by_contra hge
      apply hMid
      simp only [hMiddef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_Ico]
      exact ⟨j, ⟨hj0', hjJ⟩, r, not_lt.1 hge⟩
    have h1 := sum_stoppingSize_pow_le hP (originCube d m) m (m / K) τ rfl hfar
    have h2 := sum_weights_le_of_counts (fun T => T ∉ G ω) (originCube d m) m (m / K) j0 τ (Nat.div_le_self m K)
      (fun j hj => le_trans (Nat.le_add_right _ _) (hexpK m j hj)) hmid
    have hω' : Cfin * 3 ^ (d * m) <
        ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ := hω
    have hexpand : ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d + 1) * 3 ^ (d * m) =
        3 ^ (d * m) + ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d) * 3 ^ (d * m) := by ring
    have h3 : ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ ≤ Cfin * 3 ^ (d * m) := by
      rw [hCfin, hexpand]
      refine le_trans h1 (add_le_add le_rfl (le_trans (le_of_eq ?_) h2))
      refine Finset.sum_congr rfl fun j _ => ?_
      congr
    exact absurd h3 (not_le.2 hω')
  -- the probability of the failure events
  have hnull : μ PEᶜ = 0 := ae_iff.1 hae
  set b : ℝ := (3 : ℝ) ^ s0 with hbdef
  have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) hs0
  have hb3 : b ≤ 3 := by
    rw [hbdef]
    calc (3 : ℝ) ^ s0 ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 3 := Real.rpow_one 3
  set Gs : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k with hGdef
  have hG : Gs ≠ ∞ := stretched_exp_geometric_sum_ne_top b c hb1 hc
  set c' : ℝ := min (c / 3 / 2) (1 / 3 / 2) with hc'def
  have hc' : 0 < c' := lt_min (by positivity) (by norm_num)
  set N1 : ℕ := ⌈(d : ℝ) * K / s0⌉₊ with hN1
  set N2 : ℕ := ⌈(K : ℝ) / s0⌉₊ with hN2
  set D1 : ℝ := (N1.factorial : ℝ) / (c / 3 / 2) ^ N1 with hD1
  set D2 : ℝ := (N2.factorial : ℝ) / (1 / 3 / 2) ^ N2 with hD2
  set Ctot : ℝ≥0∞ := ENNReal.ofReal (25 ^ d * C1 * D1) * Gs + ENNReal.ofReal (3 ^ d * D2)
    with hCtot
  have hCtot_ne : Ctot ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG, ENNReal.ofReal_ne_top⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hE : ∀ m, μ (E m) ≤
      Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ (s0 / K))) := by
    intro m
    set x : ℝ := ((3 : ℝ) ^ m) ^ (s0 / K) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have h3m : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
    have hxr : x = (3 : ℝ) ^ ((m : ℝ) * (s0 / K)) := by
      rw [hxdef, ← Real.rpow_natCast 3 m, ← Real.rpow_mul (by norm_num)]
    have hmK : (m : ℝ) / K ≤ ((m / K : ℕ) : ℝ) + 1 := by
      have h1 := Nat.div_add_mod m K
      have h2 := Nat.mod_lt m hK
      have h3 : (m : ℝ) ≤ K * (((m / K : ℕ) : ℝ) + 1) := by
        have : m ≤ K * (m / K + 1) := by
          rw [Nat.mul_add, mul_one]
          omega
        exact_mod_cast this
      rw [div_le_iff₀ hKr]
      linarith
    -- `x ≤ 3 b^J`
    have hxb : x ≤ 3 * b ^ (m / K) := by
      have hbJ : b ^ (m / K) = (3 : ℝ) ^ (s0 * ((m / K : ℕ) : ℝ)) := by
        rw [hbdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [hxr, hbJ]
      have hexp : (m : ℝ) * (s0 / K) ≤ s0 * ((m / K : ℕ) : ℝ) + 1 := by
        have : (m : ℝ) * (s0 / K) = s0 * ((m : ℝ) / K) := by ring
        rw [this]
        nlinarith
      calc (3 : ℝ) ^ ((m : ℝ) * (s0 / K)) ≤ (3 : ℝ) ^ (s0 * ((m / K : ℕ) : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = 3 * (3 : ℝ) ^ (s0 * ((m / K : ℕ) : ℝ)) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_one]
            ring
    have hx3 : x ≤ 3 * 3 ^ (m / K) := by
      have : b ^ (m / K) ≤ (3 : ℝ) ^ (m / K) := pow_le_pow_left₀ (by positivity) hb3 _
      linarith
    -- polynomial factors
    have hP1 : (3 : ℝ) ^ (d * m) ≤ x ^ N1 := by
      have hN : (d : ℝ) ≤ s0 / K * N1 := by
        have h := Nat.le_ceil ((d : ℝ) * K / s0)
        rw [div_le_iff₀ hs0] at h
        rw [div_mul_eq_mul_div, le_div_iff₀ hKr]
        linarith
      calc (3 : ℝ) ^ (d * m) = ((3 : ℝ) ^ m) ^ ((d : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, ← pow_mul, mul_comm]
        _ ≤ ((3 : ℝ) ^ m) ^ (s0 / K * N1) := Real.rpow_le_rpow_of_exponent_le h3m hN
        _ = x ^ N1 := by rw [hxdef, Real.rpow_mul (by positivity), Real.rpow_natCast]
    have hP2 : (m : ℝ) ≤ x ^ N2 := by
      have hN : (1 : ℝ) ≤ s0 / K * N2 := by
        have h := Nat.le_ceil ((K : ℝ) / s0)
        rw [div_le_iff₀ hs0] at h
        rw [div_mul_eq_mul_div, le_div_iff₀ hKr]
        linarith
      calc (m : ℝ) ≤ (3 : ℝ) ^ m := by
            exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le
        _ = ((3 : ℝ) ^ m) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((3 : ℝ) ^ m) ^ (s0 / K * N2) := Real.rpow_le_rpow_of_exponent_le h3m hN
        _ = x ^ N2 := by rw [hxdef, Real.rpow_mul (by positivity), Real.rpow_natCast]
    have hexp1 : Real.exp (-(c / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (c / 3 / 2) (1 / 3 / 2)])
    have hexp2 : Real.exp (-(1 / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (c / 3 / 2) (1 / 3 / 2)])
    -- the large failure
    have hbig : μ (Big m) ≤ ENNReal.ofReal (25 ^ d * C1 * D1) * Gs *
        ENNReal.ofReal (Real.exp (-c' * x)) := by
      refine (measure_exists_notMem_near_le p G hC1 hc hs0 hq (originCube d m) m (m / K)
        le_rfl).trans ?_
      have hpoly := mul_exp_neg_le_of_le_pow hx0 hP1 hxb hc
      rw [← hD1] at hpoly
      have hreal : 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * b ^ (m / K)) ≤
          25 ^ d * C1 * D1 * Real.exp (-c' * x) := by
        have h25 : (0 : ℝ) ≤ 25 ^ d * C1 := by positivity
        calc 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * b ^ (m / K))
            = 25 ^ d * C1 * ((3 : ℝ) ^ (d * m) * Real.exp (-c * b ^ (m / K))) := by ring
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-(c / 3 / 2) * x)) :=
              mul_le_mul_of_nonneg_left hpoly h25
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-c' * x)) := by gcongr
          _ = _ := by ring
      calc ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
            ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s0) ^ (m / K))) * Gs
          = ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * b ^ (m / K))) * Gs :=
            congrArg (· * Gs) (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (25 ^ d * C1 * D1 * Real.exp (-c' * x)) * Gs := by gcongr
        _ = _ := by
            rw [ENNReal.ofReal_mul (p := 25 ^ d * C1 * D1) (by positivity)]
            ring
    -- many failures in a residue class
    have hmid : μ (Mid m) ≤ ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x)) := by
      have hterm : ∀ j ∈ Finset.Ico j0 (m / K), ∀ r : Fin d → Fin 3,
          μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classCount (fun T => T ∉ G ω) (originCube d m) m j r} ≤
            ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (m / K))) := by
        intro j hj r
        rw [Finset.mem_Ico] at hj
        have hjm := hexpK m j hj.2
        have hjm0 : j ≤ m := le_trans hj.2.le (Nat.div_le_self m K)
        have h1 : d * (m - j) + d * j = d * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hjm0]
        have hjm' : (τ + 1) * (j + 1) ≤ d * (m - j) := by linarith
        refine (measure_classCount_ge_le p G hloc hC1 hq (hj0 j hj.1) hjm' r).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have hle : m / K ≤ d * (m - j) - (τ + 1) * (j + 1) :=
          Nat.le_sub_of_add_le (by linarith)
        have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hle
        linarith
      have hsumE : μ (Mid m) ≤ ENNReal.ofReal (((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d *
          Real.exp (-(3 : ℝ) ^ (m / K))) := by
        calc μ (Mid m) ≤ ∑ j ∈ Finset.Ico j0 (m / K), ∑ r : Fin d → Fin 3,
              μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤
                classCount (fun T => T ∉ G ω) (originCube d m) m j r} :=
            (measure_biUnion_finset_le _ _).trans
              (Finset.sum_le_sum fun j _ => measure_iUnion_fintype_le _ _)
          _ ≤ ∑ j ∈ Finset.Ico j0 (m / K), ∑ _r : Fin d → Fin 3,
              ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (m / K))) :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun r _ => hterm j hj r
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            ring
      have hcard : ((Finset.Ico j0 (m / K)).card : ℝ) ≤ m := by
        have h1 : (Finset.Ico j0 (m / K)).card ≤ m := by
          rw [Nat.card_Ico]
          have := Nat.div_le_self m K
          omega
        exact_mod_cast h1
      have hpoly := mul_exp_neg_le_of_le_pow hx0 hP2 hx3 one_pos
      rw [← hD2] at hpoly
      have hreal : ((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K)) ≤
          3 ^ d * D2 * Real.exp (-c' * x) := by
        have he : Real.exp (-(3 : ℝ) ^ (m / K)) = Real.exp (-1 * (3 : ℝ) ^ (m / K)) := by
          congr 1
          ring
        have h3d : (0 : ℝ) ≤ 3 ^ d := by positivity
        calc ((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K))
            ≤ (m : ℝ) * 3 ^ d * Real.exp (-(3 : ℝ) ^ (m / K)) := by gcongr
          _ = 3 ^ d * ((m : ℝ) * Real.exp (-1 * (3 : ℝ) ^ (m / K))) := by rw [he]; ring
          _ ≤ 3 ^ d * (D2 * Real.exp (-(1 / 3 / 2) * x)) :=
              mul_le_mul_of_nonneg_left hpoly h3d
          _ ≤ 3 ^ d * (D2 * Real.exp (-c' * x)) := by gcongr
          _ = _ := by ring
      refine hsumE.trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    calc μ (E m) ≤ μ (PEᶜ ∪ (Big m ∪ Mid m)) := measure_mono (hsub m)
      _ ≤ μ PEᶜ + (μ (Big m) + μ (Mid m)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (25 ^ d * C1 * D1) * Gs * ENNReal.ofReal (Real.exp (-c' * x)) +
            ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x))) := by
          rw [hnull]
          exact add_le_add le_rfl (add_le_add hbig hmid)
      _ = Ctot * ENNReal.ofReal (Real.exp (-c' * x)) := by
          rw [hCtot]
          ring
  refine ⟨E, hEm, ⟨Ctot, c', s0 / K, hCtot_ne, hc', by positivity, hE⟩, Cfin,
    fun ω m hω => ?_⟩
  have h : ¬ (Cfin * 3 ^ (d * m) <
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ) := hω
  exact not_lt.1 h

/-- **Armstrong and Dario, Proposition 2.4**, for a general random collection of good cubes
satisfying (2.1) and (2.2) with `0 < s ≤ 1`: for every `τ ∈ ℕ` and `α > 0` there are `C`, `s' > 0`
and one measurable random scale `M` with a stretched-exponential moment of order `s'` such that,
almost surely, whenever `M < 3ᵐ`, `∑_{x ∈ Q_m} size(x)^τ ≤ C 3^{d m}` and every vertex of `Q_m` has
stopping size at most `3^{α m}`. -/
theorem exists_minimalScale_general (hd : 0 < d) (p : unitInterval)
    (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ C s : ℝ, 0 < s ∧ ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ : ℝ, 0 < θ ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          TriadicCube.stoppingSize (G ω) x ^ τ ≤ C * 3 ^ (d * m) ∧
        ∀ x ∈ (originCube d m).vertices,
          TriadicCube.stoppingSize (G ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  set μ := latticeBondLaw d p with hμdef
  obtain ⟨-, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates_general hd μ G hGm hC1 hc hs0 hq
  obtain ⟨E1, hE1m, ⟨C1', c1, s1, hC1', hc1, hs1', hE1⟩, Cf, hCf⟩ :=
    exists_events_sum_stoppingSize_le hd p G hGm hloc hC1 hc hs0 hs1 hq τ
  obtain ⟨E2, hE2m, ⟨C2, c2, hC2, hc2, hE2⟩, hE2prop⟩ :=
    exists_events_stoppingSize_le_general μ G hGm hθ hs0 hmom (originCube d) (fun _ => rfl) hα
  have hαs : 0 < α * s0 := mul_pos hα hs0
  set s : ℝ := min s1 (α * s0) with hsdef
  have hs : 0 < s := lt_min hs1' hαs
  set c' : ℝ := min c1 c2 with hcdef
  have hc' : 0 < c' := lt_min hc1 hc2
  set E : ℕ → Set (Configuration d) := fun m => E1 m ∪ E2 m with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE1m m).union (hE2m m)
  have hmono : ∀ (m : ℕ) {s' c'' : ℝ}, s ≤ s' → c' ≤ c'' →
      ENNReal.ofReal (Real.exp (-c'' * ((3 : ℝ) ^ m) ^ s')) ≤
        ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s)) := by
    intro m s' c'' hs' hc''
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have h1 : ((3 : ℝ) ^ m) ^ s ≤ ((3 : ℝ) ^ m) ^ s' :=
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hs'
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ s := by positivity
    nlinarith
  have hE : ∀ m, μ (E m) ≤ (C1' + ENNReal.ofReal C2) *
      ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s)) := by
    intro m
    calc μ (E m) ≤ μ (E1 m) + μ (E2 m) := measure_union_le _ _
      _ ≤ C1' * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s)) := by
          gcongr
          · exact (hE1 m).trans
              (mul_le_mul' le_rfl (hmono m (min_le_left _ _) (min_le_left _ _)))
          · exact (hE2 m).trans
              (mul_le_mul' le_rfl (hmono m (min_le_right _ _) (min_le_right _ _)))
      _ = _ := by ring
  obtain ⟨θ', hθ', hint, hle⟩ := exceptionalScale_exp_moment μ E hEm (C1' + ENNReal.ofReal C2)
    (ENNReal.add_ne_top.2 ⟨hC1', ENNReal.ofReal_ne_top⟩) s c' hs hc' hE
  refine ⟨Cf, s, hs, exceptionalScale E, measurable_exceptionalScale E hEm,
    ⟨θ', hθ', hint, hle⟩, Filter.Eventually.of_forall fun ω m hm => ?_⟩
  have hnot : ω ∉ E m := by
    intro hωE
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hm (not_lt.2 h3)
  exact ⟨hCf ω m fun h => hnot (Or.inl h), hE2prop ω m fun h => hnot (Or.inr h)⟩

end Rigidity.Percolation
