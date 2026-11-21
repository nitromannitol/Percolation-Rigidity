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
  obtain ⟨Cfin, Ctot, hCtot_ne, c', hc', hE⟩ :=
    exists_measure_sum_stoppingSize_gt_le hd p G hGm hloc hC1 hc hs0 hs1 hq τ
  refine ⟨fun m => {ω | Cfin * 3 ^ (d * m) < ∑ x ∈ (originCube d m).toIntegerCube.vertices,
      TriadicCube.stoppingSize (G ω) x ^ τ}, fun m => measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun x _ =>
        (TriadicCube.measurable_stoppingSize _ hGm x).pow_const τ),
    ⟨Ctot, c', s0 / ((2 * (d + τ + 1) : ℕ) : ℝ), hCtot_ne, hc', by positivity,
      fun m => hE (originCube d m)⟩, Cfin, fun ω m hω => not_lt.1 hω⟩

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
