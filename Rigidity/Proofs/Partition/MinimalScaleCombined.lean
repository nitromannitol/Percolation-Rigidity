import Rigidity.Proofs.Partition.LambdaClosure

/-!
# Armstrong and Dario, Proposition 2.4

For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, and `t ∈ ℕ`, there are a constant `C`, an
exponent `s > 0` and one random scale `M` with a stretched-exponential moment of order `s` such
that, almost surely, whenever `M < 3ᵐ`,
`Λ_t(Q_m) ≤ C` and every partition cube meeting `Q_m` has side at most `3^{d m / (d + t)}`.
The two bounds hold outside events `E₁(m)`, `E₂(m)` of probabilities at most
`C exp(-c 3^{m s_i})` (`exists_events_sum_pow_partitionCube_le`, `exists_events_stoppingSize_le`);
`M` is the largest `3ᵐ` with `E₁(m) ∪ E₂(m)` occurring.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The exceptional events of the bound on the largest partition cube. -/
theorem exists_events_stoppingSize_le (μ : Measure (Configuration d)) [IsProbabilityMeasure μ]
    {θ : ℝ} (hθ : 0 < θ)
    (hmom : ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ))
        μ ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x / θ) ∂μ) ≤ 2)
    (A : ℕ → TriadicCube d) (hA : ∀ m, (A m).scale = m) {α : ℝ} (hα : 0 < α) :
    ∃ E : ℕ → Set (Configuration d), (∀ m, MeasurableSet (E m)) ∧
      (∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ m, μ (E m) ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ α))) ∧
      ∀ (ω : Configuration d) (m : ℕ), ω ∉ E m → ∀ x ∈ (A m).vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x ≤ ((3 : ℝ) ^ m) ^ α := by
  classical
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x =>
    TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes x
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
  set C' : ℝ := 2 * (((⌈(d : ℝ) / α⌉₊).factorial : ℝ) / (1 / θ / 2) ^ ⌈(d : ℝ) / α⌉₊)
    with hC'def
  have hE : ∀ m, μ (E m) ≤
      ENNReal.ofReal C' * ENNReal.ofReal (Real.exp (-(1 / θ / 2) * ((3 : ℝ) ^ m) ^ α)) := by
    intro m
    have hcard : ((A m).toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ m) ^ d := by
      rw [IntegerCube.card_vertices]
      change (((3 ^ (A m).scale) ^ d : ℕ) : ℝ) = _
      rw [hA m]
      push_cast
      ring
    calc μ (E m) ≤ ∑ x ∈ (A m).toIntegerCube.vertices, μ {ω | ((3 : ℝ) ^ m) ^ α < f x ω} := by
          rw [hE_eq]
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ (A m).toIntegerCube.vertices,
            ENNReal.ofReal (2 * Real.exp (-(((3 : ℝ) ^ m) ^ α / θ))) :=
          Finset.sum_le_sum fun x _ =>
            measure_lt_le_of_exp_moment μ hθ (hmom x).1 (hmom x).2 _
      _ = ENNReal.ofReal (((3 : ℝ) ^ m) ^ d * (2 * Real.exp (-(((3 : ℝ) ^ m) ^ α / θ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
      _ ≤ ENNReal.ofReal (C' * Real.exp (-(1 / θ / 2) * ((3 : ℝ) ^ m) ^ α)) :=
          ENNReal.ofReal_le_ofReal (pow_mul_exp_neg_rpow_le hα hθ m)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
  exact ⟨E, hEm, ⟨C', 1 / θ / 2, by positivity, by positivity, hE⟩,
    fun ω m hω x hx => not_lt.1 fun hlt => hω ⟨x, hx, hlt⟩⟩

/-- The exceptional events of the bound on `∑_{x ∈ Q_m} 3^{τ n(x)}`. -/
theorem exists_events_sum_pow_partitionCube_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (τ : ℕ) :
    ∃ E : ℕ → Set (Configuration d), (∀ m, MeasurableSet (E m)) ∧
      (∃ (C : ℝ≥0∞) (c s : ℝ), C ≠ ∞ ∧ 0 < c ∧ 0 < s ∧ ∀ m, latticeBondLaw d p (E m) ≤
        C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ s))) ∧
      ∃ Cf : ℝ, ∀ ω : Configuration d, PartitionEvent ω → ∀ m : ℕ, ω ∉ E m →
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤ Cf * 3 ^ (d * m) := by
  classical
  obtain ⟨C1, c, hC1, hc, hq⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hae := ae_partitionEvent hd hpc
  set μ := latticeBondLaw d p with hμdef
  have hd1 : 1 ≤ d := by omega
  set K : ℕ := 2 * (d + τ + 1) with hKdef
  have hK : 0 < K := by omega
  obtain ⟨j0, hj03, hj0⟩ :=
    exists_large_scale_exp_le (Real.exp 1 * 25 ^ d * C1) c (by positivity) hc (τ + 1)
  set Cfin : ℝ := (j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d with hCfin
  set f : Vertex d → Configuration d → ℝ :=
    fun x ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x with hfdef
  have hfm : ∀ x, Measurable (f x) := fun x =>
    TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes x
  set E : ℕ → Set (Configuration d) := fun m =>
    {ω | Cfin * 3 ^ (d * m) < ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ}
    with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m =>
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun x _ => (hfm x).pow_const τ)
  -- on the partition event, the stopping sizes are the sides of the partition cubes
  have hsize : ∀ ω, PartitionEvent ω → ∀ m,
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ =
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (τ * (partitionCube ω x).scale) := by
    intro ω hP m
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hfdef]
    simp only
    rw [TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x) (partitionCube_spec hP x).2,
      ← pow_mul, mul_comm]
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
    {ω | ∃ T : TriadicCube d, m / K ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} with hBigdef
  set Mid : ℕ → Set (Configuration d) := fun m =>
    ⋃ j ∈ Finset.Ico j0 (m / K), ⋃ r : Fin d → Fin 3,
      {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} with hMiddef
  have hsub : ∀ m, E m ⊆ {ω | ¬ PartitionEvent ω} ∪ (Big m ∪ Mid m) := by
    intro m ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hP, hBig, hMid⟩ := hcon
    have hfar : ∀ T : TriadicCube d, m / K ≤ T.scale → T ∉ TriadicCube.goodCubes ω →
        ∀ x ∈ (originCube d m).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side :=
      fun T hT hbad x hx hnear => hBig ⟨T, hT, hbad, x, hx, hnear⟩
    have hmid : ∀ j, j0 ≤ j → j < m / K → ∀ r,
        classBadCount ω m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) := by
      intro j hj0' hjJ r
      by_contra hge
      apply hMid
      simp only [hMiddef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_Ico]
      exact ⟨j, ⟨hj0', hjJ⟩, r, not_lt.1 hge⟩
    have hbound := sum_pow_scale_le_of_counts hP m (m / K) j0 τ (Nat.div_le_self m K)
      (fun j hj => le_trans (Nat.le_add_right _ _) (hexpK m j hj)) hfar hmid
    have hω' : Cfin * 3 ^ (d * m) <
        ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ := hω
    rw [hsize ω hP m] at hω'
    exact absurd hbound (not_le.2 hω')
  -- the probability of the failure events
  have hnull : μ {ω | ¬ PartitionEvent ω} = 0 := ae_iff.1 hae
  set G : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (3 - 1))) ^ k with hGdef
  have hG : G ≠ ∞ := stretched_exp_geometric_sum_ne_top 3 c (by norm_num) hc
  set c' : ℝ := min (c / 3 / 2) (1 / 3 / 2) with hc'def
  have hc' : 0 < c' := lt_min (by positivity) (by norm_num)
  set D1 : ℝ := ((K * d).factorial : ℝ) / (c / 3 / 2) ^ (K * d) with hD1
  set D2 : ℝ := ((K * 1).factorial : ℝ) / (1 / 3 / 2) ^ (K * 1) with hD2
  set Ctot : ℝ≥0∞ := ENNReal.ofReal (25 ^ d * C1 * D1) * G + ENNReal.ofReal (3 ^ d * D2)
    with hCtot
  have hCtot_ne : Ctot ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG, ENNReal.ofReal_ne_top⟩
  have hE : ∀ m, μ (E m) ≤ Ctot * ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K))) := by
    intro m
    set x : ℝ := ((3 : ℝ) ^ m) ^ ((1 : ℝ) / K) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hexp1 : Real.exp (-(c / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left (c / 3 / 2) (1 / 3 / 2)])
    have hexp2 : Real.exp (-(1 / 3 / 2) * x) ≤ Real.exp (-c' * x) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right (c / 3 / 2) (1 / 3 / 2)])
    -- the large bad cube
    have hbig : μ (Big m) ≤ ENNReal.ofReal (25 ^ d * C1 * D1) * G *
        ENNReal.ofReal (Real.exp (-c' * x)) := by
      refine (measure_exists_bad_near_le p hC1 hc hq m (m / K)).trans ?_
      have hpoly := mul_exp_neg_three_pow_div_le hK d hc m (P := (3 : ℝ) ^ (d * m))
        (le_of_eq (by rw [← pow_mul, mul_comm d m]))
      rw [← hD1] at hpoly
      have hreal : 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K)) ≤
          25 ^ d * C1 * D1 * Real.exp (-c' * x) := by
        have h25 : (0 : ℝ) ≤ 25 ^ d * C1 := by positivity
        calc 25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K))
            = 25 ^ d * C1 * ((3 : ℝ) ^ (d * m) * Real.exp (-c * 3 ^ (m / K))) := by ring
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-(c / 3 / 2) * x)) :=
              mul_le_mul_of_nonneg_left hpoly h25
          _ ≤ 25 ^ d * C1 * (D1 * Real.exp (-c' * x)) := by
              gcongr
          _ = _ := by ring
      calc ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
            ENNReal.ofReal (Real.exp (-c * 3 ^ (m / K))) * G
          = ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * 3 ^ (m / K))) * G := by
            exact congrArg (· * G) (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (25 ^ d * C1 * D1 * Real.exp (-c' * x)) * G := by
            gcongr
        _ = _ := by
            rw [ENNReal.ofReal_mul (p := 25 ^ d * C1 * D1) (by positivity)]
            ring
    -- many bad cubes in a residue class
    have hmid : μ (Mid m) ≤ ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x)) := by
      have hterm : ∀ j ∈ Finset.Ico j0 (m / K), ∀ r : Fin d → Fin 3,
          μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} ≤
            ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (m / K))) := by
        intro j hj r
        rw [Finset.mem_Ico] at hj
        have hjm := hexpK m j hj.2
        have hjm0 : j ≤ m := le_trans hj.2.le (Nat.div_le_self m K)
        have hjm' : (τ + 1) * (j + 1) ≤ d * (m - j) := by
          have h1 : d * (m - j) + d * j = d * m := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hjm0]
          linarith
        refine (measure_classBadCount_ge_le p hC1 hq (by omega) (hj0 j hj.1) hjm' r).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have h1 : d * (m - j) + d * j = d * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hjm0]
        have hle : m / K ≤ d * (m - j) - (τ + 1) * (j + 1) :=
          Nat.le_sub_of_add_le (by linarith)
        have := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 by norm_num) hle
        linarith
      have hsumE : μ (Mid m) ≤ ENNReal.ofReal (((Finset.Ico j0 (m / K)).card : ℝ) * 3 ^ d *
          Real.exp (-(3 : ℝ) ^ (m / K))) := by
        calc μ (Mid m) ≤ ∑ j ∈ Finset.Ico j0 (m / K), ∑ r : Fin d → Fin 3,
              μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} :=
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
      have hpoly := mul_exp_neg_three_pow_div_le hK 1 one_pos m (P := (m : ℝ)) (by
        rw [pow_one]
        exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le)
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
    calc μ (E m) ≤ μ ({ω | ¬ PartitionEvent ω} ∪ (Big m ∪ Mid m)) := measure_mono (hsub m)
      _ ≤ μ {ω | ¬ PartitionEvent ω} + (μ (Big m) + μ (Mid m)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (25 ^ d * C1 * D1) * G * ENNReal.ofReal (Real.exp (-c' * x)) +
            ENNReal.ofReal (3 ^ d * D2) * ENNReal.ofReal (Real.exp (-c' * x))) := by
          rw [hnull]
          exact add_le_add le_rfl (add_le_add hbig hmid)
      _ = Ctot * ENNReal.ofReal (Real.exp (-c' * x)) := by
          rw [hCtot]
          ring
  refine ⟨E, hEm, ⟨Ctot, c', (1 : ℝ) / K, hCtot_ne, hc', by positivity, hE⟩, Cfin,
    fun ω hP m hω => ?_⟩
  have h : ¬ (Cfin * 3 ^ (d * m) <
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ) := hω
  rw [hsize ω hP m] at h
  exact not_lt.1 h

/-- **Armstrong and Dario, Proposition 2.4** (minimal scales for the partition `𝒫`). For
supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, and every `t ∈ ℕ`, there are `C`, `s > 0` and a
measurable random scale `M` with a stretched-exponential moment of order `s` such that, almost
surely, whenever `M < 3ᵐ`, `Λ_t(Q_m) = 3^{-d m} ∑_{x ∈ cl(Q_m)} 3^{t n(x)} ≤ C` and every vertex
of `Q_m` lies in a partition cube of side at most `3^{d m / (d + t)}`. -/
theorem exists_minimalScale [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (t : ℕ) :
    ∃ C s : ℝ, 0 < s ∧ ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ : ℝ, 0 < θ ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        (∑ x ∈ partitionClosure ω (originCube d m).toIntegerCube.vertices,
          (3 : ℝ) ^ (t * (partitionCube ω x).scale)) / 3 ^ (d * m) ≤ C ∧
        ∀ x ∈ (originCube d m).vertices,
          (3 : ℝ) ^ (partitionCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ ((d : ℝ) / (d + t)) := by
  set μ := latticeBondLaw d p with hμdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hα : (0 : ℝ) < (d : ℝ) / (d + t) := by positivity
  obtain ⟨hae, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates hd hpc
  obtain ⟨E1, hE1m, ⟨C1, c1, s1, hC1, hc1, hs1, hE1⟩, Cf, hCf⟩ :=
    exists_events_sum_pow_partitionCube_le hd hpc (t + d)
  obtain ⟨E2, hE2m, ⟨C2, c2, hC2, hc2, hE2⟩, hE2prop⟩ :=
    exists_events_stoppingSize_le μ hθ hmom (originCube d) (fun _ => rfl) hα
  set s : ℝ := min s1 ((d : ℝ) / (d + t)) with hsdef
  have hs : 0 < s := lt_min hs1 hα
  set c : ℝ := min c1 c2 with hcdef
  have hc : 0 < c := lt_min hc1 hc2
  set E : ℕ → Set (Configuration d) := fun m => E1 m ∪ E2 m with hEdef
  have hEm : ∀ m, MeasurableSet (E m) := fun m => (hE1m m).union (hE2m m)
  have hmono : ∀ (m : ℕ) {s' c' : ℝ}, s ≤ s' → c ≤ c' →
      ENNReal.ofReal (Real.exp (-c' * ((3 : ℝ) ^ m) ^ s')) ≤
        ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
    intro m s' c' hs' hc'
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have h1 : ((3 : ℝ) ^ m) ^ s ≤ ((3 : ℝ) ^ m) ^ s' :=
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hs'
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ s := by positivity
    nlinarith
  have hE : ∀ m, μ (E m) ≤ (C1 + ENNReal.ofReal C2) *
      ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
    intro m
    calc μ (E m) ≤ μ (E1 m) + μ (E2 m) := measure_union_le _ _
      _ ≤ C1 * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) +
          ENNReal.ofReal C2 * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
          gcongr
          · exact (hE1 m).trans (mul_le_mul' le_rfl (hmono m (min_le_left _ _) (min_le_left _ _)))
          · exact (hE2 m).trans
              (mul_le_mul' le_rfl (hmono m (min_le_right _ _) (min_le_right _ _)))
      _ = _ := by ring
  obtain ⟨θ', hθ', hint, hle⟩ := exceptionalScale_exp_moment μ E hEm (C1 + ENNReal.ofReal C2)
    (ENNReal.add_ne_top.2 ⟨hC1, ENNReal.ofReal_ne_top⟩) s c hs hc hE
  refine ⟨Cf, s, hs, exceptionalScale E, measurable_exceptionalScale E hEm,
    ⟨θ', hθ', hint, hle⟩, ?_⟩
  filter_upwards [hae] with ω hP m hm
  have hnot : ω ∉ E m := by
    intro hωE
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hm (not_lt.2 h3)
  have hn1 : ω ∉ E1 m := fun h => hnot (Or.inl h)
  have hn2 : ω ∉ E2 m := fun h => hnot (Or.inr h)
  refine ⟨?_, fun x hx => ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    exact (sum_partitionClosure_le hP _ t).trans (hCf ω hP m hn1)
  · rw [← TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP x)
      (partitionCube_spec hP x).2]
    exact hE2prop ω m hn2 x hx

end Rigidity.Percolation
