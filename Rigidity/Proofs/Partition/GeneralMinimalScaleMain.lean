import Rigidity.Proofs.Partition.GeneralMinimalScale

/-!
# Minimal scales for general partitions

Armstrong and Dario, Proposition 2.4 (the first bound), for the partition into maximal stopping
cubes of any random collection `G` of good triadic cubes satisfying the hypotheses (2.1) and
(2.2) of Proposition 2.1: the failure event of a cube is determined by the open edges inside its
threefold enlargement, and a cube of scale `n` fails with probability at most `C exp(-c 3^{n s})`,
`0 < s ≤ 1`. For every `τ ∈ ℕ` there is a random scale `M` with a stretched-exponential moment
such that `∑_{x ∈ Q_m} size(x)^τ ≤ C' 3^{d m}` whenever `M < 3ᵐ`, `size` being the stopping size.
The proof counts failures (`sum_stoppingSize_pow_le`, `sum_weights_le_of_counts`,
`measure_classCount_ge_le`, `measure_exists_notMem_near_le`); the exponent of the moment is
`s / (2 (d + τ + 1))`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- **Armstrong and Dario, Proposition 2.4, the first bound**, for general partitions. -/
theorem exists_scale_sum_stoppingSize_le (hd : 0 < d) (p : unitInterval)
    (G : Configuration d → Set (TriadicCube d))
    (hGm : ∀ T : TriadicCube d, MeasurableSet {ω | T ∈ G ω})
    (hloc : ∀ T : TriadicCube d,
      MeasurableSet[localEdgeSigma T.centeredTriple] {ω | T ∉ G ω})
    {C1 c s0 : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c) (hs0 : 0 < s0) (hs1 : s0 ≤ 1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ G ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)))
    (τ : ℕ) :
    ∃ C s : ℝ, 0 < s ∧ ∃ M : Configuration d → ℝ≥0∞, Measurable M ∧
      (∃ θ : ℝ, 0 < θ ∧
        Integrable (fun ω => Real.exp (((M ω).toReal / θ) ^ s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (((M ω).toReal / θ) ^ s) ∂(latticeBondLaw d p)) ≤ 2) ∧
      ∀ᵐ ω ∂(latticeBondLaw d p), ∀ m : ℕ, M ω < 3 ^ m →
        ∑ x ∈ (originCube d m).toIntegerCube.vertices,
          TriadicCube.stoppingSize (G ω) x ^ τ ≤ C * 3 ^ (d * m) := by
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
      {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classCount (fun T => T ∉ G ω) m j r}
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
        classCount (fun T => T ∉ G ω) m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) := by
      intro j hj0' hjJ r
      by_contra hge
      apply hMid
      simp only [hMiddef, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, Finset.mem_Ico]
      exact ⟨j, ⟨hj0', hjJ⟩, r, not_lt.1 hge⟩
    have h1 := sum_stoppingSize_pow_le hP m (m / K) τ hfar
    have h2 := sum_weights_le_of_counts (fun T => T ∉ G ω) m (m / K) j0 τ (Nat.div_le_self m K)
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
      refine (measure_exists_notMem_near_le p G hC1 hc hs0 hq m (m / K)).trans ?_
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
          μ {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classCount (fun T => T ∉ G ω) m j r} ≤
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
                classCount (fun T => T ∉ G ω) m j r} :=
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
  obtain ⟨θ, hθ, hint, hle⟩ := exceptionalScale_exp_moment μ E hEm Ctot hCtot_ne (s0 / K)
    c' (by positivity) hc' hE
  refine ⟨Cfin, s0 / K, by positivity, exceptionalScale E, measurable_exceptionalScale E hEm,
    ⟨θ, hθ, hint, hle⟩, ?_⟩
  filter_upwards with ω m hm
  have hnot : ω ∉ E m := by
    intro hωE
    have h3 : (3 : ℝ≥0∞) ^ m ≤ exceptionalScale E ω := by
      unfold exceptionalScale
      exact le_iSup_of_le m (by rw [if_pos hωE])
    exact absurd hm (not_lt.2 h3)
  have h : ¬ (Cfin * 3 ^ (d * m) <
      ∑ x ∈ (originCube d m).toIntegerCube.vertices, f x ω ^ τ) := hnot
  exact not_lt.1 h

end Rigidity.Percolation
