import Rigidity.Proofs.Cluster.PlanarSwitchLocCompare
import Rigidity.Proofs.Cluster.PlanarReachConcentrationHolds

/-!
# Display (5.31) of Armstrong and Dario in dimension two

The partition agrees on a triadic cube `V` of scale `n` with the partition capped at scale `k`
outside an event of probability at most `C (2 · 3^{n-k} + 29)² exp(-c 3^k)`
(`exists_measure_not_planarCapGood_le`, Proposition 4.9 with the cap at `k`). With `k = ⌊n/12⌋`,
the pointwise comparison on this event and the deterministic bound off it give, for `n ≥ 120`,
`E[(X - Y)²] ≤ C G² |q|₁² 3^{-n/4}` (`exists_lintegral_sq_sub_switchLoc_le`), where
`X = |V|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V` and `Y` is the local version, which is measurable for the
bonds inside `V`. This is display (5.31) (the inequality (e.switchloc)).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **Localization of the planar partition at the cap `k`** (Armstrong and Dario,
Proposition 4.9, in dimension two). -/
theorem exists_measure_not_planarCapGood_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube 2) (k : ℕ),
      ∃ S : Set (Configuration 2), MeasurableSet S ∧
        (∀ ω, ω ∉ S → PlanarCapGood k V ω) ∧
        latticeBondLaw 2 p S ≤ ENNReal.ofReal (C * (2 * 3 ^ (V.scale - k) + 29) ^ 2 *
          Real.exp (-c * (3 : ℝ) ^ k)) := by
  obtain ⟨C, hC, c, hc, hgood⟩ := exists_measure_not_mem_planarGoodCubes_le hpc
  have hr : ENNReal.ofReal (Real.exp (-c * (3 - 1))) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    nlinarith
  set R : ℝ≥0∞ := (1 - ENNReal.ofReal (Real.exp (-c * (3 - 1))))⁻¹ with hR
  have hRt : R ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  refine ⟨(C * R).toReal, ENNReal.toReal_nonneg, c, hc, fun V k => ?_⟩
  set S₀ := {ω : Configuration 2 | ∃ x ∈ V.vertices, ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧
    Q.IsMaximalStopping (planarGoodCubes ω) ∧
      Q ≠ TriadicCube.cappedCube (planarGoodCubes ω) k x} with hS₀
  set S₁ := {ω : Configuration 2 | ¬ PlanarPartitionEvent ω} with hS₁
  refine ⟨toMeasurable (latticeBondLaw 2 p) (S₁ ∪ S₀), measurableSet_toMeasurable _ _,
    fun ω hω => ?_, ?_⟩
  · have hω' : ω ∉ S₁ ∪ S₀ := fun h => hω (subset_toMeasurable _ _ h)
    simp only [Set.mem_union, not_or, hS₁, hS₀, Set.mem_setOf_eq, not_not] at hω'
    refine ⟨hω'.1, fun x hx => ?_⟩
    by_contra hne
    exact hω'.2 ⟨x, hx, _, (planarPartCube_spec hω'.1 x).1, (planarPartCube_spec hω'.1 x).2, hne⟩
  · rw [measure_toMeasurable]
    have h0 : latticeBondLaw 2 p S₁ = 0 := ae_iff.1 (ae_planarPartitionEvent hpc)
    have h := TriadicCube.measure_ne_cappedCube_le_stretched (latticeBondLaw 2 p)
      (fun ω => planarGoodCubes ω) V k C 3 c (by norm_num) hc hgood
    rw [ENNReal.tsum_geometric] at h
    refine (measure_union_le _ _).trans ?_
    rw [h0, zero_add]
    refine h.trans (le_of_eq ?_)
    rw [← hR, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_toReal hRt,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_mul]
    congr 1
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    push_cast
    ring

theorem three_pow_nine_mul_div_le {n k : ℕ} (h : 12 * k ≤ n) :
    (3 : ℝ) ^ (9 * k) / 3 ^ n ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h' : (12 : ℝ) * k ≤ n := by exact_mod_cast h
  push_cast
  linarith

theorem inv_three_pow_le (n : ℕ) : ((3 : ℝ) ^ n)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The centre of a triadic cube lies in its interior square at distance `6 · 3^k` when
`k + 3 ≤ n`. -/
theorem center_mem_switchInterior {V : TriadicCube 2} {k : ℕ} (hk : k + 3 ≤ V.scale) :
    V.center ∈ switchInterior k V := by
  have h27 : 27 * (3 : ℤ) ^ k ≤ 3 ^ V.scale := by
    calc 27 * (3 : ℤ) ^ k = 3 ^ (k + 3) := by ring
      _ ≤ 3 ^ V.scale := pow_le_pow_right₀ (by norm_num) hk
  have h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale := by
    have h27' : 27 * 3 ^ k ≤ 3 ^ V.scale := by exact_mod_cast h27
    omega
  have hpos : (0 : ℤ) < 3 ^ k := by positivity
  unfold switchInterior
  rw [IntegerCube.mem_vertices]
  intro i
  simp only [interiorCube, TriadicCube.toIntegerCube, TriadicCube.center, TriadicCube.side]
  push_cast [Nat.cast_sub h2r]
  generalize (3 : ℤ) ^ V.scale * V.index i = A
  constructor <;> omega

/-- **Display (5.31) of Armstrong and Dario** (inequality (e.switchloc), in dimension two). For
`n ≥ 120` and `k = ⌊n/12⌋`, the subcube pairing and its local version differ in mean square by at
most `C G² |q|₁² 3^{-n/4}`. -/
theorem exists_lintegral_sq_sub_switchLoc_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : TriadicCube 2, 120 ≤ V.scale → ∀ (q : Fin 2 → ℝ)
      (g : Vertex 2 → Fin 2 → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∫⁻ ω, ENNReal.ofReal ((edgePairing V.toIntegerCube.vertices g
          (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ V.scale -
          switchLoc (V.scale / 12) V g q (72 * 81 ^ V.scale * G * (|q 0| + |q 1|)) ω) ^ 2)
          ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * G ^ 2 * (|q 0| + |q 1|) ^ 2 * (3 : ℝ) ^ (-(V.scale : ℝ) / 4)) := by
  obtain ⟨Cp, hCp, c, hc, hS⟩ := exists_measure_not_planarCapGood_le hpc
  obtain ⟨KB, hKB, hKBk⟩ := exists_exp_neg_rpow_le_inv_pow hc one_pos 132
  set C₁ : ℝ := 128 * 352836 ^ 2 * 24 with hC₁
  set C₂ : ℝ := 4 * 72 ^ 2 * Cp * 961 * KB * 3 ^ 121 with hC₂
  refine ⟨C₁ + C₂, by positivity, fun V hn q g G hg => ?_⟩
  set n := V.scale with hndef
  set k := n / 12 with hkdef
  set Q := |q 0| + |q 1| with hQdef
  have hQ : 0 ≤ Q := by positivity
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 0)
  set M := 72 * 81 ^ n * G * Q with hMdef
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨S, hSm, hSgood, hSμ⟩ := hS V k
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n := by omega
  have hk3 : k + 3 ≤ n := by omega
  have h12 : 12 * k ≤ n := by omega
  have hn11 : n ≤ 12 * k + 11 := by omega
  have h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ n := by
    have : 27 * 3 ^ k ≤ 3 ^ n := by
      calc 27 * 3 ^ k = 3 ^ (k + 3) := by ring
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  have hcI := center_mem_switchInterior (V := V) hk3
  set b₁ := 128 * 352836 ^ 2 * G ^ 2 * Q ^ 2 * (24 * 3 ^ (9 * k) / 3 ^ n) with hb₁
  have hpt : ∀ ω, ENNReal.ofReal ((edgePairing V.toIntegerCube.vertices g
      (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n - switchLoc k V g q M ω) ^ 2) ≤
      ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) * S.indicator 1 ω := by
    intro ω
    have hXM := abs_subcubePairing_le V q hg ω
    have hYM := abs_switchLoc_le (k := k) (V := V) g q hM0 ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
      have h1 := abs_sub _ _ |>.trans (add_le_add hXM hYM)
      rw [← sq_abs]
      calc |_| ^ 2 ≤ (M + M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by
            simpa [hMdef, hQdef] using (abs_sub (edgePairing V.toIntegerCube.vertices g
              (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ V.scale)
              (switchLoc k V g q M ω)).trans (add_le_add hXM hYM)) 2
        _ = 4 * M ^ 2 := by ring
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hgood := hSgood ω hω
      refine ENNReal.ofReal_le_ofReal ?_
      rw [switchLoc_eq_of_capGood hgood hkn h2r hcI g q M]
      have hcl := abs_sub_clamp_le (Y := switchLocValue k V g q ω) hXM
      have hcmp := sq_sub_switchLocValue_le hgood hk1 hkn h2r q hg
      calc (edgePairing V.toIntegerCube.vertices g (coarsen ω V (planarMuMinimizer ω V q)) /
            9 ^ n - max (-M) (min M (switchLocValue k V g q ω))) ^ 2
          ≤ (edgePairing V.toIntegerCube.vertices g (coarsen ω V (planarMuMinimizer ω V q)) /
            9 ^ n - switchLocValue k V g q ω) ^ 2 := by
            rw [← sq_abs, ← sq_abs (_ - switchLocValue k V g q ω)]
            exact pow_le_pow_left₀ (abs_nonneg _) hcl 2
        _ ≤ b₁ := hcmp
  have hint : ∫⁻ ω, (ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) * S.indicator 1 ω)
      ∂(latticeBondLaw 2 p) = ENNReal.ofReal b₁ + ENNReal.ofReal (4 * M ^ 2) *
        latticeBondLaw 2 p S := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ (measurable_one.indicator hSm), lintegral_indicator_one hSm]
  refine (lintegral_mono hpt).trans ?_
  rw [hint]
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hSμ zero_le)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the good part
  have hgood : b₁ ≤ C₁ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    have h := three_pow_nine_mul_div_le h12
    rw [hb₁, hC₁]
    have e : 128 * 352836 ^ 2 * G ^ 2 * Q ^ 2 * (24 * 3 ^ (9 * k) / 3 ^ n) =
        128 * 352836 ^ 2 * 24 * G ^ 2 * Q ^ 2 * ((3 : ℝ) ^ (9 * k) / 3 ^ n) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  -- the bad part
  have hbad : 4 * M ^ 2 * (Cp * (2 * 3 ^ (n - k) + 29) ^ 2 * Real.exp (-c * (3 : ℝ) ^ k)) ≤
      C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    set t : ℝ := 3 ^ n with ht
    set u : ℝ := 3 ^ k with hu
    have ht0 : 0 < t := by positivity
    have hu0 : 0 < u := by positivity
    have hexp : Real.exp (-c * u) ≤ KB * (u⁻¹) ^ 132 := by
      have := hKBk k
      rwa [Real.rpow_one] at this
    have hu132 : t ^ 11 ≤ 3 ^ 121 * u ^ 132 := by
      rw [ht, hu, ← pow_mul, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : (u⁻¹) ^ 132 ≤ 3 ^ 121 / t ^ 11 := by
      rw [inv_pow, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
      linarith
    have hnk : (2 * (3 : ℝ) ^ (n - k) + 29) ^ 2 ≤ 961 * t ^ 2 := by
      have h1 : (3 : ℝ) ^ (n - k) ≤ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have h2 : (1 : ℝ) ≤ t := one_le_pow₀ (by norm_num)
      have h3 : 2 * (3 : ℝ) ^ (n - k) + 29 ≤ 31 * t := by linarith
      have h4 : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ (n - k) + 29 := by positivity
      calc (2 * (3 : ℝ) ^ (n - k) + 29) ^ 2 ≤ (31 * t) ^ 2 := pow_le_pow_left₀ h4 h3 2
        _ = 961 * t ^ 2 := by ring
    have hM2 : M ^ 2 = 72 ^ 2 * t ^ 8 * G ^ 2 * Q ^ 2 := by
      rw [hMdef, ht]
      have : (81 : ℝ) ^ n = (3 ^ n) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]
      ring
    have hlast : (t)⁻¹ ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [ht]; exact inv_three_pow_le n
    have hA : 0 ≤ 4 * M ^ 2 * Cp := by positivity
    calc 4 * M ^ 2 * (Cp * (2 * 3 ^ (n - k) + 29) ^ 2 * Real.exp (-c * (3 : ℝ) ^ k))
        = 4 * M ^ 2 * Cp * (2 * 3 ^ (n - k) + 29) ^ 2 * Real.exp (-c * u) := by rw [hu]; ring
      _ ≤ 4 * M ^ 2 * Cp * (961 * t ^ 2) * (KB * (u⁻¹) ^ 132) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hnk hA) hexp (Real.exp_pos _).le
            (by positivity)
      _ ≤ 4 * M ^ 2 * Cp * (961 * t ^ 2) * (KB * (3 ^ 121 / t ^ 11)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hKB) (by positivity)
      _ = C₂ * G ^ 2 * Q ^ 2 * t⁻¹ := by
          rw [hM2, hC₂]
          field_simp
      _ ≤ C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hlast (by positivity)
  have e : (C₁ + C₂) * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) =
      C₁ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) +
        C₂ * G ^ 2 * Q ^ 2 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by ring
  rw [e]
  exact add_le_add hgood hbad

end Rigidity.Proofs.Cluster
