import Rigidity.Proofs.Cluster.PlanarOneVarEst

/-!
# Display (5.30) of Armstrong and Dario in dimension two

For `n ≥ 9`, the solenoidal field `g` of scale `n` in direction `e` and the nine subcubes `V` of
scale `n` of `□_{n+1}`,
`E[|∑_V |□_n|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V|²] ≤ C |e|₁² |q|² (τ_n + 3^{-n/4})`
(`exists_lintegral_sum_subcube_solenoidal_sq_le`), from the partition for the reverse Hölder
inequality. The sum is minus the crossing term of Step 2 minus the sum of the differences of
Lemma 5.5 paired with `g`, because the pairing of `g` with the coarsened gradient of
`u(·, □_{n+1}, q)` over `□_{n+1}` vanishes.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- The arithmetic of the crossing term. -/
theorem crossing_arith (n : ℕ) :
    2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) * ((9 : ℝ) ^ (n + 1)) ^ (1 / 4 : ℝ) ≤
      324 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  set t : ℝ := (3 : ℝ) ^ ((n : ℝ) / 4) with htdef
  have ht : 1 ≤ t := Real.one_le_rpow (by norm_num) (by positivity)
  have ht0 : 0 < t := by linarith
  have h3n : (3 : ℝ) ^ n = t ^ 4 := by
    rw [htdef, ← Real.rpow_natCast ((3 : ℝ) ^ ((n : ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num),
      show (n : ℝ) / 4 * ((4 : ℕ) : ℝ) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h9n : (9 : ℝ) ^ n = t ^ 8 := by
    rw [show (9 : ℝ) ^ n = ((3 : ℝ) ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, h3n]
    ring
  have h81 : (81 : ℝ) ^ n = t ^ 16 := by
    rw [show (81 : ℝ) ^ n = ((9 : ℝ) ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, h9n]
    ring
  have hq : ((9 : ℝ) ^ (n + 1)) ^ (1 / 4 : ℝ) ≤ 2 * t ^ 2 := by
    rw [pow_succ, h9n, Real.mul_rpow (by positivity) (by norm_num)]
    have ha : (t ^ 8) ^ (1 / 4 : ℝ) = t ^ 2 := by
      rw [← Real.rpow_natCast t 8, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast t 2]
      norm_num
    have hb : (9 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      calc (9 : ℝ) ^ (1 / 4 : ℝ) ≤ (16 : ℝ) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
    rw [ha]
    have : 0 ≤ t ^ 2 := by positivity
    nlinarith
  have hneg : (3 : ℝ) ^ (-(n : ℝ) / 4) = t⁻¹ := by
    rw [neg_div, Real.rpow_neg (by norm_num)]
  have hA : 0 ≤ 2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) := by positivity
  calc 2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) * ((9 : ℝ) ^ (n + 1)) ^ (1 / 4 : ℝ)
      ≤ 2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) * (2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left hq hA
    _ = 2 / t ^ 16 * (t ^ 8 * 9 / t ^ 4) * (t ^ 8 * 9) * (2 * t ^ 2) := by
        rw [h81, pow_succ (9 : ℝ) n, h9n, h3n]
    _ = 324 / t ^ 2 := by
        field_simp
        ring
    _ ≤ 324 * t⁻¹ := by
        rw [div_le_iff₀ (by positivity), mul_assoc, inv_mul_eq_div, le_mul_iff_one_le_right
          (by norm_num), le_div_iff₀ ht0]
        nlinarith
    _ = 324 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [hneg]

/-- The subcubes of scale `n` of the cube of scale `n + 1` are nine. -/
theorem card_subcubesAt_succ (W : TriadicCube 2) :
    ((subcubesAt W (W.scale - 1)).card : ℝ) = 9 ∨ W.scale = 0 := by
  rcases Nat.eq_zero_or_pos W.scale with h | h
  · exact Or.inr h
  · left
    have hN := card_subcubesAt_mul (U := W) (n := W.scale - 1) (Nat.sub_le _ _)
    rw [TriadicCube.volume] at hN
    have h9 : (9 : ℝ) ^ W.scale = 9 * 9 ^ (W.scale - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h9] at hN
    have : (0 : ℝ) < 9 ^ (W.scale - 1) := by positivity
    nlinarith

/-- The cube of scale `n + 1` centred at the origin has nine subcubes of scale `n`. -/
theorem card_subcubesAt_originCube (n : ℕ) :
    ((subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n).card : ℝ) = 9 := by
  rcases card_subcubesAt_succ (⟨n + 1, 0⟩ : TriadicCube 2) with h | h
  · simpa using h
  · simp at h

/-- The algebra of the pointwise bound of display (5.30): for nine terms with
`A = -∑ S`, `((∑ T)/c)² ≤ 2 c⁻² A² + 162 · 9⁻¹ ∑ ((S - T)/c)²`. -/
theorem sq_sum_div_le_of_card_nine {ι : Type*} {s : Finset ι} (hs : (s.card : ℝ) = 9)
    (S T : ι → ℝ) {A : ℝ} (hA : A = -∑ i ∈ s, S i) {c : ℝ} (hc : 0 < c) :
    ((∑ i ∈ s, T i) / c) ^ 2 ≤
      2 / c ^ 2 * A ^ 2 + 162 * ((9 : ℝ)⁻¹ * ∑ i ∈ s, ((S i - T i) / c) ^ 2) := by
  have hCS := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => S i - T i)
  rw [hs] at hCS
  have hsumT : ∑ i ∈ s, T i = -A - ∑ i ∈ s, (S i - T i) := by
    rw [hA, Finset.sum_sub_distrib]
    ring
  have hsq : ∑ i ∈ s, ((S i - T i) / c) ^ 2 = (∑ i ∈ s, (S i - T i) ^ 2) / c ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
  rw [hsq, hsumT, div_pow, div_le_iff₀ (by positivity)]
  set B := ∑ i ∈ s, (S i - T i)
  set D := ∑ i ∈ s, (S i - T i) ^ 2
  have hB : B ^ 2 ≤ 9 * D := hCS
  have e1 : (2 / c ^ 2 * A ^ 2 + 162 * ((9 : ℝ)⁻¹ * (D / c ^ 2))) * c ^ 2 = 2 * A ^ 2 + 18 * D := by
    field_simp
    ring
  rw [e1]
  nlinarith [sq_nonneg (A - B)]

/-- **The pointwise bound of display (5.30).** The square of the normalized sum of the subcube
pairings with the solenoidal field is at most `2 · 81^{-n}` times the square of the crossing term
plus `162` times the quantity of Lemma 5.5 with the field. -/
theorem ofReal_sum_subcube_solenoidal_sq_le (ω : Configuration 2) {n : ℕ} (hn : 2 ≤ n)
    (q e : Fin 2 → ℝ) :
    ENNReal.ofReal ((∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n,
        edgePairing V.toIntegerCube.vertices (solenoidalField n e)
          (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n) ^ 2) ≤
      ENNReal.ofReal (2 / 81 ^ n) * (if PlanarPartitionEvent ω ∧
          PlanarResolved ω (⟨n + 1, 0⟩ : TriadicCube 2) then
        ENNReal.ofReal ((edgePairing (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices
            (solenoidalField n e) (fun x => clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2)
              (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q) (planarCoarseAnchor ω x)) -
          ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n, edgePairing V.toIntegerCube.vertices
            (solenoidalField n e) (fun x => clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2)
              (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q) (planarCoarseAnchor ω x))) ^ 2)
        else 0) +
        ENNReal.ofReal 162 * ENNReal.ofReal
          (planarMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube 2) n q (solenoidalField n e)) := by
  have hsol := edgePairing_solenoidalField_eq_zero hn e
    (coarsen ω (⟨n + 1, 0⟩ : TriadicCube 2) (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q))
  have hreal := sq_sum_div_le_of_card_nine (card_subcubesAt_originCube n)
    (fun V => edgePairing V.toIntegerCube.vertices (solenoidalField n e)
      (coarsen ω (⟨n + 1, 0⟩ : TriadicCube 2) (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q)))
    (fun V => edgePairing V.toIntegerCube.vertices (solenoidalField n e)
      (coarsen ω V (planarMuMinimizer ω V q)))
    (A := edgePairing (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices
        (solenoidalField n e) (fun x => clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2)
          (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q) (planarCoarseAnchor ω x)) -
      ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n, edgePairing V.toIntegerCube.vertices
        (solenoidalField n e) (fun x => clusterExtend ω (⟨n + 1, 0⟩ : TriadicCube 2)
          (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q) (planarCoarseAnchor ω x)))
    (by
      change edgePairing _ _ (coarsen ω _ _) - _ = _
      rw [hsol, zero_sub]
      rfl)
    (c := (9 : ℝ) ^ n) (by positivity)
  have hfe : (9 : ℝ)⁻¹ * ∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n,
      ((edgePairing V.toIntegerCube.vertices (solenoidalField n e)
        (coarsen ω (⟨n + 1, 0⟩ : TriadicCube 2) (planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q)) -
        edgePairing V.toIntegerCube.vertices (solenoidalField n e)
          (coarsen ω V (planarMuMinimizer ω V q))) / (9 : ℝ) ^ n) ^ 2 =
      planarMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube 2) n q (solenoidalField n e) := by
    rw [planarMuRestrictFieldError, restrictFieldError, card_subcubesAt_originCube]
    congr 1
    refine Finset.sum_congr rfl fun V hV => ?_
    rw [TriadicCube.volume, scale_of_mem_subcubesAt hV]
  have h81 : (81 : ℝ) ^ n = ((9 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hfe, ← h81] at hreal
  have hfe0 : 0 ≤ planarMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube 2) n q
      (solenoidalField n e) := by
    rw [← hfe]
    positivity
  rw [← Finset.sum_div]
  by_cases hω : PlanarPartitionEvent ω ∧ PlanarResolved ω (⟨n + 1, 0⟩ : TriadicCube 2)
  · rw [if_pos hω]
    refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num)]
  · have h0 : planarMuMinimizer ω (⟨n + 1, 0⟩ : TriadicCube 2) q = 0 := by
      rw [planarMuMinimizer, dif_neg hω]
    rw [h0] at hreal
    simp only [map_zero, Pi.zero_apply] at hreal
    rw [if_neg hω, mul_zero, zero_add]
    refine (ENNReal.ofReal_le_ofReal ?_).trans (le_of_eq (ENNReal.ofReal_mul (by norm_num)))
    simpa [edgePairing] using hreal

/-- The arithmetic of the conclusion of display (5.30). -/
theorem oneVarEst_arith {C₁ C₂ G Q P τ x y K : ℝ} (hC₂ : 0 ≤ C₂) (hP : 0 ≤ P)
    (hτ : 0 ≤ τ) (hy0 : 0 ≤ y) (hQP : Q ≤ 2 * P) (hy : y ≤ 324 * x)
    (hG : G ^ 2 = 100 * K) (hK : 0 ≤ K) :
    C₂ * G ^ 2 * Q * y + 162 * (C₁ * G ^ 2 * P * (τ + x)) ≤
      100 * (162 * C₁ + 2 * 324 * C₂) * K * P * (τ + x) := by
  rw [hG]
  have h1 : C₂ * (100 * K) * Q * y ≤ C₂ * (100 * K) * (2 * P) * (324 * (τ + x)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hQP (by positivity)) ?_ hy0 (by positivity)
    linarith
  have e : 100 * (162 * C₁ + 2 * 324 * C₂) * K * P * (τ + x) =
      C₂ * (100 * K) * (2 * P) * (324 * (τ + x)) + 162 * (C₁ * (100 * K) * P * (τ + x)) := by
    ring
  rw [e]
  linarith

/-- **Display (5.30) of Armstrong and Dario** (proof of Lemma 5.7, Step 3, in dimension two), from
the partition for the reverse Hölder inequality: for `n ≥ 9`,
`E[|∑_V |□_n|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V|²] ≤ C |e|₁² |q|² (τ_n + 3^{-n/4})`, the sum running over
the subcubes `V` of scale `n` of `□_{n+1}` and `g` being the solenoidal field of scale `n` in
direction `e`. -/
theorem exists_lintegral_sum_subcube_solenoidal_sq_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 9 ≤ n → ∀ q e : Fin 2 → ℝ,
      ∫⁻ ω, ENNReal.ofReal ((∑ V ∈ subcubesAt (⟨n + 1, 0⟩ : TriadicCube 2) n,
          edgePairing V.toIntegerCube.vertices (solenoidalField n e)
            (coarsen ω V (planarMuMinimizer ω V q)) / 9 ^ n) ^ 2) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (C * (|e 0| + |e 1|) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
  obtain ⟨C₁, hC₁, hfield⟩ := exists_lintegral_planarMuRestrictFieldError_le hpc hG
  obtain ⟨C₂, hC₂, hcross⟩ := exists_lintegral_edgePairing_sub_sum_subcubes_le hpc
    (a := 4) (by norm_num)
  refine ⟨100 * (162 * C₁ + 2 * 324 * C₂.toReal), by positivity, fun n hn q e => ?_⟩
  have hWs : (⟨n + 1, 0⟩ : TriadicCube 2).scale = n + 1 := rfl
  have hnW : n ≤ (⟨n + 1, 0⟩ : TriadicCube 2).scale := by omega
  have hg := abs_solenoidalField_le n e
  have hfm : Measurable fun ω => ENNReal.ofReal 162 * ENNReal.ofReal
      (planarMuRestrictFieldError ω (⟨n + 1, 0⟩ : TriadicCube 2) n q (solenoidalField n e)) :=
    ((measurable_planarMuRestrictFieldError _ hnW q _).ennreal_ofReal).const_mul _
  have hcrossbound := hcross (⟨n + 1, 0⟩ : TriadicCube 2) n hnW q (solenoidalField n e) _ hg
  have hfieldbound := hfield (⟨n + 1, 0⟩ : TriadicCube 2) n (by rw [hWs]; omega)
    (by rw [hWs]; omega) q (solenoidalField n e) _ hg
  rw [hWs, Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, zero_add]
    at hfieldbound
  refine (lintegral_mono fun ω => ofReal_sum_subcube_solenoidal_sq_le ω (by omega) q e).trans ?_
  rw [lintegral_add_right _ hfm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (add_le_add (mul_le_mul_of_nonneg_left hcrossbound zero_le)
    (mul_le_mul_of_nonneg_left hfieldbound zero_le)).trans ?_
  -- back to real numbers
  have hNW : ((⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ≥0∞) =
      ENNReal.ofReal ((9 : ℝ) ^ (n + 1)) := by
    rw [← ENNReal.ofReal_natCast, card_toIntegerCube_vertices_eq, hWs]
  have hvW : (⟨n + 1, 0⟩ : TriadicCube 2).volume = (9 : ℝ) ^ (n + 1) := by
    rw [TriadicCube.volume, hWs]
  rw [hNW, hvW, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  conv_lhs => rw [← ENNReal.ofReal_toReal hC₂]
  have hτx : 0 ≤ planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4) :=
    add_nonneg (planarTau_nonneg p n) (by positivity)
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg hC₁ (by positivity))
        (by positivity)) hτx))]
  refine ENNReal.ofReal_le_ofReal ?_
  set y := 2 / 81 ^ n * ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) *
    ((9 : ℝ) ^ (n + 1)) ^ (1 / ((4 : ℕ) : ℝ)) with hy
  have hy' : y ≤ 324 * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
    rw [hy, show (1 / ((4 : ℕ) : ℝ)) = (1 / 4 : ℝ) by norm_num]
    exact crossing_arith n
  have e2 : 2 / 81 ^ n * (C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 *
      ((9 : ℝ) ^ (n + 1) / 3 ^ n) * 9 ^ (n + 1) * ((9 : ℝ) ^ (n + 1)) ^ (1 / ((4 : ℕ) : ℝ))) =
      C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 * y := by rw [hy]; ring
  rw [e2]
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have key := oneVarEst_arith (C₁ := C₁) (C₂ := C₂.toReal) (G := 10 * (|e 0| + |e 1|))
    (Q := (|q 0| + |q 1|) ^ 2) (P := q 0 ^ 2 + q 1 ^ 2) (τ := planarTau p n)
    (x := (3 : ℝ) ^ (-(n : ℝ) / 4)) (y := y) (K := (|e 0| + |e 1|) ^ 2)
    ENNReal.toReal_nonneg (by positivity) (planarTau_nonneg p n) hy0
    (abs_add_abs_sq_le q) hy' (by ring) (by positivity)
  calc C₂.toReal * (10 * (|e 0| + |e 1|)) ^ 2 * (|q 0| + |q 1|) ^ 2 * y +
        162 * (C₁ * (10 * (|e 0| + |e 1|)) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)))
      ≤ 100 * (162 * C₁ + 2 * 324 * C₂.toReal) * (|e 0| + |e 1|) ^ 2 * (q 0 ^ 2 + q 1 ^ 2) *
          (planarTau p n + (3 : ℝ) ^ (-(n : ℝ) / 4)) := key
    _ = _ := by ring

end Rigidity.Proofs.Cluster
