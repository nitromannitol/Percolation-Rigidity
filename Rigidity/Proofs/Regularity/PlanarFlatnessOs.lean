import Rigidity.Proofs.Regularity.PlanarFlatnessDecay
import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad

/-!
# Lemma 5.8, (5.33), with a minimal scale of class `O_s`

`PlanarNuSubaddOsTwo p` is the part of Proposition 5.2 of Armstrong and Dario
(arXiv:1609.09431v2) for `ν` in the form `O_s`: for every triadic cube `V` the error
`|ν(V, ξ) - ½ ξ · ā ξ|` (with `ν = 0` off the event that the partition exists and resolves `V`) is at
most `Z_V |ξ|²` with `Z_V ≤ O_r(C 3^{-α scale V})` measurable.

`exists_planarNuFlatness_os`: from it, there are `μ < 1` and a minimal scale `Y ≤ O_s(θ)` such that
almost surely, whenever `Y < 3^n`, the flatness error of the coarsened maximizer of
`ν(□_{n+1}, e_i)` is at most `2 · 9^n μ^n` for `i = 0, 1`. Outside an event `E_n` the reach is at
most `(3^{n+1})^{1/40}` on `□_{n+1}`, the configuration avoids the bad events of Lemma 5.5 at the
scales `k ∈ [⌊(9(n+1)+9)/10⌋, n]`, and the subadditivity errors of `□_{n+1}` and of its subcubes of
these scales are at most `(3^{n+1})^{-α/2}`; then the pathwise bound
(`exists_planarFlatness_le_of_reach`) decays (`exists_flatnessBound_le`). The probability of `E_n` is
at most `C exp(-c 3^{n σ})` (union bounds over the vertices, the subcubes and the scales), and the
supremum of the `3^n` with `ω ∈ E_n` is the minimal scale (`exists_isOsBond_of_events`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5
open scoped Classical ENNReal Matrix

/-- **Proposition 5.2 of Armstrong and Dario for `ν` in the form `O_s`** (dimension two). -/
def PlanarNuSubaddOsTwo (p : unitInterval) : Prop :=
  ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube 2,
    ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
      IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
      ∀ (ω : Configuration 2) (ξ : Fin 2 → ℝ),
        |(if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0) -
          1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤ Z ω * (ξ 0 ^ 2 + ξ 1 ^ 2)

/-- The rate of the subadditivity errors against `(3^m)^{-α/2}` at a scale `k ≥ 9m/10`. -/
theorem subadd_ratio_ge {m k : ℕ} (hmk : 9 * m ≤ 10 * k) {α C : ℝ} (hα : 0 < α) (hC : 0 < C) :
    C⁻¹ * ((3 : ℝ) ^ m) ^ (2 * α / 5) ≤
      ((3 : ℝ) ^ m) ^ (-(α / 2)) / (C * (3 : ℝ) ^ (-(k : ℝ) * α)) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : ((3 : ℝ) ^ m) ^ (2 * α / 5) * (3 : ℝ) ^ (-(k : ℝ) * α) ≤
      ((3 : ℝ) ^ m) ^ (-(α / 2)) := by
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h : (9 * m : ℝ) ≤ 10 * k := by exact_mod_cast hmk
    nlinarith
  calc C⁻¹ * ((3 : ℝ) ^ m) ^ (2 * α / 5) * (C * (3 : ℝ) ^ (-(k : ℝ) * α))
      = (C⁻¹ * C) * (((3 : ℝ) ^ m) ^ (2 * α / 5) * (3 : ℝ) ^ (-(k : ℝ) * α)) := by ring
    _ ≤ 1 * ((3 : ℝ) ^ m) ^ (-(α / 2)) := by
        rw [inv_mul_cancel₀ hC.ne']; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := one_mul _

/-- **The tail of a subadditivity error** at a scale `k ≥ 9m/10` against `(3^m)^{-α/2}`. -/
theorem measure_subadd_gt_le {p : unitInterval} {Z : Configuration 2 → ℝ} {r α C : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hC : 0 < C) {k m : ℕ} (hmk : 9 * m ≤ 10 * k)
    (hZ : IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(k : ℝ) * α))) :
    latticeBondLaw 2 p {ω | ((3 : ℝ) ^ m) ^ (-(α / 2)) < Z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(C⁻¹ ^ r) * ((3 : ℝ) ^ m) ^ (2 * α / 5 * r))) := by
  refine (measure_lt_le_of_isOsBond hr (by positivity) (by positivity) hZ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have h := subadd_ratio_ge hmk hα hC
  have h2 := Real.rpow_le_rpow (by positivity) h hr.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)] at h2
  linarith

/-- The exceptional event of the flatness estimate at the scale `n + 1`. -/
def flatnessBad (Eb : TriadicCube 2 → ℕ → Set (Configuration 2))
    (Z : TriadicCube 2 → Configuration 2 → ℝ) (α : ℝ) (m₂ n : ℕ) : Set (Configuration 2) :=
  if n + 1 < m₂ then Set.univ else
    (⋃ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), Eb ⟨n + 1, 0⟩ k) ∪
    (⋃ z ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
      {ω | ((3 : ℝ) ^ (n + 1)) ^ (1 / 40 : ℝ) <
        TriadicCube.stoppingSize (planarCoarseGood ω) z}) ∪
    (⋃ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ⋃ x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        {ω | ((3 : ℝ) ^ (n + 1)) ^ (-(α / 2)) < Z (scaleCube k x) ω}) ∪
    {ω | ((3 : ℝ) ^ (n + 1)) ^ (-(α / 2)) < Z ⟨n + 1, 0⟩ ω}

theorem measurableSet_flatnessBad {Eb : TriadicCube 2 → ℕ → Set (Configuration 2)}
    (hEb : ∀ U n, MeasurableSet (Eb U n)) {Z : TriadicCube 2 → Configuration 2 → ℝ}
    (hZ : ∀ V, Measurable (Z V)) (α : ℝ) (m₂ n : ℕ) :
    MeasurableSet (flatnessBad Eb Z α m₂ n) := by
  unfold flatnessBad
  split_ifs
  · exact MeasurableSet.univ
  · refine (((Finset.measurableSet_biUnion _ fun k _ => hEb _ k).union
      (Finset.measurableSet_biUnion _ fun z _ => measurableSet_lt measurable_const
        (TriadicCube.measurable_stoppingSize _ measurableSet_mem_planarCoarseGood z))).union
      (Finset.measurableSet_biUnion _ fun k _ => Finset.measurableSet_biUnion _ fun x _ =>
        measurableSet_lt measurable_const (hZ _))).union
      (measurableSet_lt measurable_const (hZ _))

/-- The real inequality collecting the four parts of the exceptional event. -/
theorem flatness_sum_le {c₀ Cb E y : ℝ} (hc₀y : c₀ ≤ y) (hCb : 0 ≤ Cb)
    (hE : 0 ≤ E) (hy1 : 1 ≤ y) :
    c₀ * (Cb * E) + y ^ 2 * (2 * E) + c₀ * (y ^ 2 * (2 * E)) + 2 * E ≤
      (Cb + 6) * (y ^ (3 : ℝ) * E) := by
  have y3 : y ^ (3 : ℝ) = y * y ^ 2 := by
    rw [show (3 : ℝ) = ((2 + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [y3]
  have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
  have hyy : 1 ≤ y * y ^ 2 := one_le_mul_of_one_le_of_one_le hy1 hy2
  have b1 : c₀ ≤ y * y ^ 2 := hc₀y.trans (le_mul_of_one_le_right (by linarith) hy2)
  have b2 : y ^ 2 ≤ y * y ^ 2 := le_mul_of_one_le_left (by positivity) hy1
  have b3 : c₀ * y ^ 2 ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right hc₀y (by positivity)
  have e1 : c₀ * (Cb * E) ≤ Cb * (y * y ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right b1 (mul_nonneg hCb hE)
    linarith
  have e2 : y ^ 2 * (2 * E) ≤ 2 * (y * y ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right b2 (by positivity : (0 : ℝ) ≤ 2 * E)
    linarith
  have e3 : c₀ * (y ^ 2 * (2 * E)) ≤ 2 * (y * y ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right b3 (by positivity : (0 : ℝ) ≤ 2 * E)
    linarith
  have e4 : 2 * E ≤ 2 * (y * y ^ 2 * E) := by
    have := mul_le_mul_of_nonneg_right hyy (by positivity : (0 : ℝ) ≤ 2 * E)
    linarith
  linarith

/-- The restrict part of the exceptional event. -/
theorem measure_restrictPart_le {p : unitInterval}
    {Eb : TriadicCube 2 → ℕ → Set (Configuration 2)} {Cb cb σb : ℝ} (hCb : 0 ≤ Cb)
    (hcb : 0 < cb) (hσb : 0 < σb)
    (hEb : ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n → n < U.scale →
      latticeBondLaw 2 p (Eb U n) ≤ ENNReal.ofReal (Cb * Real.exp (-cb * ((3 : ℝ) ^ n) ^ σb)))
    (m : ℕ) {a σ : ℝ} (ha : 0 ≤ a) (hac : a ≤ cb) (hσσ : σ ≤ 9 * σb / 10) :
    latticeBondLaw 2 p (⋃ k ∈ Finset.Ico ((9 * m + 9) / 10) m, Eb ⟨m, 0⟩ k) ≤
      ENNReal.ofReal ((Finset.Ico ((9 * m + 9) / 10) m).card *
        (Cb * Real.exp (-a * ((3 : ℝ) ^ m) ^ σ))) := by
  have hy1 : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  refine measure_biUnion_le_card_mul _ _ fun k hk => ?_
  have hk9 : 9 * m ≤ 10 * k := by have := (Finset.mem_Ico.1 hk).1; omega
  refine (hEb _ k hk9 (Finset.mem_Ico.1 hk).2).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ hCb
  have h1 : ((3 : ℝ) ^ m) ^ (9 / 10 : ℝ) ≤ (3 : ℝ) ^ k := by
    have h := mul_rpow_le_three_pow (j := k) (m := m) (c := 9 / 10) (d := 0) (by
      have h1' : (9 * m : ℝ) ≤ 10 * k := by exact_mod_cast hk9
      linarith)
    rwa [Real.rpow_zero, one_mul] at h
  have h2 : ((3 : ℝ) ^ m) ^ (9 * σb / 10) ≤ ((3 : ℝ) ^ k) ^ σb := by
    calc ((3 : ℝ) ^ m) ^ (9 * σb / 10) = (((3 : ℝ) ^ m) ^ (9 / 10 : ℝ)) ^ σb := by
          rw [← Real.rpow_mul (by positivity)]; ring_nf
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 hσb.le
  calc Real.exp (-cb * ((3 : ℝ) ^ k) ^ σb) ≤ Real.exp (-cb * ((3 : ℝ) ^ m) ^ (9 * σb / 10)) := by
        apply Real.exp_le_exp.2; nlinarith
    _ ≤ _ := exp_neg_rpow_anti hy1 ha hac hσσ

/-- The reach part of the exceptional event. -/
theorem measure_reachPart_le {p : unitInterval} {θc : ℝ} (hθc : 0 < θc)
    (hmomc : ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θc) ^
        (1 : ℝ))) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θc) ^ (1 : ℝ))
        ∂latticeBondLaw 2 p) ≤ 2)
    (m : ℕ) {a σ : ℝ} (ha : 0 ≤ a) (hac : a ≤ θc⁻¹) (hσσ : σ ≤ 1 / 40) :
    latticeBondLaw 2 p (⋃ z ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
      {ω | ((3 : ℝ) ^ m) ^ (1 / 40 : ℝ) < TriadicCube.stoppingSize (planarCoarseGood ω) z}) ≤
      ENNReal.ofReal (((3 : ℝ) ^ m) ^ 2 * (2 * Real.exp (-a * ((3 : ℝ) ^ m) ^ σ))) := by
  have hy1 : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hU : ((⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ m) ^ 2 := by
    rw [card_toIntegerCube_vertices_eq, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num,
      ← pow_mul, mul_comm]
  rw [← hU]
  refine measure_biUnion_le_card_mul _ _ fun z _ => ?_
  refine (measure_lt_le_of_exp_rpow_moment (latticeBondLaw 2 p) hθc one_pos (hmomc z).1
    (hmomc z).2 (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Real.rpow_one, div_eq_inv_mul, ← neg_mul]
  exact exp_neg_rpow_anti hy1 ha hac hσσ

/-- The subadditivity part of the exceptional event at one cube. -/
theorem measure_subaddPart_le {p : unitInterval} {Z : Configuration 2 → ℝ} {r α C : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hC : 0 < C) {k m : ℕ} (hmk : 9 * m ≤ 10 * k)
    (hZ : IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(k : ℝ) * α))) {a σ : ℝ} (ha : 0 ≤ a)
    (hac : a ≤ C⁻¹ ^ r) (hσσ : σ ≤ 2 * α / 5 * r) :
    latticeBondLaw 2 p {ω | ((3 : ℝ) ^ m) ^ (-(α / 2)) < Z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-a * ((3 : ℝ) ^ m) ^ σ)) := by
  have hy1 : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  refine (measure_subadd_gt_le hr hα hC hmk hZ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (exp_neg_rpow_anti hy1 ha hac hσσ) (by norm_num)

/-- **The probability of the exceptional event of the flatness estimate.** -/
theorem exists_measure_flatnessBad_le {p : unitInterval}
    {Eb : TriadicCube 2 → ℕ → Set (Configuration 2)} {Cb cb σb : ℝ} (hCb : 0 ≤ Cb)
    (hcb : 0 < cb) (hσb : 0 < σb)
    (hEb : ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n → n < U.scale →
      latticeBondLaw 2 p (Eb U n) ≤ ENNReal.ofReal (Cb * Real.exp (-cb * ((3 : ℝ) ^ n) ^ σb)))
    {θc : ℝ} (hθc : 0 < θc)
    (hmomc : ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θc) ^
        (1 : ℝ))) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (planarCoarseGood ω) x / θc) ^ (1 : ℝ))
        ∂latticeBondLaw 2 p) ≤ 2)
    {Z : TriadicCube 2 → Configuration 2 → ℝ} {r α C : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hC : 0 < C) (hZ : ∀ V, IsOsBond 2 p (Z V) r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)))
    (m₂ : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ c σ : ℝ, 0 < c ∧ 0 < σ ∧ ∀ n : ℕ,
      latticeBondLaw 2 p (flatnessBad Eb Z α m₂ n) ≤
        ENNReal.ofReal D * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ σ)) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min cb (min θc⁻¹ (C⁻¹ ^ r)) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = min (9 * σb / 10) (min (1 / 40) (2 * α / 5 * r)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min hcb (lt_min (by positivity) (by positivity))
  have hσ0 : 0 < σ := by rw [hσ]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : a ≤ cb := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ θc⁻¹ := by rw [ha]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ C⁻¹ ^ r := by rw [ha]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hσ1 : σ ≤ 9 * σb / 10 := by rw [hσ]; exact min_le_left _ _
  have hσ2 : σ ≤ 1 / 40 := by rw [hσ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hσ3 : σ ≤ 2 * α / 5 * r := by rw [hσ]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K, hK, hKb⟩ := exists_rpow_mul_exp_le (a := (3 : ℝ)) ha0 hσ0
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = max ((Cb + 6) * K) (Real.exp (a / 2 * ((3 : ℝ) ^ m₂) ^ σ)) :=
    ⟨_, rfl⟩
  have hD1 : (Cb + 6) * K ≤ D := by rw [hD]; exact le_max_left _ _
  have hD2 : Real.exp (a / 2 * ((3 : ℝ) ^ m₂) ^ σ) ≤ D := by rw [hD]; exact le_max_right _ _
  have hD0 : 0 ≤ D := (by positivity : (0 : ℝ) ≤ (Cb + 6) * K).trans hD1
  refine ⟨D, hD0, a / 2, σ, by positivity, hσ0, fun n => ?_⟩
  rw [← ENNReal.ofReal_mul hD0]
  have hx1 : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hxy : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  by_cases hsmall : n + 1 < m₂
  · rw [flatnessBad, if_pos hsmall]
    refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
    have h1 : ((3 : ℝ) ^ n) ^ σ ≤ ((3 : ℝ) ^ m₂) ^ σ :=
      Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) hσ0.le
    have h2 : Real.exp (-(a / 2 * ((3 : ℝ) ^ m₂) ^ σ)) ≤ Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) := by
      apply Real.exp_le_exp.2
      have : 0 ≤ a / 2 := by positivity
      nlinarith
    calc (1 : ℝ) = Real.exp (a / 2 * ((3 : ℝ) ^ m₂) ^ σ) *
          Real.exp (-(a / 2 * ((3 : ℝ) ^ m₂) ^ σ)) := by rw [← Real.exp_add]; simp
      _ ≤ D * Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) :=
          mul_le_mul hD2 h2 (by positivity) hD0
  rw [flatnessBad, if_neg hsmall]
  have hA := measure_restrictPart_le hCb hcb hσb hEb (n + 1) ha0.le ha1 hσ1
  have hB := measure_reachPart_le hθc hmomc (n + 1) ha0.le ha2 hσ2
  have hC' : latticeBondLaw 2 p (⋃ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ⋃ x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        {ω | ((3 : ℝ) ^ (n + 1)) ^ (-(α / 2)) < Z (scaleCube k x) ω}) ≤
      ENNReal.ofReal ((Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1)).card *
        (((3 : ℝ) ^ (n + 1)) ^ 2 * (2 * Real.exp (-a * ((3 : ℝ) ^ (n + 1)) ^ σ)))) := by
    refine measure_biUnion_le_card_mul _ _ fun k hk => ?_
    have hU : ((⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℝ) =
        ((3 : ℝ) ^ (n + 1)) ^ 2 := by
      rw [card_toIntegerCube_vertices_eq, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num,
        ← pow_mul, mul_comm]
    rw [← hU]
    refine measure_biUnion_le_card_mul _ _ fun z _ => ?_
    have hk9 : 9 * (n + 1) ≤ 10 * k := by have := (Finset.mem_Ico.1 hk).1; omega
    have hZk := hZ (scaleCube k z)
    rw [scale_scaleCube] at hZk
    exact measure_subaddPart_le hr hα hC hk9 hZk ha0.le ha3 hσ3
  have hD' := measure_subaddPart_le hr hα hC (k := n + 1) (m := n + 1) (by omega) (hZ ⟨n + 1, 0⟩)
    ha0.le ha3 hσ3
  set y : ℝ := (3 : ℝ) ^ (n + 1) with hy
  set E : ℝ := Real.exp (-a * y ^ σ) with hE
  set c₀ : ℝ := ((Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1)).card : ℝ) with hc₀
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have hc₀0 : 0 ≤ c₀ := Nat.cast_nonneg _
  have hc₀y : c₀ ≤ y := by
    rw [hc₀, Nat.card_Ico]
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ y := by
      rw [hy]; exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le
    exact (Nat.cast_le.2 (Nat.sub_le _ _)).trans h2
  have n1 : 0 ≤ c₀ * (Cb * E) := mul_nonneg hc₀0 (mul_nonneg hCb hE0)
  have n2 : 0 ≤ y ^ 2 * (2 * E) := mul_nonneg (by positivity) (by linarith)
  have n3 : 0 ≤ c₀ * (y ^ 2 * (2 * E)) := mul_nonneg hc₀0 n2
  have n4 : 0 ≤ 2 * E := by linarith
  have htot : c₀ * (Cb * E) + y ^ 2 * (2 * E) + c₀ * (y ^ 2 * (2 * E)) + 2 * E ≤
      D * Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) := by
    have h1 := flatness_sum_le hc₀y hCb hE0 hy1
    have h2 : y ^ (3 : ℝ) * E ≤ K * Real.exp (-(a / 2) * y ^ σ) := hKb y hy1
    have h3 : Real.exp (-(a / 2) * y ^ σ) ≤ Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) := by
      apply Real.exp_le_exp.2
      have : ((3 : ℝ) ^ n) ^ σ ≤ y ^ σ := Real.rpow_le_rpow (by positivity) hxy hσ0.le
      have : 0 ≤ a / 2 := by positivity
      nlinarith
    have h4 : 0 ≤ Cb + 6 := by linarith
    calc _ ≤ (Cb + 6) * (y ^ (3 : ℝ) * E) := h1
      _ ≤ (Cb + 6) * (K * Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ)) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hK)) h4
      _ = (Cb + 6) * K * Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) := by ring
      _ ≤ D * Real.exp (-(a / 2) * ((3 : ℝ) ^ n) ^ σ) :=
          mul_le_mul_of_nonneg_right hD1 (Real.exp_pos _).le
  calc latticeBondLaw 2 p _ ≤ latticeBondLaw 2 p _ + latticeBondLaw 2 p _ := measure_union_le _ _
    _ ≤ (latticeBondLaw 2 p _ + latticeBondLaw 2 p _) + latticeBondLaw 2 p _ :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((latticeBondLaw 2 p _ + latticeBondLaw 2 p _) + latticeBondLaw 2 p _) +
          latticeBondLaw 2 p _ :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ((ENNReal.ofReal (c₀ * (Cb * E)) + ENNReal.ofReal (y ^ 2 * (2 * E))) +
          ENNReal.ofReal (c₀ * (y ^ 2 * (2 * E)))) + ENNReal.ofReal (2 * E) :=
        add_le_add (add_le_add (add_le_add hA hB) hC') hD'
    _ = ENNReal.ofReal (c₀ * (Cb * E) + y ^ 2 * (2 * E) + c₀ * (y ^ 2 * (2 * E)) + 2 * E) := by
        rw [ENNReal.ofReal_add (add_nonneg (add_nonneg n1 n2) n3) n4,
          ENNReal.ofReal_add (add_nonneg n1 n2) n3, ENNReal.ofReal_add n1 n2]
    _ ≤ _ := ENNReal.ofReal_le_ofReal htot


/-- The conditions off the exceptional event of the flatness estimate. -/
theorem of_not_mem_flatnessBad {Eb : TriadicCube 2 → ℕ → Set (Configuration 2)}
    {Z : TriadicCube 2 → Configuration 2 → ℝ} {α : ℝ} {m₂ n : ℕ} {ω : Configuration 2}
    (h : ω ∉ flatnessBad Eb Z α m₂ n) :
    m₂ ≤ n + 1 ∧ (∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1), ω ∉ Eb ⟨n + 1, 0⟩ k) ∧
      (∀ z ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        TriadicCube.stoppingSize (planarCoarseGood ω) z ≤ ((3 : ℝ) ^ (n + 1)) ^ (1 / 40 : ℝ)) ∧
      (∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
        ∀ x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
          Z (scaleCube k x) ω ≤ ((3 : ℝ) ^ (n + 1)) ^ (-(α / 2))) ∧
      Z ⟨n + 1, 0⟩ ω ≤ ((3 : ℝ) ^ (n + 1)) ^ (-(α / 2)) := by
  have hm2 : ¬ (n + 1 < m₂) := fun h' => h (by rw [flatnessBad, if_pos h']; trivial)
  rw [flatnessBad, if_neg hm2] at h
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
    not_lt] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨not_lt.1 hm2, h1, h2, h3, h4⟩

/-- `(3^m)^{1/40} ≤ 3^{⌊(9m+9)/10⌋}`. -/
theorem rpow_forty_le_three_pow (m : ℕ) :
    ((3 : ℝ) ^ m) ^ (1 / 40 : ℝ) ≤ 3 ^ ((9 * m + 9) / 10) := by
  have h2 : m ≤ 40 * ((9 * m + 9) / 10) := by omega
  have h2' : (m : ℝ) ≤ 40 * (((9 * m + 9) / 10 : ℕ) : ℝ) := by exact_mod_cast h2
  have h := mul_rpow_le_three_pow (j := (9 * m + 9) / 10) (m := m) (c := 1 / 40) (d := 0)
    (by linarith)
  rwa [Real.rpow_zero, one_mul] at h

/-- The subadditivity error of a resolved cube for a unit slope. -/
theorem abs_planarNu_sub_le_of_resolved {p : unitInterval} {ω : Configuration 2}
    (hP : PlanarPartitionEvent ω) {V : TriadicCube 2} (hV : PlanarResolved ω V) (i : Fin 2)
    {Z : ℝ} {ε : ℝ} (hZ : Z ≤ ε)
    (hb : |(if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V (Pi.single i 1)
      else 0) - 1 / 2 * ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j *
        (planarAhom p *ᵥ (Pi.single i 1 : Fin 2 → ℝ)) j| ≤
      Z * ((Pi.single i 1 : Fin 2 → ℝ) 0 ^ 2 + (Pi.single i 1 : Fin 2 → ℝ) 1 ^ 2)) :
    |planarNu ω V (Pi.single i 1) - 1 / 2 * ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j *
        (planarAhom p *ᵥ (Pi.single i 1 : Fin 2 → ℝ)) j| ≤ ε := by
  rw [if_pos ⟨hP, hV⟩, sq_single_add, mul_one] at hb
  exact hb.trans hZ

/-- **Lemma 5.8, (5.33), with a minimal scale of class `O_s`**, from Proposition 5.2 for `ν` in
the form `O_s`. -/
theorem exists_planarNuFlatness_os {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hsub : PlanarNuSubaddOsTwo p) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ s θ : ℝ, 0 < s ∧ 0 < θ ∧
      ∃ Y : Configuration 2 → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧ IsOsBond 2 p Y s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ n : ℕ, Y ω < 3 ^ n → ∀ i : Fin 2,
        planarFlatnessError ⟨n + 1, 0⟩
            (coarsen ω ⟨n + 1, 0⟩ (planarNuSolution ω ⟨n + 1, 0⟩ (Pi.single i 1)))
            (Pi.single i 1) ≤ 2 * 9 ^ n * μ ^ n := by
  obtain ⟨A₀, hRH⟩ := planarRHFailureBound_holds hpc
  obtain ⟨ε', hε', t, -, hMU⟩ := planar_meyers_rh_uniform A₀
  have hp1' : 1 < 1 + ε' / 2 := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp1'
  obtain ⟨A₂, Aτ, K, hA₂, hAτ, hK, Eb, hEbm, ⟨Cb, cb, σb, hCb, hcb, hσb, hEb⟩, hincl⟩ :=
    exists_restrictBad_os hpc hRH t ⌈3 * (1 + ε' / 2).conjExponent⌉₊
  obtain ⟨CMey, hCMey, hMey⟩ := hMU K hK
  have hΛ := restrictConst_nonneg (r := (1 + ε' / 2).conjExponent) (p := 1 + ε' / 2) (A₂ := A₂)
    hAτ hCMey
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨hHc, ⟨θc, hθc, hmomc⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num)
    (latticeBondLaw 2 p) planarCoarseGood measurableSet_mem_planarCoarseGood hC₀ hc₀ one_pos hq
  obtain ⟨C1, cR, s0R, hC1, hcR, hs0R, -, hfail⟩ := hRH
  obtain ⟨hu, -, -⟩ := partition_estimates_general (d := 2) (by norm_num) (latticeBondLaw 2 p)
    (planarRHGood A₀) (measurableSet_mem_planarRHGood A₀) hC1 hcR hs0R hfail
  obtain ⟨rs, αs, Cs, hrs, hαs, hCs, hZ⟩ := hsub
  choose Z hZm hZ0 hZos hZb using hZ
  obtain ⟨CMf, hCMf, hflat⟩ := exists_planarFlatness_le_of_reach
  obtain ⟨μ, hμ0, hμ1, m₁, hdec⟩ := exists_flatnessBound_le (CM := CMf)
    (KE := (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
      (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2)
    (Λ := restrictConst Aτ (1 + ε' / 2).conjExponent CMey (1 + ε' / 2) A₂)
    (CN := 1296 * 162001 ^ 2) (γ := αs / 2) hCMf (sq_nonneg _) hΛ (by norm_num) (by positivity)
  obtain ⟨D, hD, c, σ, hc, hσ, hprob⟩ := exists_measure_flatnessBad_le hCb hcb hσb hEb hθc hmomc
    hrs hαs hCs hZos (max m₁ 10)
  obtain ⟨θ, hθ, Y, hYm, hY0, hYos, hYae⟩ := exists_isOsBond_of_events
    (flatnessBad Eb Z αs (max m₁ 10)) (measurableSet_flatnessBad hEbm hZm αs (max m₁ 10))
    ENNReal.ofReal_ne_top hσ hc hprob
  refine ⟨μ, hμ0, hμ1, σ, θ, hσ, hθ, Y, hYm, hY0, hYos, ?_⟩
  filter_upwards [hYae, ae_planarPartitionEvent hpc, hHc, hu, ae_planarReach_ne_top hpc, hincl]
    with ω hY hP hH hu' hfin hincl' n hn i
  obtain ⟨hm2, hnotEb, hss, hZk, hZU⟩ := of_not_mem_flatnessBad (hY n hn)
  have hm10 : 10 ≤ n + 1 := (le_max_right _ _).trans hm2
  have hm1 : m₁ ≤ n + 1 := (le_max_left _ _).trans hm2
  have hy1 : (1 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hreach : ∀ z ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
      planarReach ω z ≤ ENNReal.ofReal (((3 : ℝ) ^ (n + 1)) ^ (1 / 40 : ℝ)) := fun z hz =>
    (planarReach_le_stoppingSize hH z).trans (ENNReal.ofReal_le_ofReal (hss z hz))
  have hS1 : 1 ≤ ((3 : ℝ) ^ (n + 1)) ^ (1 / 40 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
  have hSm := rpow_forty_le_three_pow (n + 1)
  have hs : (∀ x, ∀ z ∈ cube (stoppingScale (planarRHGood A₀ ω) x) x,
        stoppingScale (planarRHGood A₀ ω) z = stoppingScale (planarRHGood A₀ ω) x) ∧
      (∀ x y, supDist x y ≤ 1 →
        stoppingScale (planarRHGood A₀ ω) y ≤ stoppingScale (planarRHGood A₀ ω) x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), stoppingScale (planarRHGood A₀ ω) y ≤ k →
        (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω :=
    ⟨fun x z hz => stoppingScale_eq_of_mem_cube hu' hz,
      fun x y hxy => stoppingScale_le_of_supDist hu' hxy,
      fun k y hk => mem_of_stoppingScale_le hu' hk⟩
  have hR : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      planarNuRestrictError ω ⟨n + 1, 0⟩ k (Pi.single i 1) ≤
        restrictConst Aτ (1 + ε' / 2).conjExponent CMey (1 + ε' / 2) A₂ *
          (planarNuDefect ω ⟨n + 1, 0⟩ k (Pi.single i 1) /
            (⟨n + 1, 0⟩ : TriadicCube 2).volume) := by
    intro k hk
    have hk1 := (Finset.mem_Ico.1 hk).1
    have hk2 := (Finset.mem_Ico.1 hk).2
    have hk9 : 9 * (⟨n + 1, 0⟩ : TriadicCube 2).scale ≤ 10 * k := by
      change 9 * (n + 1) ≤ 10 * k; omega
    exact planarNuRestrictError_le_of_not_mem_restrictBad_rh (A₀ := A₀)
      (s := fun ω => stoppingScale (planarRHGood A₀ ω)) (t := t) (K := K)
      (τ := ⌈3 * (1 + ε' / 2).conjExponent⌉₊) (Aτ := Aτ) (A₂ := A₂) (U := ⟨n + 1, 0⟩) (n := k)
      hpq (Nat.le_ceil _) hCMey hAτ hA₂ hMey hP hs hfin hk9 hk2
      (fun hbad => hnotEb k hk (hincl' _ _ hbad)) (Pi.single i 1)
  have hsubk : ∀ k ∈ Finset.Ico ((9 * (n + 1) + 9) / 10) (n + 1),
      ∀ x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        |planarNu ω (scaleCube k x) (Pi.single i 1) - 1 / 2 * ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j *
          (planarAhom p *ᵥ (Pi.single i 1 : Fin 2 → ℝ)) j| ≤
          ((3 : ℝ) ^ (n + 1)) ^ (-(αs / 2)) := by
    intro k hk x hx
    have hkm : k ≤ n + 1 := (Finset.mem_Ico.1 hk).2.le
    have hres : PlanarResolved ω (scaleCube k x) := by
      refine planarResolved_of_reach hP
        (scaleCube_subset hkm (((⟨n + 1, 0⟩ : TriadicCube 2).mem_toIntegerCube_vertices x).1 hx))
        hreach ?_
      rw [scale_scaleCube]
      exact hSm.trans (pow_le_pow_right₀ (by norm_num) (Finset.mem_Ico.1 hk).1)
    exact abs_planarNu_sub_le_of_resolved hP hres i (hZk k hk x hx) (hZb _ ω _)
  have hUe : |planarNu ω ⟨n + 1, 0⟩ (Pi.single i 1) - 1 / 2 * ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j *
      (planarAhom p *ᵥ (Pi.single i 1 : Fin 2 → ℝ)) j| ≤ ((3 : ℝ) ^ (n + 1)) ^ (-(αs / 2)) := by
    have hres : PlanarResolved ω ⟨n + 1, 0⟩ := planarResolved_of_reach hP (subset_refl _) hreach
      (hSm.trans (pow_le_pow_right₀ (by norm_num)
        (by change (9 * (n + 1) + 9) / 10 ≤ n + 1; omega)))
    exact abs_planarNu_sub_le_of_resolved hP hres i hZU (hZb _ ω _)
  have h := hflat ω hP (n + 1) i (by omega) hS1 hSm hreach hΛ hR hsubk hUe
  have h2 := hdec (n + 1) hm1
  simp only [Nat.add_sub_cancel] at h2
  exact h.trans h2

end Rigidity.Proofs.Regularity
