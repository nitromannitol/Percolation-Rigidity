import Rigidity.Proofs.Green.GeneralFluxScale
import Rigidity.Proofs.Green.DarioGuFluxWeakNormBad
import Rigidity.Proofs.WeakPoincare.VeryGood

/-!
# The bad scales of the minimal scale of Proposition B.1 of Dario–Gu on `ℤ^d`

The extension of `DarioGuFluxWeakNormBad.lean` from `ℤ²` to `ℤ^d`. The bad scales are bounded by:

* `measure_stoppingSize_lt_le`: `P(∃ z ∈ S, L < size(□_𝒫(z))) ≤ |S| · 2 e^{-L/θ}`, from the
  exponential moments of the sizes of the partition cubes (`partition_estimates`);
* `exists_measure_toReal_lt_leD`: a variable with moments `E[X^q] ≤ (A q^κ)^q` exceeds `t` with
  probability at most `2 exp(-(t/C)^s)`, and is finite almost surely;
* `exists_summable_badBoundD`: the resulting bounds
  `41^d 9^{dn} · 2 e^{-⌊3^{βn}⌋/θ} + 2 exp(-(3^{βn}/((n + 1) C))^s)` are summable against
  `exp((3^{n+1})^{s'})` for some `s' > 0` (`summable_densityBad`).
-/

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
  Rigidity.External Rigidity.Proofs.S2 Rigidity.Poincare.GeneralDim
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} {p : unitInterval}

/-! ### The sizes of the partition cubes -/

theorem exists_isOsBond_stoppingSizeD [NeZero d] (hd : 2 ≤ d)
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ z : Vertex d,
      IsOsBond d p (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 1 θ := by
  obtain ⟨θ, hθ, hexp⟩ := (partition_estimates hd hpc).2.1
  refine ⟨θ, hθ, fun z => ?_⟩
  have e : (fun ω => Real.exp (Real.rpow
      (max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z / θ) 0) 1)) =
      fun ω => Real.exp (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z / θ) := by
    funext ω
    rw [max_eq_left (div_nonneg (stoppingSize_nonneg _ z) hθ.le)]
    simp
  rw [IsOsBond, e]
  exact hexp z

/-- **The bad event of the sizes of the partition cubes.** -/
theorem measure_stoppingSize_lt_le {θ : ℝ} (hθ : 0 < θ)
    (hos : ∀ z : Vertex d,
      IsOsBond d p (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) 1 θ)
    (S : Finset (Vertex d)) (L : ℕ) :
    latticeBondLaw d p
        {ω | ∃ z ∈ S, (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ≤
      ENNReal.ofReal (S.card * (2 * Real.exp (-(L / θ)))) := by
  have hz : ∀ z, latticeBondLaw d p
      {ω | (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ≤
      ENNReal.ofReal (2 * Real.exp (-(L / θ))) := by
    intro z
    have h := Rigidity.WeakPoincare.measure_lt_le_of_isOsBond (fun ω => stoppingSize_nonneg _ z)
      hθ one_pos (hos z) (t := (L : ℝ)) (Nat.cast_nonneg _)
    simp only [Real.rpow_one] at h
    exact h
  have hset : {ω | ∃ z ∈ S, (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} =
      ⋃ z ∈ S, {ω | (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := by
    ext ω
    simp
  rw [hset]
  calc latticeBondLaw d p
        (⋃ z ∈ S, {ω | (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z})
      ≤ ∑ z ∈ S, latticeBondLaw d p
          {ω | (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ S, ENNReal.ofReal (2 * Real.exp (-(L / θ))) := Finset.sum_le_sum fun z _ => hz z
    _ = ENNReal.ofReal (S.card * (2 * Real.exp (-(L / θ)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

theorem measurableSet_stoppingSize_lt (S : Finset (Vertex d)) (L : ℕ) :
    MeasurableSet
      {ω : Configuration d | ∃ z ∈ S, (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := by
  have hset : {ω : Configuration d |
      ∃ z ∈ S, (L : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} =
      ⋃ z ∈ S, (fun ω => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z) ⁻¹' Set.Ioi L := by
    ext ω
    simp
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun z _ =>
    measurable_stoppingSize_goodCubes z measurableSet_Ioi

/-- On the partition event, the side of the partition cube is the stopping size. -/
theorem partSide_le_of_stoppingSize_le {ω : Configuration d} (hP : PartitionEvent ω)
    {z : Vertex d} {L : ℕ} (h : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ≤ L) :
    partSide ω z ≤ L := by
  have hsize : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z =
      (3 : ℝ) ^ (partitionCube ω z).scale :=
    TriadicCube.stoppingSize_eq_of_mem (mem_partitionCube hP z) (partitionCube_spec hP z).2
  rw [hsize] at h
  have : ((partSide ω z : ℕ) : ℝ) ≤ L := by
    rw [partSide]
    push_cast
    exact h
  exact_mod_cast this

/-! ### Variables with moments of polynomial growth -/

theorem exists_measure_toReal_lt_leD {A κ : ℝ} (hA : 0 < A) (hκ : 0 < κ) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ X : Configuration d → ℝ≥0∞, Measurable X →
      GrowthMomentsD p X A κ → ∀ t : ℝ, 0 ≤ t →
        latticeBondLaw d p {ω | t < (X ω).toReal} ≤
          ENNReal.ofReal (2 * Real.exp (-(t / C) ^ s)) := by
  have hs : 0 < 1 / (2 * κ) := by positivity
  have hsk : 1 / (2 * κ) * κ < 1 := by
    rw [one_div_mul_eq_div, div_lt_one (by positivity)]
    linarith
  obtain ⟨C, hC, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p) hA hs hsk
  refine ⟨1 / (2 * κ), C, hs, hC, fun X hXm hX t ht => ?_⟩
  have hos : IsOsBond d p (fun ω => (X ω).toReal) (1 / (2 * κ)) C :=
    GeneralDim.isOsBond_of_ae_ofReal_le hA.le hmom hXm.ennreal_toReal (fun ω => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_toReal_le) hX
  exact Rigidity.WeakPoincare.measure_lt_le_of_isOsBond (fun ω => ENNReal.toReal_nonneg) hC hs hos ht

theorem measure_eq_top_of_growthMomentsD {A κ : ℝ} {X : Configuration d → ℝ≥0∞}
    (hXm : Measurable X) (hX : GrowthMomentsD p X A κ) :
    latticeBondLaw d p {ω | X ω = ⊤} = 0 := by
  have h1 := hX 1 le_rfl
  simp only [ENNReal.rpow_one] at h1
  have hfin : ∫⁻ ω, X ω ∂latticeBondLaw d p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have := ae_lt_top hXm hfin
  rw [ae_iff] at this
  simpa [lt_top_iff_ne_top] using this

/-! ### Summability -/

/-- The bound of the probability of the bad scale `n`. -/
noncomputable def badBoundD (d n₀ : ℕ) (β θ C s₁ : ℝ) (n : ℕ) : ℝ :=
  if n < n₀ then 1 else
    41 ^ d * 9 ^ (d * n) * (2 * Real.exp (-((⌊(3 : ℝ) ^ (β * n)⌋₊ : ℝ) / θ))) +
      2 * Real.exp (-((3 : ℝ) ^ (β * n) / ((n + 1) * C)) ^ s₁)

theorem badBoundD_nonneg (d n₀ : ℕ) (β θ C s₁ : ℝ) (n : ℕ) : 0 ≤ badBoundD d n₀ β θ C s₁ n := by
  unfold badBoundD
  split_ifs
  · exact zero_le_one
  · positivity

/-- **The bounds of the bad scales are summable** against `exp((3^{n+1})^s)` for some `s > 0`. -/
theorem exists_summable_badBoundD (d n₀ : ℕ) {β θ C s₁ : ℝ} (hβ : 0 < β) (hθ : 0 < θ) (hC : 0 < C)
    (hs₁ : 0 < s₁) :
    ∃ s : ℝ, 0 < s ∧
      Summable fun n : ℕ => badBoundD d n₀ β θ C s₁ n * Real.exp ((1 * 3 ^ (n + 1)) ^ s) := by
  set c₂ := 2 / (β * Real.log 3) + 1 with hc₂
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc₂0 : 0 < c₂ := by positivity
  set s := min (β * 1 / 2) (β / 2 * s₁ / 2) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  refine ⟨s, hs0, ?_⟩
  have hsum1 := summable_densityBad (α := β) (s₀ := 1) (C₁ := θ) hβ one_pos hθ d
  have hsum2 := summable_densityBad (α := β / 2) (s₀ := s₁) (C₁ := c₂ * C) (by positivity) hs₁
    (by positivity) 0
  have hfin : Summable fun n : ℕ => (if n < n₀ then (1 : ℝ) else 0) *
      Real.exp ((1 * 3 ^ (n + 1)) ^ s) :=
    summable_of_ne_finset_zero (s := Finset.range n₀) fun n hn => by
      rw [Finset.mem_range] at hn
      rw [if_neg hn, zero_mul]
  have hx1 : ∀ n : ℕ, (1 : ℝ) ≤ 1 * 3 ^ (n + 1) := fun n => by
    rw [one_mul]
    exact one_le_pow₀ (by norm_num)
  have hA : ∀ n : ℕ, 41 ^ d * 9 ^ (d * n) * (2 * Real.exp (-((⌊(3 : ℝ) ^ (β * n)⌋₊ : ℝ) / θ))) *
      Real.exp ((1 * 3 ^ (n + 1)) ^ s) ≤ 2 * 41 ^ d * Real.exp (1 / θ) * (2738 * 9 ^ (d * n) *
        Real.exp (-((((3 : ℝ) ^ β) ^ n / θ) ^ (1 : ℝ))) *
        Real.exp ((1 * 3 ^ (n + 1)) ^ (β * 1 / 2))) := by
    intro n
    set x := (3 : ℝ) ^ (β * n) with hx
    have hxn : x = ((3 : ℝ) ^ β) ^ n := rpow_mul_natCast_eq 3 (by norm_num) β n
    have hfloor : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x
      linarith
    have he : Real.exp (-((⌊x⌋₊ : ℝ) / θ)) ≤
        Real.exp (1 / θ) * Real.exp (-((x / θ) ^ (1 : ℝ))) := by
      rw [Real.rpow_one, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : (x - 1) / θ ≤ (⌊x⌋₊ : ℝ) / θ := div_le_div_of_nonneg_right hfloor hθ.le
      have e : (x - 1) / θ = x / θ - 1 / θ := by ring
      linarith
    have hE := exp_le_exp_rpow_of_le (hx1 n) (min_le_left _ _ : s ≤ β * 1 / 2)
    rw [← hxn]
    set E' := Real.exp ((1 * 3 ^ (n + 1)) ^ (β * 1 / 2))
    set F := Real.exp (-((x / θ) ^ (1 : ℝ)))
    calc 41 ^ d * 9 ^ (d * n) * (2 * Real.exp (-((⌊x⌋₊ : ℝ) / θ))) *
          Real.exp ((1 * 3 ^ (n + 1)) ^ s)
        ≤ 41 ^ d * 9 ^ (d * n) * (2 * (Real.exp (1 / θ) * F)) * E' := by gcongr
      _ = 2 * (41 ^ d * (Real.exp (1 / θ) * 9 ^ (d * n) * F * E')) := by ring
      _ ≤ 2 * 2738 * (41 ^ d * (Real.exp (1 / θ) * 9 ^ (d * n) * F * E')) := by
          have : 0 ≤ 41 ^ d * (Real.exp (1 / θ) * 9 ^ (d * n) * F * E') := by positivity
          linarith
      _ = 2 * 41 ^ d * Real.exp (1 / θ) * (2738 * 9 ^ (d * n) * F * E') := by ring
  have hB : ∀ n : ℕ, 2 * Real.exp (-((3 : ℝ) ^ (β * n) / ((n + 1) * C)) ^ s₁) *
      Real.exp ((1 * 3 ^ (n + 1)) ^ s) ≤ 2 / 2738 * (2738 * 9 ^ (0 * n) *
        Real.exp (-((((3 : ℝ) ^ (β / 2)) ^ n / (c₂ * C)) ^ s₁)) *
        Real.exp ((1 * 3 ^ (n + 1)) ^ (β / 2 * s₁ / 2))) := by
    intro n
    set a := (3 : ℝ) ^ (β / 2 * n) with ha
    have ha0 : 0 < a := by positivity
    have han : a = ((3 : ℝ) ^ (β / 2)) ^ n := rpow_mul_natCast_eq 3 (by norm_num) (β / 2) n
    have hxa : (3 : ℝ) ^ (β * n) = a * a := by
      rw [ha, ← Real.rpow_add (by norm_num)]
      ring_nf
    have hden : (n : ℝ) + 1 ≤ c₂ * a := one_add_le_mul_rpow hβ n
    have hx2 : a / (c₂ * C) ≤ a * a / ((n + 1) * C) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hden (mul_nonneg ha0.le hC.le)]
    have he2 : Real.exp (-(a * a / ((n + 1) * C)) ^ s₁) ≤ Real.exp (-(a / (c₂ * C)) ^ s₁) :=
      Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow (by positivity) hx2 hs₁.le))
    have hE := exp_le_exp_rpow_of_le (hx1 n) (min_le_right _ _ : s ≤ β / 2 * s₁ / 2)
    rw [hxa, zero_mul, pow_zero, ← han]
    calc 2 * Real.exp (-(a * a / ((n + 1) * C)) ^ s₁) * Real.exp ((1 * 3 ^ (n + 1)) ^ s)
        ≤ 2 * Real.exp (-(a / (c₂ * C)) ^ s₁) *
            Real.exp ((1 * 3 ^ (n + 1)) ^ (β / 2 * s₁ / 2)) := by gcongr
      _ = 2 / 2738 * (2738 * 1 * Real.exp (-(a / (c₂ * C)) ^ s₁) *
            Real.exp ((1 * 3 ^ (n + 1)) ^ (β / 2 * s₁ / 2))) := by ring
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (badBoundD_nonneg _ _ _ _ _ _ n)
    (Real.exp_pos _).le) (fun n => ?_)
    (hfin.add ((hsum1.mul_left (2 * 41 ^ d * Real.exp (1 / θ))).add (hsum2.mul_left (2 / 2738))))
  have hT1 : 0 ≤ 2 * 41 ^ d * Real.exp (1 / θ) * (2738 * 9 ^ (d * n) *
      Real.exp (-((((3 : ℝ) ^ β) ^ n / θ) ^ (1 : ℝ))) *
      Real.exp ((1 * 3 ^ (n + 1)) ^ (β * 1 / 2))) := by positivity
  have hT2 : 0 ≤ 2 / 2738 * (2738 * 9 ^ (0 * n) *
      Real.exp (-((((3 : ℝ) ^ (β / 2)) ^ n / (c₂ * C)) ^ s₁)) *
      Real.exp ((1 * 3 ^ (n + 1)) ^ (β / 2 * s₁ / 2))) := by positivity
  unfold badBoundD
  split_ifs with hn
  · linarith
  · rw [zero_mul, zero_add, add_mul]
    exact add_le_add (hA n) (hB n)

end Rigidity.Green.GeneralFlux
