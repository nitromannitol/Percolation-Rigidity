import Rigidity.Proofs.Corrector.GeneralLinftyIteration
import Rigidity.Proofs.Corrector.DarioOptimalCorrector
import Rigidity.Proofs.S2.ClusterDensityBounds

/-!
# Steps 5 and 6 of the proof of Dario's Theorem 1 in dimension `d ≥ 3`

* Step 5 (`isOsBond_sub_of_linftyIterationData_zero`): when the box oscillations of the coarsened
  corrector are bounded uniformly in the scale (the hypotheses of Steps 1–4 with the growth exponent
  `a = 0`, the form of (5.5) in dimension `d ≥ 3`), the moment bound of Steps 1–4,
  `E|F_0(x) - F_0(0)|^q ≤ (K q^k)^q`, gives `|F_0(x) - F_0(0)| ≤ O_s(C)` for every `s < 1/k`,
  uniformly in `x`;
* Step 6 and the assembly (`darioOptimalCorrectorThree_of_coarsened`): with the coarsening error
  `|χ_p(x) - [χ_p]_𝒫(x)| 1_{x ∈ 𝒞_∞} ≤ O_s(C)` of Step 6 (5.10) and the linearity of the corrector
  in the slope (from the qualitative corrector input, proved in every dimension), Dario's Theorem 1
  in dimension `d ≥ 3`, `|χ_p(x) - χ_p(y)| 1_{x, y ∈ 𝒞_∞} ≤ O_s(C |p|)`
  (`DarioOptimalCorrectorThree`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

variable {d : ℕ}

/-- A scale `m ≥ 1` with `|x|_∞ < 3^{m+1}`. -/
theorem exists_scale_of_vertex (x : Vertex d) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ) := by
  set M : ℕ := Finset.univ.sup fun i => (x i).natAbs with hM
  refine ⟨M + 1, by omega, fun i => ?_⟩
  have h1 : (x i).natAbs ≤ M := Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  have h2 : M + 1 + 1 < 3 ^ (M + 1 + 1) := Nat.lt_pow_self (by norm_num)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast (show (x i).natAbs < 3 ^ (M + 1 + 1) by omega)

/-- **Dario, Step 5 of the proof of Theorem 1, in dimension `d ≥ 3`**: under the hypotheses of
Steps 1–4 with the growth exponent `0`, for every `s < 1/k`, `|F_0(x) - F_0(0)| ≤ O_s(C)` with `C`
independent of `x`. -/
theorem isOsBond_sub_of_linftyIterationData_zero {p : unitInterval} {A B k : ℝ} (hA : 0 ≤ A)
    {s : ℝ} (hs : 0 < s) (hsk : s * k < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : Vertex d → Vertex d → Configuration d → ℝ,
      LinftyIterationData p F A B k 0 → ∀ x : Vertex d,
      IsOsBond d p (fun ω => |F 0 x ω - F 0 0 ω|) s C := by
  obtain ⟨C₁, hC₁, hmom⟩ := isOsBond_of_moment_le (d := d) (p := p) (A := 1) one_pos hs hsk
  set K := (36 * (7 + 2 * 9 ^ d)) * max A B with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max A B := le_trans hA (le_max_left _ _)
    positivity
  refine ⟨C₁ * (K + 1), by positivity, fun F hD x => ?_⟩
  obtain ⟨m, hm1, hx⟩ := exists_scale_of_vertex x
  set c := K + 1 with hc
  have hc0 : 0 < c := by positivity
  have hXm : Measurable fun ω => |F 0 x ω - F 0 0 ω| / c :=
    ((hD.meas 0 x).sub (hD.meas 0 0)).abs.div_const c
  have hX : IsOsBond d p (fun ω => |F 0 x ω - F 0 0 ω| / c) s C₁ := by
    refine hmom _ hXm (fun ω => by positivity) fun q hq => ?_
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hmom' := hD.mom_sub_le hm1 hx hq
    rw [mul_zero, Real.rpow_zero, mul_one] at hmom'
    have hpt : ∀ ω, (|F 0 x ω - F 0 0 ω| / c) ^ q = |F 0 x ω - F 0 0 ω| ^ q / c ^ q :=
      fun ω => Real.div_rpow (abs_nonneg _) hc0.le q
    have hbound : (K * q ^ k) ^ q / c ^ q ≤ (1 * q ^ k) ^ q := by
      have hqk : 0 ≤ q ^ k := Real.rpow_nonneg hq0 k
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 q), one_mul]
      have h1 : (K * q ^ k) ^ q ≤ ((K + 1) * q ^ k) ^ q :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) hq0
      calc (K * q ^ k) ^ q ≤ ((K + 1) * q ^ k) ^ q := h1
        _ = (q ^ k) ^ q * c ^ q := by
            rw [hc, Real.mul_rpow (show (0 : ℝ) ≤ K + 1 by positivity) hqk]
            ring
    have hlin : ∫⁻ ω, ENNReal.ofReal ((|F 0 x ω - F 0 0 ω| / c) ^ q) ∂latticeBondLaw d p ≤
        ENNReal.ofReal ((1 * q ^ k) ^ q) := by
      calc ∫⁻ ω, ENNReal.ofReal ((|F 0 x ω - F 0 0 ω| / c) ^ q) ∂latticeBondLaw d p
          = ∫⁻ ω, ENNReal.ofReal (|F 0 x ω - F 0 0 ω| ^ q) * ENNReal.ofReal (1 / c ^ q)
              ∂latticeBondLaw d p := by
            refine lintegral_congr fun ω => ?_
            rw [hpt, ← ENNReal.ofReal_mul (by positivity), mul_one_div]
        _ = mom p (fun ω => F 0 x ω - F 0 0 ω) q * ENNReal.ofReal (1 / c ^ q) :=
            lintegral_mul_const _ (measurable_ofReal_abs_rpow ((hD.meas 0 x).sub (hD.meas 0 0)) q)
        _ ≤ ENNReal.ofReal ((K * q ^ k) ^ q) * ENNReal.ofReal (1 / c ^ q) := by gcongr
        _ = ENNReal.ofReal ((K * q ^ k) ^ q / c ^ q) := by
            rw [← ENNReal.ofReal_mul (by positivity), mul_one_div]
        _ ≤ ENNReal.ofReal ((1 * q ^ k) ^ q) := ENNReal.ofReal_le_ofReal hbound
    have hmq : Measurable fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q := hXm.pow_const q
    have hnn : 0 ≤ᵐ[latticeBondLaw d p] fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q :=
      Eventually.of_forall fun ω => by positivity
    have hint : Integrable (fun ω => (|F 0 x ω - F 0 0 ω| / c) ^ q) (latticeBondLaw d p) := by
      refine ⟨hmq.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn]
      exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
    refine ⟨hint, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmq.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have h2 := IsOsBond.const_mul hc0 hX
  have heq : (fun ω => c * (|F 0 x ω - F 0 0 ω| / c)) = fun ω => |F 0 x ω - F 0 0 ω| := by
    funext ω
    field_simp
  rw [heq, mul_comm] at h2
  exact h2

/-- A finite sum of nonnegative variables of class `O_σ(θ)` is of class
`O_σ((2 · 4^{1/σ})^n max(θ, 3^{1/σ}))`, `n` the number of terms. -/
theorem isOsBond_sum [NeZero d] {p : unitInterval} {ι : Type*} (S : Finset ι)
    (Y : ι → Configuration d → ℝ) (hYm : ∀ i, Measurable (Y i)) (hY0 : ∀ i ω, 0 ≤ Y i ω)
    {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hY : ∀ i ∈ S, IsOsBond d p (Y i) σ θ) :
    IsOsBond d p (fun ω => ∑ i ∈ S, Y i ω) σ
      ((2 * 4 ^ (1 / σ)) ^ S.card * max θ (3 ^ (1 / σ))) := by
  classical
  have hM0 : 0 < max θ (3 ^ (1 / σ)) := lt_max_of_lt_left hθ
  have hb1 : (1 : ℝ) ≤ 2 * 4 ^ (1 / σ) := by
    have : (1 : ℝ) ≤ 4 ^ (1 / σ) := Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  induction S using Finset.induction_on with
  | empty =>
      have h1 := isOsBond_const (d := d) (p := p) one_pos hσ
      refine IsOsBond.mono_variable hσ (by positivity) measurable_const (fun ω => ?_)
        (IsOsBond.mono_scale hσ (by positivity) ?_ measurable_const h1)
      · simp
      · rw [Finset.card_empty, pow_zero, one_mul, one_mul]
        exact le_max_right _ _
  | insert a S ha ih =>
      have h₁ := ih fun i hi => hY i (Finset.mem_insert_of_mem hi)
      set cS := (2 * 4 ^ (1 / σ)) ^ S.card * max θ (3 ^ (1 / σ)) with hcS
      have hcS0 : 0 < cS := by positivity
      have hθc : θ ≤ cS := (le_max_left θ (3 ^ (1 / σ))).trans
        (le_mul_of_one_le_left hM0.le (one_le_pow₀ hb1))
      have hSm : Measurable fun ω => ∑ i ∈ S, Y i ω := Finset.measurable_sum _ fun i _ => hYm i
      have hmax := IsOsBond.max hσ hθ hcS0 (hYm a) hSm (hY a (Finset.mem_insert_self a S)) h₁
      rw [max_eq_right hθc] at hmax
      have h2 := IsOsBond.const_mul (two_pos) hmax
      have hconst : 2 * (cS * 4 ^ (1 / σ)) =
          (2 * 4 ^ (1 / σ)) ^ (insert a S).card * max θ (3 ^ (1 / σ)) := by
        rw [Finset.card_insert_of_notMem ha, pow_succ, hcS]
        ring
      rw [← hconst]
      refine IsOsBond.mono_variable hσ (by positivity) (Finset.measurable_sum _ fun i _ => hYm i)
        (fun ω => ?_) h2
      rw [Finset.sum_insert ha]
      have h0 : 0 ≤ ∑ i ∈ S, Y i ω := Finset.sum_nonneg fun i _ => hY0 i ω
      have := le_max_left (Y a ω) (∑ i ∈ S, Y i ω)
      have := le_max_right (Y a ω) (∑ i ∈ S, Y i ω)
      linarith

/-- The scale `0` is degenerate: `X ≤ O_s(0)` for every `X`, since `X/0 = 0`. -/
theorem isOsBond_zero_scale' [NeZero d] {p : unitInterval} (X : Configuration d → ℝ) {s : ℝ}
    (hs : 0 < s) : IsOsBond d p X s 0 := by
  have h1 : ∀ ω, Real.exp (Real.rpow (max (X ω / 0) 0) s) = 1 := by
    intro ω
    rw [div_zero, max_self]
    change Real.exp ((0 : ℝ) ^ s) = 1
    rw [Real.zero_rpow hs.ne', Real.exp_zero]
  unfold IsOsBond
  simp only [h1]
  exact ⟨integrable_const 1, by simp⟩

/-- **The coarsening error of Dario, Step 6 (5.10), for increments**, in dimension `d`: for every
slope `e_i` and points `x, y`, there is `E ≤ O_{s₆}(C₆)` such that for every corrected plane `ℓ` of
slope `e_i`, the corrector increment `χ(x) - χ(y)` differs from the field increment
`G i y 0 (x - y) - G i y 0 0` by at most `E`. -/
def CoarseningError [NeZero d] (p : unitInterval)
    (G : Fin d → Vertex d → Vertex d → Vertex d → Configuration d → ℝ) (s₆ C₆ : ℝ) : Prop :=
  ∀ (i : Fin d) (x y : Vertex d), ∃ E : Configuration d → ℝ, Measurable E ∧
    IsOsBond d p E s₆ C₆ ∧
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ ℓ : uniqueInfiniteComponent h → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
      ∀ (hx : x ∈ (uniqueInfiniteComponent h).supp) (hy : y ∈ (uniqueInfiniteComponent h).supp),
        |((ℓ ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * x j) -
            (ℓ ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * y j)) -
          (G i y 0 (x - y) ω - G i y 0 0 ω)| ≤ E ω

/-- **The coarsened corrector of Dario, §5, in dimension `d ≥ 3`**: for every base point `y` and
every coordinate slope `e_i`, fields `G i y` satisfying the hypotheses of Steps 1–4 with box
oscillations bounded uniformly in the scale (`LinftyIterationData` with the growth exponent `0`),
and the coarsening error of Step 6 (`CoarseningError`). It follows from the base hypotheses of §5
(`darioCoarsenedCorrectorThree_of_base`), which hold on the route of
`darioOptimalCorrectorThree_holds`. -/
def DarioCoarsenedCorrectorThree (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∃ A B k s₆ C₆ : ℝ, 0 < s₆ ∧ 0 < C₆ ∧
    ∃ G : Fin d → Vertex d → Vertex d → Vertex d → Configuration d → ℝ,
      (∀ i y, LinftyIterationData p (G i y) A B k 0) ∧ CoarseningError p G s₆ C₆

/-- **Dario's Theorem 1 in dimension `d ≥ 3`** (`DarioOptimalCorrectorThree`) from the coarsened
corrector data of §5 (`DarioCoarsenedCorrectorThree`: Theorem 2 at the box with a bound uniform in
the scale, the stationarity, the comparison of the translated partitions and the coarsening
error), with the linearity of the corrector in the slope from the qualitative corrector input. -/
theorem darioOptimalCorrectorThree_of_coarsened
    (hG : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → DarioCoarsenedCorrectorThree d p) : DarioOptimalCorrectorThree := by
  intro d _ hd3 p hpc hp1
  have hd : 2 ≤ d := by omega
  obtain ⟨A, B, k, s₆, C₆, hs₆, hC₆, G, hGD, hE⟩ := hG d hd3 p hpc hp1
  have hA : 0 ≤ A := (hGD 0 0).hA
  set s₅ : ℝ := 1 / (2 * (|k| + 1)) with hs₅def
  have hs₅ : 0 < s₅ := by positivity
  have hs₅k : s₅ * k < 1 := by
    have hk : k ≤ |k| := le_abs_self k
    rw [hs₅def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith [abs_nonneg k]
  obtain ⟨C₅, hC₅, h5⟩ := isOsBond_sub_of_linftyIterationData_zero (d := d) (p := p) (B := B) hA
    hs₅ hs₅k
  set s' := min s₆ s₅ with hs'def
  have hs' : 0 < s' := lt_min hs₆ hs₅
  set Θ : ℝ := 2 * (max (C₆ * 6 ^ (1 / s')) (C₅ * 6 ^ (1 / s')) * 4 ^ (1 / s')) with hΘ
  have hΘ0 : 0 < Θ := by positivity
  set Cf : ℝ := (2 * 4 ^ (1 / s')) ^ (Finset.univ : Finset (Fin d)).card * max Θ (3 ^ (1 / s'))
    with hCf
  have hCf0 : 0 < Cf := by positivity
  refine ⟨s', Cf, hs', hCf0, fun q x y => ?_⟩
  choose E hEm hEO hEae using fun i : Fin d => hE i x y
  set Gd : Fin d → Configuration d → ℝ := fun i ω => |G i y 0 (x - y) ω - G i y 0 0 ω| with hGd
  have hGdm : ∀ i, Measurable (Gd i) := fun i =>
    (((hGD i y).meas 0 (x - y)).sub ((hGD i y).meas 0 0)).abs
  set Y : Fin d → Configuration d → ℝ := fun i ω => 2 * max (E i ω) (Gd i ω) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => ((hEm i).max (hGdm i)).const_mul 2
  have hY0 : ∀ i ω, 0 ≤ Y i ω := fun i ω => by
    have : 0 ≤ Gd i ω := abs_nonneg _
    have := le_max_right (E i ω) (Gd i ω)
    simp only [hY]
    linarith
  have hYO : ∀ i, IsOsBond d p (Y i) s' Θ := by
    intro i
    have hE' := IsOsBond.mono_exponent hs' (min_le_left _ _) (hEm i) (hEO i)
    have hG' := IsOsBond.mono_exponent hs' (min_le_right _ _) (hGdm i) (h5 (G i y) (hGD i y) (x - y))
    have hmax := IsOsBond.max hs' (by positivity) (by positivity) (hEm i) (hGdm i) hE' hG'
    exact IsOsBond.const_mul (two_pos) hmax
  have hsum := isOsBond_sum (Finset.univ : Finset (Fin d)) Y hYm hY0 hs' hΘ0 fun i _ => hYO i
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨fun ω => Q * ∑ i, Y i ω, (Finset.measurable_sum _ fun i _ => hYm i).const_mul Q, ?_, ?_⟩
  · rcases hQ0.eq_or_lt with hQz | hQp
    · rw [← hQz, mul_zero]
      simp only [zero_mul]
      exact isOsBond_zero_scale' _ hs'
    · have := IsOsBond.const_mul hQp hsum
      convert this using 1
      ring
  · filter_upwards [ae_all_iff.2 hEae,
      Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds d hd p hpc hp1]
      with ω hEω hR2
    intro h ℓ hℓ hx hy
    choose L hL using fun i : Fin d => ((hR2 h).1 (Pi.single i 1) ⟨x, hx⟩).exists
    have hlin := corrector_sub_eq (hR2 h).1 hℓ (fun i => (hL i).1) ⟨x, hx⟩ ⟨y, hy⟩
    dsimp only at hlin
    have hi : ∀ i : Fin d,
        |(L i ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * x j) -
          (L i ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * y j)| ≤ Y i ω := by
      intro i
      have hb := hEω i h (L i) (hL i).1 hx hy
      have := abs_sub_abs_le_abs_sub ((L i ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j *
        x j) - (L i ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * y j))
        (G i y 0 (x - y) ω - G i y 0 0 ω)
      have h1 := le_max_left (E i ω) (Gd i ω)
      have h2 := le_max_right (E i ω) (Gd i ω)
      simp only [hY, hGd] at h1 h2 ⊢
      linarith
    change |(ℓ ⟨x, hx⟩ - ∑ i, q i * x i) - (ℓ ⟨y, hy⟩ - ∑ i, q i * y i)| ≤ Q * ∑ i, Y i ω
    rw [hlin]
    have hYle : ∀ i, Y i ω ≤ ∑ j, Y j ω := fun i =>
      Finset.single_le_sum (f := fun j => Y j ω) (fun j _ => hY0 j ω) (Finset.mem_univ i)
    calc _ ≤ ∑ i, |q i * ((L i ⟨x, hx⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * x j) -
            (L i ⟨y, hy⟩ - ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * y j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |q i| * ∑ j, Y j ω := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((hi i).trans (hYle i)) (abs_nonneg _)
      _ = Q * ∑ i, Y i ω := by rw [hQ, Finset.sum_mul]

end Rigidity.Corrector.GeneralDim
