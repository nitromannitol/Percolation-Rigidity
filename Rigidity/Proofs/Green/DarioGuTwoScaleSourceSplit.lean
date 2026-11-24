import Rigidity.Proofs.Green.DarioGuTwoScaleErrorFromSource

/-!
# The splitting of the source term in Steps 3-4 of Proposition 4.3 of Dario–Gu

The source term of the equation of `w` is `θ^{-1} (f - Σ_i (F_i(· - e_i) - F_i) - ξ)` with `f`, `F`
and `ξ` as in (4.26) (`twoScaleSource`). Testing against `ψ² v`, the divergence term is summed by
parts (`tsum_mul_sub_shift_eq`) and every term is estimated by Young's inequality, as in Step 2 of
the source (the inequality after (4.28)):

`θ^{-1} Σ_x ψ² v (f - D^* · F - ξ) ≤ E(ψ v) + (2s)^{-1} Σ_x (ψ v)² + (2θ^{-2} Q_f + 5θ^{-2} Q_F + Q_ξ) s^{α - 3}`

(`tsum_source_le_of_split`) once `Σ_x (ψ f)² ≤ Q_f s^{α - 4}` (Step 4 for `f`),
`Σ_x Σ_i (F_i(x) ψ(x + e_i))² ≤ Q_F s^{α - 3}` and `Σ_x Σ_i (F_i(x) D_i ψ(x))² ≤ Q_F s^{α - 4}`
(Step 4 for `F`), and `-θ^{-1} Σ_x ψ² v ξ ≤ E(ψ v)/4 + (8s)^{-1} Σ_x (ψ v)² + Q_ξ s^{α - 3}`
(Step 3, (4.32) after Young's inequality). Here `F` lives on the open edges.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- **Summation by parts on `ℤ²`**: `Σ_x φ(x) (G(x - e) - G(x)) = Σ_x G(x) (φ(x + e) - φ(x))`. -/
theorem tsum_mul_sub_shift_eq {φ G : Vertex 2 → ℝ} (hφ : Summable fun x => φ x ^ 2)
    (hG : Summable fun x => G x ^ 2) (e : Vertex 2) :
    ∑' x, φ x * (G (x - e) - G x) = ∑' x, G x * (φ (x + e) - φ x) := by
  have h1 : Summable fun x => φ x * G (x - e) :=
    summable_mul_of_sq hφ (summable_sq_sub_shift hG e)
  have h2 : Summable fun x => φ x * G x := summable_mul_of_sq hφ hG
  have h3 : Summable fun x => G x * φ (x + e) :=
    summable_mul_of_sq hG (summable_sq_add_shift hφ e)
  have h4 : Summable fun x => G x * φ x := summable_mul_of_sq hG hφ
  have hshift : ∑' x, φ x * G (x - e) = ∑' x, G x * φ (x + e) := by
    have := (Equiv.addRight e).tsum_eq (fun x => φ x * G (x - e))
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
    rw [← this]
    exact tsum_congr fun x => mul_comm _ _
  have e1 : ∑' x, φ x * (G (x - e) - G x) = ∑' x, φ x * G (x - e) - ∑' x, φ x * G x := by
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun x => by ring
  have e2 : ∑' x, G x * (φ (x + e) - φ x) = ∑' x, G x * φ (x + e) - ∑' x, G x * φ x := by
    rw [← h3.tsum_sub h4]
    exact tsum_congr fun x => by ring
  rw [e1, e2, hshift]
  congr 1
  exact tsum_congr fun x => mul_comm _ _

theorem openCond_sq (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) :
    openCond ω i x ^ 2 = openCond ω i x := by
  unfold openCond
  split_ifs <;> norm_num

/-- **The splitting of the source term with Young's inequality.** -/
theorem tsum_source_le_of_split (ω : Configuration 2) {θ s α B Qf QF Qξ : ℝ}
    {ψ v f ξ : Vertex 2 → ℝ} {F : Fin 2 → Vertex 2 → ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hψ : ∀ x, |ψ x| ≤ B) (hv : Summable fun x => v x ^ 2)
    (hfs : Summable fun x => (ψ x * f x) ^ 2) (hfb : ∑' x, (ψ x * f x) ^ 2 ≤ Qf * s ^ (α - 4))
    (hFs : ∀ i, Summable fun x => F i x ^ 2)
    (hFo : ∀ i x, F i x = openCond ω i x * F i x)
    (hFb : ∑' x, ∑ i : Fin 2, (F i x * ψ (x + unit i)) ^ 2 ≤ QF * s ^ (α - 3))
    (hFb' : ∑' x, ∑ i : Fin 2, (F i x * (ψ (x + unit i) - ψ x)) ^ 2 ≤ QF * s ^ (α - 4))
    (hξs : Summable fun x => ψ x ^ 2 * v x * ξ x)
    (hξ : -(θ⁻¹ * ∑' x, ψ x ^ 2 * v x * ξ x) ≤ openEnergy ω (fun x => ψ x * v x) / 4 +
      1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 + Qξ * s ^ (α - 3)) :
    θ⁻¹ * ∑' x, ψ x ^ 2 * v x * (f x - ∑ i : Fin 2, (F i (x - unit i) - F i x) - ξ x) ≤
      openEnergy ω (fun x => ψ x * v x) + 1 / (2 * s) * ∑' x, (ψ x * v x) ^ 2 +
        (2 * θ⁻¹ ^ 2 * Qf + 5 * θ⁻¹ ^ 2 * QF + Qξ) * s ^ (α - 3) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hψ 0)
  have hψ2 : ∀ x, |ψ x ^ 2| ≤ B ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψ x) 2
  have hψv : Summable fun x => (ψ x * v x) ^ 2 := summable_sq_mul_of_abs_le hψ hv
  have hφ : Summable fun x => (ψ x ^ 2 * v x) ^ 2 := summable_sq_mul_of_abs_le hψ2 hv
  set φ : Vertex 2 → ℝ := fun x => ψ x ^ 2 * v x with hφdef
  have hfv : Summable fun x => ψ x ^ 2 * v x * f x :=
    (summable_mul_of_sq hψv hfs).congr fun x => by ring
  have hdiv : ∀ i : Fin 2, Summable fun x => φ x * (F i (x - unit i) - F i x) :=
    fun i => summable_mul_of_sq hφ (summable_sq_sub (summable_sq_sub_shift (hFs i) _) (hFs i))
  have hdivs : Summable fun x => ∑ i : Fin 2, φ x * (F i (x - unit i) - F i x) :=
    summable_sum fun i _ => hdiv i
  -- the three parts
  have hsplit : ∑' x, ψ x ^ 2 * v x * (f x - ∑ i : Fin 2, (F i (x - unit i) - F i x) - ξ x) =
      ∑' x, ψ x ^ 2 * v x * f x - ∑ i : Fin 2, ∑' x, φ x * (F i (x - unit i) - F i x) -
        ∑' x, ψ x ^ 2 * v x * ξ x := by
    rw [← Summable.tsum_finsetSum fun i _ => hdiv i, ← hfv.tsum_sub hdivs,
      ← (hfv.sub hdivs).tsum_sub hξs]
    refine tsum_congr fun x => ?_
    simp only [hφdef]
    rw [← Finset.mul_sum]
    ring
  -- the `f` part by Young's inequality
  have key : ∀ x, θ⁻¹ * (ψ x ^ 2 * v x * f x) ≤
      1 / (8 * s) * (ψ x * v x) ^ 2 + 2 * s * θ⁻¹ ^ 2 * (ψ x * f x) ^ 2 := by
    intro x
    have hsq := sq_nonneg (ψ x * v x / (4 * s) - θ⁻¹ * (ψ x * f x))
    have e : 1 / (8 * s) * (ψ x * v x) ^ 2 + 2 * s * θ⁻¹ ^ 2 * (ψ x * f x) ^ 2 -
        θ⁻¹ * (ψ x ^ 2 * v x * f x) = 2 * s * (ψ x * v x / (4 * s) - θ⁻¹ * (ψ x * f x)) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hs.le hsq]
  have hfpart : θ⁻¹ * ∑' x, ψ x ^ 2 * v x * f x ≤
      1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 + 2 * s * θ⁻¹ ^ 2 * ∑' x, (ψ x * f x) ^ 2 := by
    have hA := hψv.mul_left (1 / (8 * s))
    have hB' := hfs.mul_left (2 * s * θ⁻¹ ^ 2)
    calc θ⁻¹ * ∑' x, ψ x ^ 2 * v x * f x = ∑' x, θ⁻¹ * (ψ x ^ 2 * v x * f x) :=
          tsum_mul_left.symm
      _ ≤ ∑' x, (1 / (8 * s) * (ψ x * v x) ^ 2 + 2 * s * θ⁻¹ ^ 2 * (ψ x * f x) ^ 2) :=
          Summable.tsum_le_tsum key (hfv.mul_left _) (hA.add hB')
      _ = 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 + 2 * s * θ⁻¹ ^ 2 * ∑' x, (ψ x * f x) ^ 2 := by
          rw [hA.tsum_add hB', tsum_mul_left, tsum_mul_left]
  -- the divergence part, summed by parts
  have hFpart : -(θ⁻¹ * ∑ i : Fin 2, ∑' x, φ x * (F i (x - unit i) - F i x)) ≤
      openEnergy ω (fun x => ψ x * v x) / 4 + 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 +
        θ⁻¹ ^ 2 * ∑' x, ∑ i : Fin 2, (F i x * ψ (x + unit i)) ^ 2 +
        4 * s * θ⁻¹ ^ 2 * ∑' x, ∑ i : Fin 2, (F i x * (ψ (x + unit i) - ψ x)) ^ 2 := by
    have hparts : ∀ i : Fin 2, ∑' x, φ x * (F i (x - unit i) - F i x) =
        ∑' x, F i x * (φ (x + unit i) - φ x) := fun i => tsum_mul_sub_shift_eq hφ (hFs i) _
    simp only [hparts]
    have hFψ : ∀ i : Fin 2, Summable fun x => (F i x * ψ (x + unit i)) ^ 2 := fun i =>
      (summable_sq_mul_of_abs_le (fun x => hψ (x + unit i)) (hFs i)).congr fun x => by ring
    have hFdψ : ∀ i : Fin 2, Summable fun x => (F i x * (ψ (x + unit i) - ψ x)) ^ 2 := by
      intro i
      have hb : ∀ x, |ψ (x + unit i) - ψ x| ≤ 2 * B := fun x => by
        have := abs_sub (ψ (x + unit i)) (ψ x)
        linarith [hψ (x + unit i), hψ x]
      exact (summable_sq_mul_of_abs_le hb (hFs i)).congr fun x => by ring
    have hE : ∀ i : Fin 2, Summable fun x =>
        openCond ω i x * (ψ (x + unit i) * v (x + unit i) - ψ x * v x) ^ 2 := fun i =>
      Summable.of_nonneg_of_le (fun x => mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _))
        (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i x))
        (summable_sq_sub (summable_sq_add_shift hψv (unit i)) hψv)
    have hFφ : ∀ i : Fin 2, Summable fun x => F i x * (φ (x + unit i) - φ x) := fun i =>
      summable_mul_of_sq (hFs i) (summable_sq_sub (summable_sq_add_shift hφ _) hφ)
    -- pointwise Young
    have hpt : ∀ (i : Fin 2) (x : Vertex 2), -(θ⁻¹ * (F i x * (φ (x + unit i) - φ x))) ≤
        openCond ω i x * (ψ (x + unit i) * v (x + unit i) - ψ x * v x) ^ 2 / 4 +
          1 / (16 * s) * (ψ x * v x) ^ 2 + θ⁻¹ ^ 2 * (F i x * ψ (x + unit i)) ^ 2 +
          4 * s * θ⁻¹ ^ 2 * (F i x * (ψ (x + unit i) - ψ x)) ^ 2 := by
      intro i x
      set a := openCond ω i x
      set D := ψ (x + unit i) * v (x + unit i) - ψ x * v x
      set u := ψ x * v x
      set g := F i x
      set p' := ψ (x + unit i)
      set dp := ψ (x + unit i) - ψ x
      have hg : g = a * g := hFo i x
      have ha2 : a ^ 2 = a := openCond_sq ω i x
      have hprod : φ (x + unit i) - φ x = p' * D + u * dp := by
        simp only [hφdef, p', D, u, dp]
        ring
      rw [hprod]
      have y1 : -(θ⁻¹ * (g * (p' * D))) ≤ a * D ^ 2 / 4 + θ⁻¹ ^ 2 * (g * p') ^ 2 := by
        have : θ⁻¹ * (g * (p' * D)) = (θ⁻¹ * g * p') * (a * D) := by
          calc θ⁻¹ * (g * (p' * D)) = θ⁻¹ * ((a * g) * (p' * D)) := by rw [← hg]
            _ = (θ⁻¹ * g * p') * (a * D) := by ring
        rw [this]
        have hsq := sq_nonneg (a * D / 2 + θ⁻¹ * g * p')
        have e : (a * D) ^ 2 = a * D ^ 2 := by rw [mul_pow, ha2]
        nlinarith
      have y2 : -(θ⁻¹ * (g * (u * dp))) ≤ 1 / (16 * s) * u ^ 2 +
          4 * s * θ⁻¹ ^ 2 * (g * dp) ^ 2 := by
        have hsq := sq_nonneg (u / (8 * s) + θ⁻¹ * (g * dp))
        have e : 1 / (16 * s) * u ^ 2 + 4 * s * θ⁻¹ ^ 2 * (g * dp) ^ 2 +
            θ⁻¹ * (g * (u * dp)) = 4 * s * (u / (8 * s) + θ⁻¹ * (g * dp)) ^ 2 := by
          field_simp
          ring
        nlinarith [mul_nonneg hs.le hsq]
      have e3 : -(θ⁻¹ * (g * (p' * D + u * dp))) =
          -(θ⁻¹ * (g * (p' * D))) + -(θ⁻¹ * (g * (u * dp))) := by ring
      rw [e3]
      linarith
    -- sum over `x` and `i`
    have hsum : ∀ i : Fin 2, -(θ⁻¹ * ∑' x, F i x * (φ (x + unit i) - φ x)) ≤
        (∑' x, openCond ω i x * (ψ (x + unit i) * v (x + unit i) - ψ x * v x) ^ 2) / 4 +
          1 / (16 * s) * ∑' x, (ψ x * v x) ^ 2 + θ⁻¹ ^ 2 * ∑' x, (F i x * ψ (x + unit i)) ^ 2 +
          4 * s * θ⁻¹ ^ 2 * ∑' x, (F i x * (ψ (x + unit i) - ψ x)) ^ 2 := by
      intro i
      have h1 := (hE i).div_const 4
      have h2 := hψv.mul_left (1 / (16 * s))
      have h3 := (hFψ i).mul_left (θ⁻¹ ^ 2)
      have h4 := (hFdψ i).mul_left (4 * s * θ⁻¹ ^ 2)
      calc -(θ⁻¹ * ∑' x, F i x * (φ (x + unit i) - φ x))
          = ∑' x, -(θ⁻¹ * (F i x * (φ (x + unit i) - φ x))) := by
            rw [tsum_neg, tsum_mul_left]
        _ ≤ ∑' x, (openCond ω i x * (ψ (x + unit i) * v (x + unit i) - ψ x * v x) ^ 2 / 4 +
              1 / (16 * s) * (ψ x * v x) ^ 2 + θ⁻¹ ^ 2 * (F i x * ψ (x + unit i)) ^ 2 +
              4 * s * θ⁻¹ ^ 2 * (F i x * (ψ (x + unit i) - ψ x)) ^ 2) :=
            Summable.tsum_le_tsum (hpt i) ((hFφ i).mul_left _).neg (((h1.add h2).add h3).add h4)
        _ = _ := by
            rw [((h1.add h2).add h3).tsum_add h4, (h1.add h2).tsum_add h3, h1.tsum_add h2,
              tsum_div_const, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    have hEn : openEnergy ω (fun x => ψ x * v x) =
        ∑' x, openCond ω 0 x * (ψ (x + unit 0) * v (x + unit 0) - ψ x * v x) ^ 2 +
          ∑' x, openCond ω 1 x * (ψ (x + unit 1) * v (x + unit 1) - ψ x * v x) ^ 2 := by
      unfold openEnergy
      rw [← (hE 0).tsum_add (hE 1)]
      exact tsum_congr fun x => by rw [Fin.sum_univ_two]
    have hF1 : ∑' x, ∑ i : Fin 2, (F i x * ψ (x + unit i)) ^ 2 =
        ∑' x, (F 0 x * ψ (x + unit 0)) ^ 2 + ∑' x, (F 1 x * ψ (x + unit 1)) ^ 2 := by
      rw [← (hFψ 0).tsum_add (hFψ 1)]
      exact tsum_congr fun x => by rw [Fin.sum_univ_two]
    have hF2 : ∑' x, ∑ i : Fin 2, (F i x * (ψ (x + unit i) - ψ x)) ^ 2 =
        ∑' x, (F 0 x * (ψ (x + unit 0) - ψ x)) ^ 2 +
          ∑' x, (F 1 x * (ψ (x + unit 1) - ψ x)) ^ 2 := by
      rw [← (hFdψ 0).tsum_add (hFdψ 1)]
      exact tsum_congr fun x => by rw [Fin.sum_univ_two]
    rw [Fin.sum_univ_two, hEn, hF1, hF2]
    have s0 := hsum 0
    have s1 := hsum 1
    have e : -(θ⁻¹ * (∑' x, F 0 x * (φ (x + unit 0) - φ x) +
        ∑' x, F 1 x * (φ (x + unit 1) - φ x))) =
        -(θ⁻¹ * ∑' x, F 0 x * (φ (x + unit 0) - φ x)) +
          -(θ⁻¹ * ∑' x, F 1 x * (φ (x + unit 1) - φ x)) := by ring
    rw [e]
    have h16 : 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 =
        1 / (16 * s) * ∑' x, (ψ x * v x) ^ 2 + 1 / (16 * s) * ∑' x, (ψ x * v x) ^ 2 := by ring
    linarith
  -- assembly
  rw [hsplit]
  have hE0 : 0 ≤ openEnergy ω (fun x => ψ x * v x) :=
    tsum_nonneg fun x => Finset.sum_nonneg fun i _ =>
      mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _)
  have hV0 : 0 ≤ ∑' x, (ψ x * v x) ^ 2 := tsum_nonneg fun x => sq_nonneg _
  have hθ2 : 0 ≤ θ⁻¹ ^ 2 := sq_nonneg _
  have hs4 : s * s ^ (α - 4) = s ^ (α - 3) := by
    rw [show α - 3 = (α - 4) + 1 by ring, Real.rpow_add_one hs.ne']
    ring
  have k1 : 2 * s * θ⁻¹ ^ 2 * ∑' x, (ψ x * f x) ^ 2 ≤ 2 * θ⁻¹ ^ 2 * Qf * s ^ (α - 3) := by
    have := mul_le_mul_of_nonneg_left hfb (by positivity : 0 ≤ 2 * s * θ⁻¹ ^ 2)
    rw [← hs4]
    linarith
  have k2 : θ⁻¹ ^ 2 * ∑' x, ∑ i : Fin 2, (F i x * ψ (x + unit i)) ^ 2 ≤
      θ⁻¹ ^ 2 * QF * s ^ (α - 3) := by
    have := mul_le_mul_of_nonneg_left hFb hθ2
    linarith
  have k3 : 4 * s * θ⁻¹ ^ 2 * ∑' x, ∑ i : Fin 2, (F i x * (ψ (x + unit i) - ψ x)) ^ 2 ≤
      4 * θ⁻¹ ^ 2 * QF * s ^ (α - 3) := by
    have := mul_le_mul_of_nonneg_left hFb' (by positivity : 0 ≤ 4 * s * θ⁻¹ ^ 2)
    rw [← hs4]
    linarith
  have hcV : 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 + 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 +
      1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 ≤ 1 / (2 * s) * ∑' x, (ψ x * v x) ^ 2 := by
    have h1 : 1 / (2 * s) * ∑' x, (ψ x * v x) ^ 2 = 4 * (1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2) := by
      ring
    have h2 : 0 ≤ 1 / (8 * s) * ∑' x, (ψ x * v x) ^ 2 := by positivity
    linarith
  have e : θ⁻¹ * (∑' x, ψ x ^ 2 * v x * f x - ∑ i : Fin 2, ∑' x, φ x * (F i (x - unit i) - F i x) -
      ∑' x, ψ x ^ 2 * v x * ξ x) = θ⁻¹ * ∑' x, ψ x ^ 2 * v x * f x +
        -(θ⁻¹ * ∑ i : Fin 2, ∑' x, φ x * (F i (x - unit i) - F i x)) +
        -(θ⁻¹ * ∑' x, ψ x ^ 2 * v x * ξ x) := by ring
  rw [e]
  nlinarith [hfpart, hFpart, hξ, k1, k2, k3, hcV, hE0]

end Rigidity.Green
