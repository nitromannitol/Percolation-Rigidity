import Rigidity.Proofs.Green.GeneralTwoScaleFluxBound

/-!
# The estimate of the source term of Proposition 4.3 of Dario–Gu on `ℤ^d`

Steps 3-4 of the proof of Proposition 4.3 of Dario–Gu (lines 2333-2446 of the source) with the
weight `ψ = 1`, on `ℤ^d`, `d ≥ 2`. The source term of the equation of `w` on the cluster splits as
`θ^{-1} (f - Σ_i (F_i(· - e_i) - F_i) - ξ)` with `f = 1_𝒞 fpartD` (`clusterFD`),
`F_i = 1_𝒞 stepOneFD` (`clusterFluxD`) and `ξ = 1_𝒞 Σ_{k,i} g̃_{k,i} D_i D_k p̄` (`clusterXiD`)
(`clusterSourceD_eq_split`). If on the cluster the corrector grows like
`|χ_k(x)| ≤ B (√r + |x - y| + 2)^α` (Proposition 2.12) and the weak norms of the centered flux on
the dyadic balls are at most `C_f ρ^α` (Proposition 2.13), then for every square summable `v`
vanishing off the cluster

`Σ_x v G(r) ≤ E(v) + (2r)^{-1} Σ_x v² + Q r^{α - d/2 - 2}`

(`tsum_clusterSourceD_le`), with `Q` depending only on `d, σ, θ, B, C_f, α`. The sums of the squares
of `f` and `F` (Step 4) are bounded by `summable_tsum_sq_le_growth`:
`Σ_x g² ≤ L² C r^{β + d/2}` when `|g(x)| ≤ L (√r + |x - y| + 2)^β exp(-|x - y|²/(32σr))`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-! ### Gaussian sums with the growth of the corrector -/

/-- The constant of `sq_add_mul_exp_le` at `a = 3`, `c = 16σ`. -/
noncomputable def growthFactor (σ : ℝ) : ℝ :=
  2 * 3 ^ 2 + 2 * (Real.sqrt (16 * σ) * Real.sqrt (2 * (16 * σ)))

/-- The constant of `summable_tsum_sq_le_growth`. -/
noncomputable def growthConstD (d : ℕ) (σ : ℝ) : ℝ :=
  growthFactor σ * ((Real.pi * (64 * σ)) ^ ((d : ℝ) / 2) * gaussMassBoundD d (64 * σ / 2))

theorem growthConstD_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ growthConstD d σ := by
  unfold growthConstD growthFactor gaussMassBoundD
  have : 0 ≤ ∑' n : ℤ, Real.exp (-(2 * Real.pi ^ 2 * (64 * σ / 2)) * (n : ℝ) ^ 2) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  positivity

theorem sq_rpow_half {s β : ℝ} (hs : 0 < s) : (s ^ (β / 2)) ^ 2 = s ^ β := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  congr 1
  push_cast
  ring

/-- **Gaussian sums with polynomial growth**: if
`|g(x)| ≤ L (√s + |x - y| + 2)^β exp(-|x - y|²/(32σs))` with `0 ≤ β ≤ 1` and `s ≥ 1`, then `g` is
square summable and `Σ_x g² ≤ L² C s^{β + d/2}`. -/
theorem summable_tsum_sq_le_growth {σ s β L : ℝ} (hσ : 0 < σ) (hs : 1 ≤ s) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) {g : Vertex d → ℝ} {y : Vertex d}
    (hg : ∀ x, |g x| ≤ L * ((Real.sqrt s + ‖edzD x y‖ + 2) ^ β *
      Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * s))))) :
    Summable (fun x => g x ^ 2) ∧
      ∑' x, g x ^ 2 ≤ L ^ 2 * growthConstD d σ * s ^ (β + (d : ℝ) / 2) := by
  have hs0 : 0 < s := by linarith
  have hsr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsr1 : 1 ≤ Real.sqrt s := Real.one_le_sqrt.2 hs
  have hpt : ∀ x, g x ^ 2 ≤ L ^ 2 * s ^ β * growthFactor σ *
      Real.exp (-(‖edzD x y‖ ^ 2 / (64 * σ * s))) := by
    intro x
    set v := ‖edzD x y‖ with hv
    have hv0 : 0 ≤ v := norm_nonneg _
    set w := v / Real.sqrt s with hw
    have hw0 : 0 ≤ w := by positivity
    have hvw : v = Real.sqrt s * w := by rw [hw]; field_simp
    have h1 : Real.sqrt s + v + 2 ≤ Real.sqrt s * (3 + w) := by rw [hvw]; nlinarith
    have h2 : (Real.sqrt s + v + 2) ^ β ≤ s ^ (β / 2) * (3 + w) := by
      calc (Real.sqrt s + v + 2) ^ β ≤ (Real.sqrt s * (3 + w)) ^ β :=
            Real.rpow_le_rpow (by positivity) h1 hβ0
        _ = Real.sqrt s ^ β * (3 + w) ^ β := Real.mul_rpow hsr.le (by positivity)
        _ ≤ Real.sqrt s ^ β * (3 + w) ^ (1 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1) (by positivity)
        _ = s ^ (β / 2) * (3 + w) := by
            rw [Real.rpow_one, Real.sqrt_eq_rpow, ← Real.rpow_mul hs0.le]
            ring_nf
    have hww : w ^ 2 = v ^ 2 / s := by rw [hw, div_pow, Real.sq_sqrt hs0.le]
    have h3 : Real.exp (-(v ^ 2 / (32 * σ * s))) ^ 2 = Real.exp (-(w ^ 2 / (16 * σ))) := by
      rw [← Real.exp_nat_mul, hww]
      congr 1
      push_cast
      ring
    have h4 := sq_add_mul_exp_le (a := 3) hw0 (by positivity : 0 < 16 * σ)
    have h5 : Real.exp (-(w ^ 2 / (4 * (16 * σ)))) = Real.exp (-(v ^ 2 / (64 * σ * s))) := by
      rw [hww]
      congr 1
      ring
    have hgsq := sq_le_sq_of_abs_leD (hg x)
    have hG0 : 0 ≤ (Real.sqrt s + v + 2) ^ β := by positivity
    have hE0 := Real.exp_pos (-(w ^ 2 / (16 * σ)))
    calc g x ^ 2 ≤ (L * ((Real.sqrt s + v + 2) ^ β * Real.exp (-(v ^ 2 / (32 * σ * s))))) ^ 2 :=
          hgsq
      _ = L ^ 2 * ((Real.sqrt s + v + 2) ^ β) ^ 2 * Real.exp (-(v ^ 2 / (32 * σ * s))) ^ 2 := by
          ring
      _ = L ^ 2 * ((Real.sqrt s + v + 2) ^ β) ^ 2 * Real.exp (-(w ^ 2 / (16 * σ))) := by rw [h3]
      _ ≤ L ^ 2 * (s ^ (β / 2) * (3 + w)) ^ 2 * Real.exp (-(w ^ 2 / (16 * σ))) := by
          gcongr
      _ = L ^ 2 * s ^ β * ((3 + w) ^ 2 * Real.exp (-(w ^ 2 / (16 * σ)))) := by
          rw [mul_pow, sq_rpow_half hs0]
          ring
      _ ≤ L ^ 2 * s ^ β * (growthFactor σ * Real.exp (-(w ^ 2 / (4 * (16 * σ))))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = L ^ 2 * s ^ β * growthFactor σ * Real.exp (-(v ^ 2 / (64 * σ * s))) := by
          rw [h5]
          ring
  have hsum : Summable fun x => L ^ 2 * s ^ β * growthFactor σ *
      Real.exp (-(‖edzD x y‖ ^ 2 / (64 * σ * s))) :=
    (summable_exp_neg_sq_edzD (c := 64 * σ * s) (by positivity) y).mul_left _
  have hgs : Summable fun x => g x ^ 2 := Summable.of_nonneg_of_le (fun x => sq_nonneg _) hpt hsum
  refine ⟨hgs, ?_⟩
  have hgf : 0 ≤ growthFactor σ := by unfold growthFactor; positivity
  have hT := tsum_exp_neg_sq_edzD_le (d := d) (c := 64 * σ) (r := s) (by positivity) hs y
  calc ∑' x, g x ^ 2
      ≤ ∑' x, L ^ 2 * s ^ β * growthFactor σ * Real.exp (-(‖edzD x y‖ ^ 2 / (64 * σ * s))) :=
        Summable.tsum_le_tsum hpt hgs hsum
    _ = L ^ 2 * s ^ β * growthFactor σ *
          ∑' x, Real.exp (-(‖edzD x y‖ ^ 2 / (64 * σ * s))) := tsum_mul_left
    _ ≤ L ^ 2 * s ^ β * growthFactor σ * ((Real.pi * (64 * σ)) ^ ((d : ℝ) / 2) *
          gaussMassBoundD d (64 * σ / 2) * s ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by
        rw [Real.rpow_add hs0]
        unfold growthConstD
        ring

/-- `(r^{-d/2} / √r^j)² r^{β + d/2} = r^{β - d/2 - j}`. -/
theorem scale_sq_mul {r β : ℝ} (hr : 0 < r) (j : ℕ) :
    (r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ j) ^ 2 * r ^ (β + (d : ℝ) / 2) =
      r ^ (β - (d : ℝ) / 2 - j) := by
  have e1 : (r ^ (-((d : ℝ) / 2))) ^ 2 = r ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have e2 : (Real.sqrt r ^ j) ^ 2 = r ^ (j : ℝ) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hr.le, Real.rpow_natCast]
  rw [div_pow, e1, e2, div_mul_eq_mul_div, ← Real.rpow_add hr, ← Real.rpow_sub hr]
  congr 1
  ring

theorem mul_sqrt_eq_pow (r : ℝ) (hr : 0 ≤ r) : r * Real.sqrt r = Real.sqrt r ^ 3 := by
  rw [pow_succ, Real.sq_sqrt hr]

theorem self_eq_sqrt_pow (r : ℝ) (hr : 0 ≤ r) : r = Real.sqrt r ^ 2 := (Real.sq_sqrt hr).symm

/-! ### The terms `f`, `F` and `ξ` -/

/-- The term `f = (∂_r P - (σ/2) Σ_k D_k D_k P) + Σ_k D_k ∂_r P χ_k` of (4.26). -/
noncomputable def fpartD (σ : ℝ) (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y x : Vertex d) : ℝ :=
  (latticeGaussianTimeDerivD σ r x y -
      σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ r z y) x) +
    ∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ r z y) x * χ k x

/-- `1_𝒞 f`. -/
noncomputable def clusterFD {ω : Configuration d} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y x : Vertex d) : ℝ :=
  if x ∈ K.supp then fpartD σ χ r y x else 0

/-- `1_𝒞 F_i`. -/
noncomputable def clusterFluxD {ω : Configuration d} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y : Vertex d) (i : Fin d) (x : Vertex d) : ℝ :=
  if x ∈ K.supp then stepOneFD ω χ (fun z => latticeGaussianD σ r z y) i x else 0

/-- `1_𝒞 ξ` with `ξ = Σ_{k,i} g̃_{k,i} D_i D_k P`. -/
noncomputable def clusterXiD {ω : Configuration d} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y x : Vertex d) : ℝ :=
  if x ∈ K.supp then ∑ k, ∑ i, centeredFluxD ω σ χ k i x *
    fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x else 0

theorem stepOneFD_eq_zero_of_not_adj (ω : Configuration d) (χ : Fin d → Vertex d → ℝ)
    (P : Vertex d → ℝ) (i : Fin d) {z : Vertex d} (h : ¬ (openGraph ω).Adj z (z + Pi.single i 1)) :
    stepOneFD ω χ P i z = 0 := by
  unfold stepOneFD openCondD
  rw [if_neg h, zero_mul]

/-- `1_𝒞 F_i(x - e_i) = 1_𝒞(x) F_i(x - e_i)`: an open edge does not leave the cluster. -/
theorem clusterFluxD_sub_eq {ω : Configuration d} (K : OpenComponent ω) (σ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y : Vertex d) (i : Fin d) (x : Vertex d) :
    clusterFluxD K σ χ r y i (x - Pi.single i 1) =
      if x ∈ K.supp then stepOneFD ω χ (fun z => latticeGaussianD σ r z y) i (x - Pi.single i 1)
        else 0 := by
  unfold clusterFluxD
  by_cases hadj : (openGraph ω).Adj (x - Pi.single i 1) (x - Pi.single i 1 + Pi.single i 1)
  · rw [sub_add_cancel] at hadj
    have hiff : x - Pi.single i 1 ∈ K.supp ↔ x ∈ K.supp :=
      ⟨fun h => mem_supp_of_openAdjD h hadj, fun h => mem_supp_of_openAdjD h hadj.symm⟩
    by_cases hx : x ∈ K.supp
    · rw [if_pos (hiff.2 hx), if_pos hx]
    · rw [if_neg (fun h => hx (hiff.1 h)), if_neg hx]
  · rw [stepOneFD_eq_zero_of_not_adj ω χ _ i hadj]
    split_ifs <;> rfl

/-- **The splitting of the source term.** -/
theorem clusterSourceD_eq_split {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (r : ℝ) (y x : Vertex d) :
    clusterSourceD K σ θ χ y r x = θ⁻¹ * (clusterFD K σ χ r y x -
      ∑ i, (clusterFluxD K σ χ r y i (x - Pi.single i 1) - clusterFluxD K σ χ r y i x) -
      clusterXiD K σ χ r y x) := by
  simp only [clusterFluxD_sub_eq]
  unfold clusterSourceD clusterFD clusterXiD clusterFluxD twoScaleSourceD fpartD
  split_ifs with hx
  · ring
  · simp

/-! ### The growth of the corrector and Step 4 -/

theorem one_le_growth {r β v : ℝ} (hβ : 0 ≤ β) (hv : 0 ≤ v) :
    1 ≤ (Real.sqrt r + v + 2) ^ β :=
  Real.one_le_rpow (by have := Real.sqrt_nonneg r; linarith) hβ

theorem one_add_sum_abs_le {χ : Fin d → Vertex d → ℝ} {x : Vertex d} {B G : ℝ}
    (hG : 1 ≤ G) (hχ : ∀ k, |χ k x| ≤ B * G) :
    1 + ∑ k, |χ k x| ≤ (1 + d * B) * G := by
  have h : ∑ k, |χ k x| ≤ d * (B * G) := by
    calc ∑ k, |χ k x| ≤ ∑ _k : Fin d, B * G := Finset.sum_le_sum fun k _ => hχ k
      _ = d * (B * G) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- **Step 4 for `f`**: `Σ_x f² ≤ Q r^{β - d/2 - 3}`. -/
theorem summable_tsum_sq_clusterFD_le {ω : Configuration d} (K : OpenComponent ω) {σ r β B : ℝ}
    (hσ : 0 < σ) (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hB : 0 ≤ B)
    {χ : Fin d → Vertex d → ℝ} {y : Vertex d}
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ B * (Real.sqrt r + ‖edzD x y‖ + 2) ^ β) :
    Summable (fun x => clusterFD K σ χ r y x ^ 2) ∧
      ∑' x, clusterFD K σ χ r y x ^ 2 ≤
        (σ / 2 * d * gaussConstD d σ 3 * (1 + d * B)) ^ 2 * growthConstD d σ *
          r ^ (β - (d : ℝ) / 2 - 3) := by
  have hr0 : 0 < r := by linarith
  set c₃ := σ / 2 * d * gaussConstD d σ 3 with hc₃
  have hc₃0 : 0 ≤ c₃ := by have := gaussConstD_pos (d := d) hσ 3; positivity
  set L := c₃ * (1 + d * B) * (r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 3) with hL
  have hbd : ∀ x, |clusterFD K σ χ r y x| ≤ L * ((Real.sqrt r + ‖edzD x y‖ + 2) ^ β *
      Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
    intro x
    unfold clusterFD
    split_ifs with hx
    · set G := (Real.sqrt r + ‖edzD x y‖ + 2) ^ β with hG
      have hG1 : 1 ≤ G := one_le_growth hβ0 (norm_nonneg _)
      set E := Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) with hE
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      set R := r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 3 with hR
      have hR0 : 0 ≤ R := by positivity
      have h1 := abs_timeDeriv_sub_secondDiffD_le hσ hr x y
      have h2 := fun k => abs_fwdDiffD_latticeGaussianTimeDerivD_le hσ hr k x y
      rw [mul_sqrt_eq_pow r hr0.le] at h1
      simp only [mul_sqrt_eq_pow r hr0.le] at h2
      have h1' : |latticeGaussianTimeDerivD σ r x y -
          σ / 2 * ∑ k, fwdDiffD k (fwdDiffD k fun z => latticeGaussianD σ r z y) x| ≤
          c₃ * R * E := by
        rw [hc₃, hR, hE]
        refine h1.trans (le_of_eq ?_)
        ring
      have h2' : ∀ k, |fwdDiffD k (fun z => latticeGaussianTimeDerivD σ r z y) x| ≤
          c₃ * R * E := fun k => by
        rw [hc₃, hR, hE]
        refine (h2 k).trans (le_of_eq ?_)
        ring
      have hsum : |∑ k, fwdDiffD k (fun z => latticeGaussianTimeDerivD σ r z y) x * χ k x| ≤
          c₃ * R * E * ∑ k, |χ k x| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (h2' k) (abs_nonneg _)
      have hχ' := one_add_sum_abs_le hG1 (hχ x hx)
      have hCRE : 0 ≤ c₃ * R * E := by positivity
      unfold fpartD
      calc _ ≤ c₃ * R * E + c₃ * R * E * ∑ k, |χ k x| := (abs_add_le _ _).trans
            (add_le_add h1' hsum)
        _ = c₃ * R * E * (1 + ∑ k, |χ k x|) := by ring
        _ ≤ c₃ * R * E * ((1 + d * B) * G) := mul_le_mul_of_nonneg_left hχ' hCRE
        _ = L * (G * E) := by rw [hL]; ring
    · rw [abs_zero]
      have : 0 ≤ L := by rw [hL]; positivity
      positivity
  obtain ⟨hs, ht⟩ := summable_tsum_sq_le_growth hσ hr hβ0 hβ1 hbd
  refine ⟨hs, ht.trans (le_of_eq ?_)⟩
  have hsc := scale_sq_mul (d := d) (β := β) hr0 3
  push_cast at hsc
  calc L ^ 2 * growthConstD d σ * r ^ (β + (d : ℝ) / 2) =
      (c₃ * (1 + d * B)) ^ 2 * growthConstD d σ *
        ((r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 3) ^ 2 * r ^ (β + (d : ℝ) / 2)) := by
        rw [hL]; ring
    _ = _ := by rw [hsc]

/-- **Step 4 for `F`**: `Σ_x Σ_i F_i² ≤ Q r^{β - d/2 - 2}`. -/
theorem summable_tsum_sq_clusterFluxD_le {ω : Configuration d} (K : OpenComponent ω)
    {σ r β B : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hB : 0 ≤ B)
    {χ : Fin d → Vertex d → ℝ} {y : Vertex d}
    (hχ : ∀ x ∈ K.supp, ∀ k, |χ k x| ≤ B * (Real.sqrt r + ‖edzD x y‖ + 2) ^ β) (i : Fin d) :
    Summable (fun x => clusterFluxD K σ χ r y i x ^ 2) ∧
      ∑' x, clusterFluxD K σ χ r y i x ^ 2 ≤
        (gaussConstD d σ 2 * (1 + d * B)) ^ 2 * growthConstD d σ * r ^ (β - (d : ℝ) / 2 - 2) := by
  have hr0 : 0 < r := by linarith
  set c₂ := gaussConstD d σ 2 with hc₂
  have hc₂0 : 0 ≤ c₂ := (gaussConstD_pos hσ 2).le
  set L := c₂ * (1 + d * B) * (r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 2) with hL
  have hbd : ∀ x, |clusterFluxD K σ χ r y i x| ≤ L * ((Real.sqrt r + ‖edzD x y‖ + 2) ^ β *
      Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
    intro x
    unfold clusterFluxD
    split_ifs with hx
    · set G := (Real.sqrt r + ‖edzD x y‖ + 2) ^ β with hG
      have hG1 : 1 ≤ G := one_le_growth hβ0 (norm_nonneg _)
      set E := Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r))) with hE
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      set R := r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 2 with hR
      have hR0 : 0 ≤ R := by positivity
      have hrr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
      have hDD : ∀ k, |fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x| ≤
          c₂ * R * E := fun k => by
        have h := abs_fwdDiffD_fwdDiffD_latticeGaussianD_le hσ hr i k x y
        rw [hc₂, hR, hE, hrr]
        refine h.trans (le_of_eq ?_)
        ring
      have hχ' := one_add_sum_abs_le hG1 (hχ x hx)
      have hCRE : 0 ≤ c₂ * R * E := by positivity
      have hsum : |∑ k, χ k x * fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x| ≤
          c₂ * R * E * ∑ k, |χ k x| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => by
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hDD k) (abs_nonneg _)
      unfold stepOneFD
      rw [abs_mul]
      calc |openCondD ω i x| * |fwdDiffD i (fwdDiffD i fun z => latticeGaussianD σ r z y) x -
            ∑ k, χ k x * fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x|
          ≤ 1 * (c₂ * R * E + c₂ * R * E * ∑ k, |χ k x|) :=
            mul_le_mul (abs_openCondD_le ω i x) ((abs_sub _ _).trans (add_le_add (hDD i) hsum))
              (abs_nonneg _) zero_le_one
        _ = c₂ * R * E * (1 + ∑ k, |χ k x|) := by ring
        _ ≤ c₂ * R * E * ((1 + d * B) * G) := mul_le_mul_of_nonneg_left hχ' hCRE
        _ = L * (G * E) := by rw [hL]; ring
    · rw [abs_zero]
      have : 0 ≤ L := by rw [hL]; positivity
      positivity
  obtain ⟨hs, ht⟩ := summable_tsum_sq_le_growth hσ hr hβ0 hβ1 hbd
  refine ⟨hs, ht.trans (le_of_eq ?_)⟩
  have hsc := scale_sq_mul (d := d) (β := β) hr0 2
  push_cast at hsc
  calc L ^ 2 * growthConstD d σ * r ^ (β + (d : ℝ) / 2) =
      (c₂ * (1 + d * B)) ^ 2 * growthConstD d σ *
        ((r ^ (-((d : ℝ) / 2)) / Real.sqrt r ^ 2) ^ 2 * r ^ (β + (d : ℝ) / 2)) := by
        rw [hL]; ring
    _ = _ := by rw [hsc]

/-! ### The centered flux -/

theorem growth_le_of_dist_le {r β v v' : ℝ} (hβ1 : β ≤ 1)
    (hv' : 0 ≤ v') (hvv : v' ≤ v + 1) :
    (Real.sqrt r + v' + 2) ^ β ≤ Real.sqrt r + v + 3 := by
  have hs := Real.sqrt_nonneg r
  calc (Real.sqrt r + v' + 2) ^ β ≤ (Real.sqrt r + v' + 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
    _ = Real.sqrt r + v' + 2 := Real.rpow_one _
    _ ≤ Real.sqrt r + v + 3 := by linarith

/-- The growth of the centered flux on the cluster. -/
theorem abs_centeredFluxD_le {ω : Configuration d} {K : OpenComponent ω} {σ B β r : ℝ}
    {χ : Fin d → Vertex d → ℝ} {y : Vertex d} (hσ : 0 ≤ σ) (hB : 0 ≤ B) (hβ1 : β ≤ 1)
    (hχ : ∀ z ∈ K.supp, ∀ k, |χ k z| ≤ B * (Real.sqrt r + ‖edzD z y‖ + 2) ^ β)
    {x : Vertex d} (hx : x ∈ K.supp) (k i : Fin d) :
    |centeredFluxD ω σ χ k i x| ≤ (1 + σ / 2 + 2 * B) * (Real.sqrt r + ‖edzD x y‖ + 3) := by
  have hv0 := norm_nonneg (edzD x y)
  have hs := Real.sqrt_nonneg r
  set W := Real.sqrt r + ‖edzD x y‖ + 3 with hW
  have hW1 : 1 ≤ W := by linarith
  have h1 : |χ k x| ≤ B * W :=
    (hχ x hx k).trans (mul_le_mul_of_nonneg_left
      (growth_le_of_dist_le hβ1 hv0 (by linarith)) hB)
  have hδ : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  unfold centeredFluxD
  set δ : ℝ := if i = k then 1 else 0 with hδdef
  by_cases hadj : (openGraph ω).Adj x (x + Pi.single i 1)
  · rw [if_pos hadj]
    have hK' : x + Pi.single i 1 ∈ K.supp := mem_supp_of_openAdjD hx hadj
    have hd' : ‖edzD (x + Pi.single i 1) y‖ ≤ ‖edzD x y‖ + 1 := norm_edzD_le_of_adj hadj y
    have h2 : |χ k (x + Pi.single i 1)| ≤ B * W :=
      (hχ _ hK' k).trans (mul_le_mul_of_nonneg_left
        (growth_le_of_dist_le hβ1 (norm_nonneg _) hd') hB)
    have hA : |δ + (χ k (x + Pi.single i 1) - χ k x)| ≤
        |δ| + (|χ k (x + Pi.single i 1)| + |χ k x|) :=
      (abs_add_le _ _).trans (by have := abs_sub (χ k (x + Pi.single i 1)) (χ k x); linarith)
    have hB' : |σ / 2 * δ| = σ / 2 * |δ| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ / 2)]
    calc |δ + (χ k (x + Pi.single i 1) - χ k x) - σ / 2 * δ|
        ≤ |δ + (χ k (x + Pi.single i 1) - χ k x)| + |σ / 2 * δ| := abs_sub _ _
      _ ≤ |δ| + (|χ k (x + Pi.single i 1)| + |χ k x|) + σ / 2 * |δ| := by rw [hB']; linarith
      _ ≤ 1 + (B * W + B * W) + σ / 2 * 1 := by
          gcongr
      _ ≤ (1 + σ / 2 + 2 * B) * W := by nlinarith
  · rw [if_neg hadj, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ / 2)]
    calc σ / 2 * |δ| ≤ σ / 2 * 1 := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ ≤ (1 + σ / 2 + 2 * B) * W := by nlinarith

/-- The coefficients `1_𝒞 g̃_{k,i} D_i D_k P` are square summable. -/
theorem summable_sq_flux_coeffD {ω : Configuration d} (K : OpenComponent ω) {σ B β r : ℝ}
    (hσ : 0 < σ) (hB : 0 ≤ B) (hβ1 : β ≤ 1) (hr : 1 ≤ r)
    {χ : Fin d → Vertex d → ℝ} {y : Vertex d}
    (hχ : ∀ z ∈ K.supp, ∀ k, |χ k z| ≤ B * (Real.sqrt r + ‖edzD z y‖ + 2) ^ β) (k i : Fin d) :
    Summable fun x => (if x ∈ K.supp then centeredFluxD ω σ χ k i x *
      fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x else 0) ^ 2 := by
  have hr0 : 0 < r := by linarith
  set c := (1 + σ / 2 + 2 * B) with hc
  have hc0 : 0 ≤ c := by positivity
  have hg2 := gaussConstD_pos (d := d) hσ 2
  refine (summable_tsum_sq_le_growth (β := 1) (L := 2 * c * (gaussConstD d σ 2 *
    r ^ (-((d : ℝ) / 2)) / r)) (y := y) (g := fun x => if x ∈ K.supp then
      centeredFluxD ω σ χ k i x * fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x
      else 0) hσ hr zero_le_one le_rfl fun x => ?_).1
  split_ifs with hx
  · rw [abs_mul, Real.rpow_one]
    have h1 := abs_centeredFluxD_le hσ.le hB hβ1 hχ hx k i
    have h2 := abs_fwdDiffD_fwdDiffD_latticeGaussianD_le hσ hr i k x y
    have hv0 := norm_nonneg (edzD x y)
    have hs0 := Real.sqrt_nonneg r
    have hW : Real.sqrt r + ‖edzD x y‖ + 3 ≤ 2 * (Real.sqrt r + ‖edzD x y‖ + 2) := by linarith
    calc |centeredFluxD ω σ χ k i x| *
          |fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x|
        ≤ (c * (Real.sqrt r + ‖edzD x y‖ + 3)) * (gaussConstD d σ 2 * r ^ (-((d : ℝ) / 2)) / r *
            Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (c * (2 * (Real.sqrt r + ‖edzD x y‖ + 2))) * (gaussConstD d σ 2 *
            r ^ (-((d : ℝ) / 2)) / r * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * r)))) := by
          gcongr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

/-! ### Summation by parts and the splitting with Young's inequality -/

/-- **Summation by parts on `ℤ^d`**: `Σ_x φ(x) (G(x - e) - G(x)) = Σ_x G(x) (φ(x + e) - φ(x))`. -/
theorem tsum_mul_sub_shift_eqD {φ G : Vertex d → ℝ} (hφ : Summable fun x => φ x ^ 2)
    (hG : Summable fun x => G x ^ 2) (e : Vertex d) :
    ∑' x, φ x * (G (x - e) - G x) = ∑' x, G x * (φ (x + e) - φ x) := by
  have h1 : Summable fun x => φ x * G (x - e) :=
    summable_mul_of_sqD hφ (summable_sq_sub_shiftD hG e)
  have h2 : Summable fun x => φ x * G x := summable_mul_of_sqD hφ hG
  have h3 : Summable fun x => G x * φ (x + e) :=
    summable_mul_of_sqD hG (summable_sq_add_shiftD hφ e)
  have h4 : Summable fun x => G x * φ x := summable_mul_of_sqD hG hφ
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

/-- **The splitting of the source term with Young's inequality** (weight one). -/
theorem tsum_source_le_of_splitD (ω : Configuration d) {θ s β Qf QF Qξ : ℝ}
    {v f ξ : Vertex d → ℝ} {F : Fin d → Vertex d → ℝ} (hθ : 0 < θ) (hs : 0 < s)
    (hv : Summable fun x => v x ^ 2)
    (hfs : Summable fun x => f x ^ 2) (hfb : ∑' x, f x ^ 2 ≤ Qf * s ^ (β - 1))
    (hFs : ∀ i, Summable fun x => F i x ^ 2)
    (hFo : ∀ i x, F i x = openCondD ω i x * F i x)
    (hFb : ∑ i, ∑' x, F i x ^ 2 ≤ QF * s ^ β)
    (hξs : Summable fun x => v x * ξ x)
    (hξ : -(θ⁻¹ * ∑' x, v x * ξ x) ≤ openEnergyD ω v / 4 +
      1 / (8 * s) * ∑' x, v x ^ 2 + Qξ * s ^ β) :
    θ⁻¹ * ∑' x, v x * (f x - ∑ i, (F i (x - Pi.single i 1) - F i x) - ξ x) ≤
      openEnergyD ω v + 1 / (2 * s) * ∑' x, v x ^ 2 +
        (2 * θ⁻¹ ^ 2 * Qf + θ⁻¹ ^ 2 * QF + Qξ) * s ^ β := by
  have hfv : Summable fun x => v x * f x := summable_mul_of_sqD hv hfs
  have hdiv : ∀ i : Fin d, Summable fun x => v x * (F i (x - Pi.single i 1) - F i x) :=
    fun i => summable_mul_of_sqD hv
      (summable_sq_subD (summable_sq_sub_shiftD (hFs i) (Pi.single i 1)) (hFs i))
  have hdivs : Summable fun x => ∑ i, v x * (F i (x - Pi.single i 1) - F i x) :=
    summable_sum fun i _ => hdiv i
  have hsplit : ∑' x, v x * (f x - ∑ i, (F i (x - Pi.single i 1) - F i x) - ξ x) =
      ∑' x, v x * f x - ∑ i, ∑' x, v x * (F i (x - Pi.single i 1) - F i x) -
        ∑' x, v x * ξ x := by
    rw [← Summable.tsum_finsetSum fun i _ => hdiv i, ← hfv.tsum_sub hdivs,
      ← (hfv.sub hdivs).tsum_sub hξs]
    refine tsum_congr fun x => ?_
    rw [← Finset.mul_sum]
    ring
  -- the `f` part
  have key : ∀ x, θ⁻¹ * (v x * f x) ≤ 1 / (8 * s) * v x ^ 2 + 2 * s * θ⁻¹ ^ 2 * f x ^ 2 := by
    intro x
    have hsq := sq_nonneg (v x / (4 * s) - θ⁻¹ * f x)
    have e : 1 / (8 * s) * v x ^ 2 + 2 * s * θ⁻¹ ^ 2 * f x ^ 2 - θ⁻¹ * (v x * f x) =
        2 * s * (v x / (4 * s) - θ⁻¹ * f x) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hs.le hsq]
  have hfpart : θ⁻¹ * ∑' x, v x * f x ≤
      1 / (8 * s) * ∑' x, v x ^ 2 + 2 * s * θ⁻¹ ^ 2 * ∑' x, f x ^ 2 := by
    have hA := hv.mul_left (1 / (8 * s))
    have hB' := hfs.mul_left (2 * s * θ⁻¹ ^ 2)
    calc θ⁻¹ * ∑' x, v x * f x = ∑' x, θ⁻¹ * (v x * f x) := tsum_mul_left.symm
      _ ≤ ∑' x, (1 / (8 * s) * v x ^ 2 + 2 * s * θ⁻¹ ^ 2 * f x ^ 2) :=
          Summable.tsum_le_tsum key (hfv.mul_left _) (hA.add hB')
      _ = 1 / (8 * s) * ∑' x, v x ^ 2 + 2 * s * θ⁻¹ ^ 2 * ∑' x, f x ^ 2 := by
          rw [hA.tsum_add hB', tsum_mul_left, tsum_mul_left]
  -- the divergence part, summed by parts
  have hparts : ∀ i : Fin d, ∑' x, v x * (F i (x - Pi.single i 1) - F i x) =
      ∑' x, F i x * (v (x + Pi.single i 1) - v x) := fun i =>
    tsum_mul_sub_shift_eqD hv (hFs i) _
  have hedge : ∀ i : Fin d, Summable fun x =>
      openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 := fun i =>
    Summable.of_nonneg_of_le (fun x => mul_nonneg (openCondD_nonneg ω i x) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCondD_le_one ω i x))
      (summable_sq_subD (summable_sq_add_shiftD hv (Pi.single i 1)) hv)
  have hFv : ∀ i : Fin d, Summable fun x => F i x * (v (x + Pi.single i 1) - v x) := fun i =>
    summable_mul_of_sqD (hFs i) (summable_sq_subD (summable_sq_add_shiftD hv (Pi.single i 1)) hv)
  have hFpart : -(θ⁻¹ * ∑ i, ∑' x, v x * (F i (x - Pi.single i 1) - F i x)) ≤
      openEnergyD ω v / 4 + θ⁻¹ ^ 2 * ∑ i, ∑' x, F i x ^ 2 := by
    simp only [hparts]
    have hpt : ∀ i x, -(θ⁻¹ * (F i x * (v (x + Pi.single i 1) - v x))) ≤
        openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 / 4 + θ⁻¹ ^ 2 * F i x ^ 2 := by
      intro i x
      have hc2 := openCondD_sq ω i x
      have hFo' := hFo i x
      have h := sq_nonneg (openCondD ω i x * (v (x + Pi.single i 1) - v x) / 2 + θ⁻¹ * F i x)
      have e1 : θ⁻¹ * (F i x * (v (x + Pi.single i 1) - v x)) =
          θ⁻¹ * F i x * (openCondD ω i x * (v (x + Pi.single i 1) - v x)) := by
        conv_lhs => rw [hFo']
        ring
      have e2 : (openCondD ω i x * (v (x + Pi.single i 1) - v x)) ^ 2 =
          openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 := by rw [mul_pow, hc2]
      nlinarith
    have hper : ∀ i : Fin d, -(θ⁻¹ * ∑' x, F i x * (v (x + Pi.single i 1) - v x)) ≤
        (∑' x, openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2) / 4 +
          θ⁻¹ ^ 2 * ∑' x, F i x ^ 2 := by
      intro i
      have hs1 : Summable fun x => openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 / 4 +
          θ⁻¹ ^ 2 * F i x ^ 2 := ((hedge i).div_const 4).add ((hFs i).mul_left _)
      calc -(θ⁻¹ * ∑' x, F i x * (v (x + Pi.single i 1) - v x))
          = ∑' x, -(θ⁻¹ * (F i x * (v (x + Pi.single i 1) - v x))) := by
            rw [tsum_neg, tsum_mul_left]
        _ ≤ ∑' x, (openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 / 4 +
            θ⁻¹ ^ 2 * F i x ^ 2) :=
            Summable.tsum_le_tsum (hpt i) ((hFv i).mul_left θ⁻¹).neg hs1
        _ = _ := by
            rw [((hedge i).div_const 4).tsum_add ((hFs i).mul_left _), tsum_div_const,
              tsum_mul_left]
    have hEsum : openEnergyD ω v =
        ∑ i, ∑' x, openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2 := by
      rw [openEnergyD, Summable.tsum_finsetSum fun i _ => hedge i]
    calc -(θ⁻¹ * ∑ i, ∑' x, F i x * (v (x + Pi.single i 1) - v x))
        = ∑ i, -(θ⁻¹ * ∑' x, F i x * (v (x + Pi.single i 1) - v x)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∑ i, ((∑' x, openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2) / 4 +
            θ⁻¹ ^ 2 * ∑' x, F i x ^ 2) := Finset.sum_le_sum fun i _ => hper i
      _ = openEnergyD ω v / 4 + θ⁻¹ ^ 2 * ∑ i, ∑' x, F i x ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← hEsum]
  -- assembly
  rw [hsplit, mul_sub, mul_sub]
  have hθ0 : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ.le
  have hf2 : 2 * s * θ⁻¹ ^ 2 * ∑' x, f x ^ 2 ≤ 2 * θ⁻¹ ^ 2 * Qf * s ^ β := by
    have h1 : 2 * s * θ⁻¹ ^ 2 * ∑' x, f x ^ 2 ≤ 2 * s * θ⁻¹ ^ 2 * (Qf * s ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hfb (by positivity)
    have e : s * s ^ (β - 1) = s ^ β := by
      rw [Real.rpow_sub_one hs.ne']
      field_simp
    have e2 : 2 * s * θ⁻¹ ^ 2 * (Qf * s ^ (β - 1)) = 2 * θ⁻¹ ^ 2 * Qf * (s * s ^ (β - 1)) := by
      ring
    rw [e2, e] at h1
    exact h1
  have hF2 : θ⁻¹ ^ 2 * ∑ i, ∑' x, F i x ^ 2 ≤ θ⁻¹ ^ 2 * QF * s ^ β := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hFb (by positivity)
  have hhalf : 1 / (8 * s) * ∑' x, v x ^ 2 + 1 / (8 * s) * ∑' x, v x ^ 2 ≤
      1 / (2 * s) * ∑' x, v x ^ 2 := by
    have hv0 : 0 ≤ ∑' x, v x ^ 2 := tsum_nonneg fun x => sq_nonneg _
    have : 1 / (8 * s) + 1 / (8 * s) ≤ 1 / (2 * s) := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    nlinarith
  have hE0 := openEnergyD_nonneg ω v
  have e3 : (2 * θ⁻¹ ^ 2 * Qf + θ⁻¹ ^ 2 * QF + Qξ) * s ^ β =
      2 * θ⁻¹ ^ 2 * Qf * s ^ β + θ⁻¹ ^ 2 * QF * s ^ β + Qξ * s ^ β := by ring
  linarith

end Rigidity.Green.GeneralDim
