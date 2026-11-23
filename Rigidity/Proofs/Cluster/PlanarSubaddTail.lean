import Rigidity.Proofs.Cluster.PlanarSIUpgrade

/-!
# Proposition 5.2 of Armstrong and Dario in dimension two: stretched-exponential tails

`PlanarSubaddGood p ω V K β` says that the planar partition exists, resolves `V`, and
`|μ(V, q) + (1/2) q · ā⁻¹ q| ≤ K |q|² 3^{-β scale V}`,
`|ν(V, ξ) - (1/2) ξ · ā ξ| ≤ K |ξ|² 3^{-β scale V}` for all `q, ξ`.
For the cubes `□_m` centred at the origin its failure has probability at most
`C exp(-c 3^{m s})` (`exists_planarSubaddGood_tail`): with `n = ⌊m/2⌋`, `m = n + 3 + j` and
`3^ℓ ≈ 3^{nα/24}`, on the event of Lemma 5.11 (`exists_planarRho_tail`) the comparison error, the
bound of `-μ` and `ρ(□_m)` are small, and Lemma 5.3 (`planar_minimalset`) gives the bounds
(`planarSubaddGood_of_event`). This is the content of Proposition 5.2 used in Proposition 5.13:
`|μ(□_m, q) + (1/2) q · ā⁻¹ q| ≤ C |q|² 3^{-mβ}` off an event of stretched-exponentially small
probability.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- The conclusion of Proposition 5.2 on a cube `V` at level `K 3^{-β scale V}`. -/
def PlanarSubaddGood (p : unitInterval) (ω : Configuration 2) (V : TriadicCube 2) (K β : ℝ) :
    Prop :=
  PlanarPartitionEvent ω ∧ PlanarResolved ω V ∧
    (∀ q : Fin 2 → ℝ, |planarMu ω V q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
      K * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(V.scale : ℝ) * β)) ∧
    ∀ ξ : Fin 2 → ℝ, |planarNu ω V ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
      K * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(V.scale : ℝ) * β)

/-- The bound of `-μ(V, ·)` by its values at three slopes, on the event. -/
theorem planarMuBound_le_of_planarReachLe {U V : TriadicCube 2} {ℓ : ℕ}
    (h : PlanarReachLe ω U ℓ) (hV : V.vertices ⊆ U.vertices) (hℓ : ℓ ≤ V.scale) :
    planarMuBound ω V ≤ 12649824 * 81 ^ ℓ := by
  have hres := planarResolved_of_planarReachLe h hV hℓ
  set M : ℝ := 2108304 * 81 ^ ℓ with hM
  have hb : ∀ q : Fin 2 → ℝ, 0 ≤ -planarMu ω V q ∧ -planarMu ω V q ≤ M * (|q 0| + |q 1|) ^ 2 :=
    fun q => ⟨neg_nonneg.2 (planarMu_nonpos h.1 hres q),
      by have := neg_planarMu_le_of_planarReachLe h hV hℓ q; rw [hM]; linarith⟩
  obtain ⟨a0, a1⟩ := hb (Pi.single 0 1)
  obtain ⟨b0, b1⟩ := hb (Pi.single 1 1)
  obtain ⟨c0, c1⟩ := hb (Pi.single 0 1 + Pi.single 1 1)
  have n0 : (|(Pi.single 0 1 : Fin 2 → ℝ) 0| + |(Pi.single 0 1 : Fin 2 → ℝ) 1|) ^ 2 = 1 := by
    norm_num [Pi.single_apply]
  have n1 : (|(Pi.single 1 1 : Fin 2 → ℝ) 0| + |(Pi.single 1 1 : Fin 2 → ℝ) 1|) ^ 2 = 1 := by
    norm_num [Pi.single_apply]
  have n2 : (|(Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 0| +
      |(Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) 1|) ^ 2 = 4 := by
    norm_num [Pi.single_apply]
  rw [n0] at a1
  rw [n1] at b1
  rw [n2] at c1
  unfold planarMuBound
  rw [abs_of_nonneg a0, abs_of_nonneg b0]
  have hM0 : 0 ≤ M := by positivity
  have : |-planarMu ω V (Pi.single 0 1 + Pi.single 1 1) - -planarMu ω V (Pi.single 0 1) -
      -planarMu ω V (Pi.single 1 1)| ≤ 4 * M := by
    rw [abs_le]; constructor <;> linarith
  have e : (12649824 : ℝ) * 81 ^ ℓ = 6 * M := by rw [hM]; ring
  rw [e]
  linarith

/-- The constant of the threshold of Lemma 5.11 on the event. -/
noncomputable def planarThresholdConst (C S : ℝ) : ℝ :=
  4 * (C + 1) * (1 + 2 * (9 / 4 * S ^ 2 + 2108304 + S)) + 2 * (132100 * S ^ 2 + 2 * 10 ^ 10)

/-- The constant of the bounds of Proposition 5.2 on the event. -/
noncomputable def planarSubaddConst (C S : ℝ) : ℝ :=
  planarThresholdConst C S + 10 ^ 10 * S +
    Real.sqrt (101198600 * (planarThresholdConst C S + 10 ^ 9 * S))

theorem planarThresholdConst_nonneg {C S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) :
    0 ≤ planarThresholdConst C S := by
  unfold planarThresholdConst; positivity

theorem planarSubaddConst_nonneg {C S : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) :
    0 ≤ planarSubaddConst C S := by
  have := planarThresholdConst_nonneg hC hS
  unfold planarSubaddConst; positivity

theorem eighty_one_pow_le {ℓ : ℕ} {w : ℝ} (hu : (3 : ℝ) ^ ℓ ≤ w) : (81 : ℝ) ^ ℓ ≤ w ^ 4 := by
  rw [show (81 : ℝ) ^ ℓ = ((3 : ℝ) ^ ℓ) ^ 4 by rw [← pow_mul, pow_mul']; norm_num]
  exact pow_le_pow_left₀ (by positivity) hu 4

theorem succ_mul_pow_le {ℓ k : ℕ} {w : ℝ} (hu : (3 : ℝ) ^ ℓ ≤ w) :
    ((ℓ : ℝ) + 1) * ((3 : ℝ) ^ k) ^ ℓ ≤ w ^ (k + 1) := by
  have hℓu : (ℓ : ℝ) + 1 ≤ 3 ^ ℓ := by exact_mod_cast (Nat.lt_pow_self (by norm_num) : ℓ < 3 ^ ℓ)
  have e : ((3 : ℝ) ^ k) ^ ℓ = ((3 : ℝ) ^ ℓ) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e]
  calc ((ℓ : ℝ) + 1) * ((3 : ℝ) ^ ℓ) ^ k ≤ (3 : ℝ) ^ ℓ * ((3 : ℝ) ^ ℓ) ^ k :=
        mul_le_mul_of_nonneg_right hℓu (by positivity)
    _ = ((3 : ℝ) ^ ℓ) ^ (k + 1) := by ring
    _ ≤ w ^ (k + 1) := pow_le_pow_left₀ (by positivity) hu _

/-- The threshold of Lemma 5.11 on the scale `w`. -/
theorem planarRhoThreshold_le_of {α C S w : ℝ} {n ℓ : ℕ} (hC : 0 ≤ C) (hS0 : 0 ≤ S)
    (hw1 : 1 ≤ w) (hu : (3 : ℝ) ^ ℓ ≤ w) (hr : (3 : ℝ) ^ (-(n : ℝ) * α) * w ^ 24 ≤ 1)
    (hsq : w ^ 48 ≤ Real.sqrt ((3 : ℝ) ^ n)) :
    planarRhoThreshold α C S n ℓ ≤ planarThresholdConst C S / w ^ 20 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have h81 := eighty_one_pow_le hu
  have hr0 : 0 < (3 : ℝ) ^ (-(n : ℝ) * α) := by positivity
  have hrw : (3 : ℝ) ^ (-(n : ℝ) * α) ≤ 1 / w ^ 24 := by
    rw [le_div_iff₀ (by positivity)]; exact hr
  have he : Real.exp 1 - 1 ≤ 2 := by
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have he0 : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1; linarith
  have hw4 : (1 : ℝ) ≤ w ^ 4 := one_le_pow₀ hw1
  have h1 : (1 : ℝ) ≤ 81 ^ ℓ := one_le_pow₀ (by norm_num)
  set K₀ : ℝ := 1 + 2 * (9 / 4 * S ^ 2 + 2108304 + S) with hK₀
  have hc1 : 1 + 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S) ≤ K₀ * w ^ 4 := by
    rw [hK₀]
    nlinarith only [h81, hw4, h1, sq_nonneg S, hS0]
  have a1 : 2 * (Real.exp 1 - 1) * (C + 1) ≤ 4 * (C + 1) := by nlinarith only [he, hC]
  have a2 : (1 + 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S)) * (3 : ℝ) ^ (-(n : ℝ) * α) ≤
      K₀ * w ^ 4 * (1 / w ^ 24) := mul_le_mul hc1 hrw hr0.le (by positivity)
  have e1 : K₀ * w ^ 4 * (1 / w ^ 24) = K₀ / w ^ 20 := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e1] at a2
  have t1 : 2 * (Real.exp 1 - 1) * (C + 1) * (1 + 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S)) *
      (3 : ℝ) ^ (-(n : ℝ) * α) ≤ 4 * (C + 1) * K₀ / w ^ 20 := by
    calc _ = 2 * (Real.exp 1 - 1) * (C + 1) *
          ((1 + 2 * (9 / 4 * S ^ 2 + 2108304 * 81 ^ ℓ + S)) * (3 : ℝ) ^ (-(n : ℝ) * α)) := by
          ring
      _ ≤ 4 * (C + 1) * (K₀ / w ^ 20) := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = _ := by ring
  have h5 := succ_mul_pow_le (k := 12) hu
  rw [show ((3 : ℝ) ^ 12) = 531441 by norm_num] at h5
  have h6 : w ^ 13 * w ^ 20 ≤ Real.sqrt ((3 : ℝ) ^ n) := by
    rw [← pow_add]; exact (pow_le_pow_right₀ hw1 (by norm_num)).trans hsq
  have hK0 : 0 ≤ 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) := by positivity
  have t2 : 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (ℓ + 1) * 531441 ^ ℓ /
      Real.sqrt ((3 : ℝ) ^ n) ≤ 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) / w ^ 20 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (ℓ + 1) * 531441 ^ ℓ * w ^ 20
        = 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * (((ℓ : ℝ) + 1) * 531441 ^ ℓ) * w ^ 20 := by ring
      _ ≤ 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) * w ^ 13 * w ^ 20 := by gcongr
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h6 hK0
  unfold planarRhoThreshold planarRhoCap
  calc _ ≤ 4 * (C + 1) * K₀ / w ^ 20 + 2 * (132100 * S ^ 2 + 2 * 10 ^ 10) / w ^ 20 :=
        add_le_add t1 t2
    _ = planarThresholdConst C S / w ^ 20 := by rw [← add_div, planarThresholdConst, hK₀]

/-- The comparison error on the scale `w`. -/
theorem comparison_const_le {ℓ n N : ℕ} {w : ℝ} (hw1 : 1 ≤ w) (hu : (3 : ℝ) ^ ℓ ≤ w)
    (hsq : w ^ 48 ≤ Real.sqrt ((3 : ℝ) ^ n)) (hnN : n ≤ N) :
    10 ^ 9 * (ℓ + 1) * 729 ^ ℓ / Real.sqrt ((3 : ℝ) ^ N) ≤ 10 ^ 9 / w ^ 20 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have h7 := succ_mul_pow_le (k := 6) hu
  rw [show ((3 : ℝ) ^ 6) = 729 by norm_num] at h7
  have hsqm : Real.sqrt ((3 : ℝ) ^ n) ≤ Real.sqrt ((3 : ℝ) ^ N) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) hnN)
  have h8 : w ^ 7 * w ^ 20 ≤ Real.sqrt ((3 : ℝ) ^ N) := by
    rw [← pow_add]; exact (pow_le_pow_right₀ hw1 (by norm_num)).trans (hsq.trans hsqm)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 (by positivity)) (by positivity)]
  calc 10 ^ 9 * (ℓ + 1) * 729 ^ ℓ * w ^ 20 = 10 ^ 9 * (((ℓ : ℝ) + 1) * 729 ^ ℓ) * w ^ 20 := by
        ring
    _ ≤ 10 ^ 9 * w ^ 7 * w ^ 20 := by gcongr
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h8 (by norm_num)

/-- The numerical bounds of Lemma 5.3 on the scale `w`. -/
theorem subadd_numeric {S kT Y ρ Λ w : ℝ} (hS0 : 0 ≤ S) (hkT0 : 0 ≤ kT) (hY0 : 0 ≤ Y)
    (hρ0 : 0 ≤ ρ) (hw1 : 1 ≤ w) (hY : Y ≤ 10 ^ 9 / w ^ 20)
    (hρ : ρ ≤ kT / w ^ 20) (hΛ : Λ ≤ 12649824 * w ^ 4) :
    4 * Y * S + Real.sqrt (8 * (Λ + 1) * (ρ + Y * S)) ≤
        (kT + 10 ^ 10 * S + Real.sqrt (101198600 * (kT + 10 ^ 9 * S))) / w ^ 8 ∧
      ρ + 6 * Y * S + Real.sqrt (8 * (Λ + 1) * (ρ + Y * S)) ≤
        (kT + 10 ^ 10 * S + Real.sqrt (101198600 * (kT + 10 ^ 9 * S))) / w ^ 8 := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have hw8 : 0 < w ^ 8 := by positivity
  have hw820 : w ^ 8 ≤ w ^ 20 := pow_le_pow_right₀ hw1 (by norm_num)
  have h20 : ∀ a : ℝ, 0 ≤ a → a / w ^ 20 ≤ a / w ^ 8 :=
    fun a ha => div_le_div_of_nonneg_left ha hw8 hw820
  have hΛw : Λ + 1 ≤ 12649825 * w ^ 4 := by
    have := one_le_pow₀ (n := 4) hw1; linarith
  have hYS : Y * S ≤ 10 ^ 9 * S / w ^ 20 :=
    calc Y * S ≤ 10 ^ 9 / w ^ 20 * S := mul_le_mul_of_nonneg_right hY hS0
      _ = 10 ^ 9 * S / w ^ 20 := by ring
  have a1 : ρ + Y * S ≤ (kT + 10 ^ 9 * S) / w ^ 20 := by rw [add_div]; linarith
  have hin : 8 * (Λ + 1) * (ρ + Y * S) ≤ 101198600 * (kT + 10 ^ 9 * S) / (w ^ 8) ^ 2 := by
    have a2 := mul_le_mul hΛw a1 (by positivity) (by positivity)
    calc 8 * (Λ + 1) * (ρ + Y * S) = 8 * ((Λ + 1) * (ρ + Y * S)) := by ring
      _ ≤ 8 * (12649825 * w ^ 4 * ((kT + 10 ^ 9 * S) / w ^ 20)) :=
          mul_le_mul_of_nonneg_left a2 (by norm_num)
      _ = _ := by
          rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
          ring
  have hsqrt : Real.sqrt (8 * (Λ + 1) * (ρ + Y * S)) ≤
      Real.sqrt (101198600 * (kT + 10 ^ 9 * S)) / w ^ 8 := by
    refine (Real.sqrt_le_sqrt hin).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hw8.le]
  have hYS8 : Y * S ≤ 10 ^ 9 * S / w ^ 8 := hYS.trans (h20 _ (by positivity))
  have hρ8 : ρ ≤ kT / w ^ 8 := hρ.trans (h20 _ hkT0)
  have e1 : (kT + 10 ^ 10 * S + Real.sqrt (101198600 * (kT + 10 ^ 9 * S))) / w ^ 8 =
      kT / w ^ 8 + 10 ^ 10 * S / w ^ 8 + Real.sqrt (101198600 * (kT + 10 ^ 9 * S)) / w ^ 8 := by
    rw [add_div, add_div]
  have e2 : 10 ^ 10 * S / w ^ 8 = 10 * (10 ^ 9 * S / w ^ 8) := by ring
  have hk8 : 0 ≤ kT / w ^ 8 := by positivity
  have hS8 : 0 ≤ 10 ^ 9 * S / w ^ 8 := by positivity
  rw [e1, e2]
  constructor
  · have : 4 * Y * S = 4 * (Y * S) := by ring
    rw [this]
    linarith
  · have : 6 * Y * S = 6 * (Y * S) := by ring
    rw [this]
    linarith

/-- **Proposition 5.2 on the event of Lemma 5.11** (deterministic): with `w ≥ 1`, `3^ℓ ≤ w`,
`3^{-nα} w^{24} ≤ 1` and `w^{48} ≤ 3^{n/2}`, on the event that the reach is at most `3^ℓ` on
`□_{n+3+j}` and `ρ(□_{n+3+j})` is below the threshold of Lemma 5.11, the bounds of
Proposition 5.2 hold on `□_{n+3+j}` with the error `K / w⁸`. -/
theorem planarSubaddGood_of_event {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {S Sa : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin 2 → ℝ, |((planarAhom p)⁻¹ *ᵥ v) 0| + |((planarAhom p)⁻¹ *ᵥ v) 1| ≤
      S * (|v 0| + |v 1|))
    (hSa : ∀ v : Fin 2 → ℝ, |(planarAhom p *ᵥ v) 0| + |(planarAhom p *ᵥ v) 1| ≤
      Sa * (|v 0| + |v 1|))
    {α C : ℝ} (hC : 0 ≤ C) {n j ℓ : ℕ} {w : ℝ} (hw1 : 1 ≤ w) (hu : (3 : ℝ) ^ ℓ ≤ w)
    (hr : (3 : ℝ) ^ (-(n : ℝ) * α) * w ^ 24 ≤ 1) (hsq : w ^ 48 ≤ Real.sqrt ((3 : ℝ) ^ n))
    (hG : PlanarReachLe ω ⟨n + 3 + j, 0⟩ ℓ ∧
      planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarRhoThreshold α C S n ℓ) :
    PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n + 3 + j, 0⟩ ∧
      (∀ q : Fin 2 → ℝ, |planarMu ω ⟨n + 3 + j, 0⟩ q +
          1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
        planarSubaddConst C S / w ^ 8 * (q 0 ^ 2 + q 1 ^ 2)) ∧
      ∀ ξ : Fin 2 → ℝ, |planarNu ω ⟨n + 3 + j, 0⟩ ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
        planarSubaddConst C S / w ^ 8 * (2 * Sa ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
  obtain ⟨hRL, hρ⟩ := hG
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have hℓU : ℓ ≤ n + 3 + j := by
    have h3 : (3 : ℝ) ^ ℓ ≤ 3 ^ (n + 3 + j) := by
      have hsq3 : Real.sqrt ((3 : ℝ) ^ n) ≤ 3 ^ n := by
        rw [Real.sqrt_le_left (by positivity)]
        have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
        nlinarith only [h1]
      calc (3 : ℝ) ^ ℓ ≤ w := hu
        _ ≤ w ^ 48 := by
            calc w = w ^ 1 := (pow_one w).symm
              _ ≤ w ^ 48 := pow_le_pow_right₀ hw1 (by norm_num)
        _ ≤ 3 ^ n := hsq.trans hsq3
        _ ≤ 3 ^ (n + 3 + j) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h3
  have hres := planarResolved_of_planarReachLe hRL (subset_refl _) hℓU
  have hYe := planarComparisonError_le_of_planarReachLe hRL
  have hZ : planarComparisonError ω ⟨n + 3 + j, 0⟩ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hYe
  have hY0 : 0 ≤ (planarComparisonError ω ⟨n + 3 + j, 0⟩).toReal := ENNReal.toReal_nonneg
  have hYw : (planarComparisonError ω ⟨n + 3 + j, 0⟩).toReal ≤ 10 ^ 9 / w ^ 20 :=
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hYe).trans
      (comparison_const_le hw1 hu hsq (show n ≤ n + 3 + j by omega))
  have hΛ : planarMuBound ω ⟨n + 3 + j, 0⟩ ≤ 12649824 * w ^ 4 :=
    (planarMuBound_le_of_planarReachLe hRL (subset_refl _) hℓU).trans
      (mul_le_mul_of_nonneg_left (eighty_one_pow_le hu) (by norm_num))
  have hρw : planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarThresholdConst C S / w ^ 20 :=
    hρ.trans (planarRhoThreshold_le_of hC hS0 hw1 hu hr hsq)
  obtain ⟨hnum1, hnum2⟩ := subadd_numeric hS0 (planarThresholdConst_nonneg hC hS0) hY0
    (planarRho_nonneg p ω _) hw1 hYw hρw hΛ
  have hKF0 := planarSubaddConst_nonneg hC hS0
  have hSa' : ∀ v : Fin 2 → ℝ, ((planarAhom p *ᵥ v) 0) ^ 2 + ((planarAhom p *ᵥ v) 1) ^ 2 ≤
      2 * Sa ^ 2 * (v 0 ^ 2 + v 1 ^ 2) := by
    intro v
    have h1 : ((planarAhom p *ᵥ v) 0) ^ 2 + ((planarAhom p *ᵥ v) 1) ^ 2 ≤
        (|(planarAhom p *ᵥ v) 0| + |(planarAhom p *ᵥ v) 1|) ^ 2 := by
      rw [← sq_abs ((planarAhom p *ᵥ v) 0), ← sq_abs ((planarAhom p *ᵥ v) 1)]
      nlinarith only [abs_nonneg ((planarAhom p *ᵥ v) 0), abs_nonneg ((planarAhom p *ᵥ v) 1)]
    have h2 := pow_le_pow_left₀ (by positivity) (hSa v) 2
    have h3 := l1_sq_le_two_mul v
    have h4 : (Sa * (|v 0| + |v 1|)) ^ 2 = Sa ^ 2 * (|v 0| + |v 1|) ^ 2 := by ring
    rw [h4] at h2
    have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg Sa)
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ Sa ^ 2 * (2 * (v 0 ^ 2 + v 1 ^ 2)) := h5
      _ = _ := by ring
  refine ⟨hRL.1, hres, fun q => ?_, fun ξ => ?_⟩
  · have hm := (planar_minimalset hpc hRL.1 hres hZ hS0 hS q).1
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [planarSubaddConst]
    exact hnum1
  · have hinv : (planarAhom p)⁻¹ *ᵥ (planarAhom p *ᵥ ξ) = ξ := planarAhom_inv_mulVec_mulVec hpc ξ
    have hm := (planar_minimalset hpc hRL.1 hres hZ hS0 hS (planarAhom p *ᵥ ξ)).2
    rw [hinv] at hm
    have hdot : ∑ i, (planarAhom p *ᵥ ξ) i * ξ i = ∑ i, ξ i * (planarAhom p *ᵥ ξ) i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hdot] at hm
    refine hm.trans ?_
    have hc : planarRho p ω ⟨n + 3 + j, 0⟩ +
        6 * (planarComparisonError ω ⟨n + 3 + j, 0⟩).toReal * S +
        Real.sqrt (8 * (planarMuBound ω ⟨n + 3 + j, 0⟩ + 1) * (planarRho p ω ⟨n + 3 + j, 0⟩ +
          (planarComparisonError ω ⟨n + 3 + j, 0⟩).toReal * S)) ≤
        planarSubaddConst C S / w ^ 8 := by
      rw [planarSubaddConst]
      exact hnum2
    exact mul_le_mul hc (hSa' ξ) (by positivity) (div_nonneg hKF0 (by positivity))

/-- A factor `9ᵐ` is absorbed by halving the rate of a stretched exponential. -/
theorem exists_nine_pow_mul_exp_rpow_le {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, (9 : ℝ) ^ m * Real.exp (-a * ((3 : ℝ) ^ m) ^ s) ≤
      K * Real.exp (-(a / 2) * ((3 : ℝ) ^ m) ^ s) := by
  refine ⟨((⌈((2 : ℕ) : ℝ) / s⌉₊).factorial : ℝ) / (a / 2) ^ ⌈((2 : ℕ) : ℝ) / s⌉₊,
    by positivity, fun m => ?_⟩
  have h := Rigidity.Percolation.pow_mul_exp_neg_rpow_le (d := 2) hs
    (show (0 : ℝ) < 1 / a by positivity) m
  have e1 : ((3 : ℝ) ^ m) ^ 2 = 9 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e2 : Real.exp (-(((3 : ℝ) ^ m) ^ s / (1 / a))) = Real.exp (-a * ((3 : ℝ) ^ m) ^ s) := by
    congr 1; rw [div_div_eq_mul_div, div_one]; ring
  have e3 : 1 / (1 / a) / 2 = a / 2 := by rw [one_div_one_div]
  rw [e1, e2, e3] at h
  linarith

theorem three_rpow_natCast_mul (k : ℕ) (s : ℝ) : ((3 : ℝ) ^ k) ^ s = (3 : ℝ) ^ ((k : ℝ) * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- The scales of the proof of the tails of Proposition 5.2: with `n ≈ m/2`, `x = nα/24`,
`ℓ = ⌊x⌋` and `w = 3^x`. -/
theorem tail_params {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1 / 4) {m n ℓ : ℕ} {w X : ℝ}
    (hn3 : (m : ℝ) ≤ 2 * n + 1) (hℓ : ℓ = ⌊(n : ℝ) * α / 24⌋₊)
    (hw : w = (3 : ℝ) ^ ((n : ℝ) * α / 24))
    (hX : X = ((3 : ℝ) ^ m) ^ (α / 48)) :
    1 ≤ w ∧ (3 : ℝ) ^ ℓ ≤ w ∧ w ≤ 3 * (3 : ℝ) ^ ℓ ∧ (3 : ℝ) ^ (-(n : ℝ) * α) * w ^ 24 ≤ 1 ∧
      w ^ 48 ≤ Real.sqrt ((3 : ℝ) ^ n) ∧ ℓ ≤ n ∧
      1 / w ^ 8 ≤ 3 * (3 : ℝ) ^ (-(m : ℝ) * (α / 6)) ∧ X ≤ 3 * w := by
  have hx0 : 0 ≤ (n : ℝ) * α / 24 := by positivity
  have hnα : (n : ℝ) * α ≤ n / 4 := by
    have := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hmα : (m : ℝ) * α ≤ (2 * n + 1) * α := mul_le_mul_of_nonneg_right hn3 hα0.le
  have hwpow : ∀ k : ℕ, w ^ k = (3 : ℝ) ^ ((n : ℝ) * α / 24 * k) := fun k => by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw]; exact Real.one_le_rpow (by norm_num) hx0
  · rw [hw, hℓ, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hx0)
  · rw [hw, hℓ, ← pow_succ', ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := Nat.lt_floor_add_one ((n : ℝ) * α / 24)
    push_cast
    linarith
  · rw [hwpow, ← Real.rpow_add (by norm_num)]
    have : -(n : ℝ) * α + (n : ℝ) * α / 24 * (24 : ℕ) = 0 := by push_cast; ring
    rw [this, Real.rpow_zero]
  · have h2 : (w ^ 48) ^ 2 ≤ (3 : ℝ) ^ n := by
      rw [← pow_mul, hwpow, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    calc w ^ 48 = Real.sqrt ((w ^ 48) ^ 2) := by
          rw [Real.sqrt_sq (by rw [hw]; positivity)]
      _ ≤ Real.sqrt ((3 : ℝ) ^ n) := Real.sqrt_le_sqrt h2
  · rw [hℓ]
    apply Nat.floor_le_of_le
    linarith
  · have h3 : 0 < (3 : ℝ) ^ ((m : ℝ) * (α / 6)) := by positivity
    have hw8 : (3 : ℝ) ^ ((m : ℝ) * (α / 6)) ≤ 3 * w ^ 8 := by
      rw [hwpow, show (3 : ℝ) * 3 ^ ((n : ℝ) * α / 24 * (8 : ℕ)) =
        3 ^ ((n : ℝ) * α / 24 * (8 : ℕ) + 1) by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith
    have hw0 : 0 < w := by rw [hw]; positivity
    rw [neg_mul, Real.rpow_neg (by norm_num), div_le_iff₀ (by positivity),
      show (3 : ℝ) * ((3 : ℝ) ^ ((m : ℝ) * (α / 6)))⁻¹ * w ^ 8 =
        3 * w ^ 8 / (3 : ℝ) ^ ((m : ℝ) * (α / 6)) by ring, le_div_iff₀ h3, one_mul]
    exact hw8
  · rw [hX, three_rpow_natCast_mul, hw, show (3 : ℝ) * 3 ^ ((n : ℝ) * α / 24) =
      3 ^ ((n : ℝ) * α / 24 + 1) by rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith

/-- The three probabilities of the tails of Proposition 5.2. -/
theorem tail_terms {α θ c C₂ K₁ K₂ c' X : ℝ} {m n j ℓ : ℕ} (hα0 : 0 < α) (hα : α ≤ 1 / 4)
    (hθ : 0 < θ) (hc : 0 < c) (hC₂ : 0 ≤ C₂) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hc'1 : c' ≤ 1 / (9 * θ) / 2) (hc'2 : c' ≤ c / 2) (hc'3 : c' ≤ 1 / 729)
    (hX0 : 0 ≤ X) (hXr : X = (3 : ℝ) ^ ((m : ℝ) * (α / 48)))
    (h₁ : (9 : ℝ) ^ m * Real.exp (-(1 / (9 * θ)) * X) ≤
      K₁ * Real.exp (-(1 / (9 * θ) / 2) * X))
    (h₂ : (9 : ℝ) ^ m * Real.exp (-c * X) ≤ K₂ * Real.exp (-(c / 2) * X))
    (hmn : m = n + 3 + j) (hn2 : (2 : ℝ) * n ≤ m) (hn3 : (m : ℝ) ≤ 2 * n + 1) (hn4 : (4 : ℝ) ≤ n)
    (hX9 : X / 9 ≤ (3 : ℝ) ^ ℓ) :
    (9 : ℝ) ^ (n + 3 + j) * (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ))) +
        (9 : ℝ) ^ (3 + j) * (2 * C₂ * Real.exp (-c * (3 : ℝ) ^ n)) +
        729 * Real.exp (-((9 : ℝ) ^ j * (3 : ℝ) ^ (-(n : ℝ) * α))) ≤
      (2 * K₁ + 2 * C₂ * K₂ + 729) * Real.exp (-c' * X) := by
  have hexp_mono : ∀ {a b : ℝ}, b ≤ a → Real.exp (-a * X) ≤ Real.exp (-b * X) :=
    fun {a b} hab => Real.exp_le_exp.2 (by nlinarith only [hab, hX0])
  have hmR : (m : ℝ) = n + 3 + j := by exact_mod_cast hmn
  -- the first term
  have hT1 : (9 : ℝ) ^ (n + 3 + j) * (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ))) ≤
      2 * K₁ * Real.exp (-c' * X) := by
    have he : Real.exp (-((3 : ℝ) ^ ℓ / θ)) ≤ Real.exp (-(1 / (9 * θ)) * X) := by
      apply Real.exp_le_exp.2
      rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul,
        div_le_div_iff₀ (by positivity) hθ]
      nlinarith only [hX9, hθ]
    rw [← hmn]
    have s1 := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 2 * 9 ^ m by positivity)
    have s2 := mul_le_mul_of_nonneg_left (hexp_mono hc'1) (show (0 : ℝ) ≤ 2 * K₁ by positivity)
    have s3 := mul_le_mul_of_nonneg_left h₁ (show (0 : ℝ) ≤ 2 by norm_num)
    calc _ = 2 * 9 ^ m * Real.exp (-((3 : ℝ) ^ ℓ / θ)) := by ring
      _ ≤ 2 * 9 ^ m * Real.exp (-(1 / (9 * θ)) * X) := s1
      _ = 2 * (9 ^ m * Real.exp (-(1 / (9 * θ)) * X)) := by ring
      _ ≤ 2 * (K₁ * Real.exp (-(1 / (9 * θ) / 2) * X)) := s3
      _ = 2 * K₁ * Real.exp (-(1 / (9 * θ) / 2) * X) := by ring
      _ ≤ _ := s2
  -- the second term
  have hT2 : (9 : ℝ) ^ (3 + j) * (2 * C₂ * Real.exp (-c * (3 : ℝ) ^ n)) ≤
      2 * C₂ * K₂ * Real.exp (-c' * X) := by
    have h3 : X ≤ (3 : ℝ) ^ n := by
      rw [hXr, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith only [hα, hα0, hn3, hn4]
    have he : Real.exp (-c * (3 : ℝ) ^ n) ≤ Real.exp (-c * X) :=
      Real.exp_le_exp.2 (by nlinarith only [h3, hc])
    have h9 : (9 : ℝ) ^ (3 + j) ≤ 9 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have s0 := mul_le_mul h9 he (Real.exp_pos _).le (by positivity)
    have s1 := (mul_le_mul_of_nonneg_left (hexp_mono hc'2) hK₂)
    calc _ = 2 * C₂ * ((9 : ℝ) ^ (3 + j) * Real.exp (-c * (3 : ℝ) ^ n)) := by ring
      _ ≤ 2 * C₂ * (9 ^ m * Real.exp (-c * X)) :=
          mul_le_mul_of_nonneg_left s0 (by positivity)
      _ ≤ 2 * C₂ * (K₂ * Real.exp (-(c / 2) * X)) :=
          mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ ≤ 2 * C₂ * (K₂ * Real.exp (-c' * X)) := mul_le_mul_of_nonneg_left s1 (by positivity)
      _ = _ := by ring
  -- the third term
  have hT3 : 729 * Real.exp (-((9 : ℝ) ^ j * (3 : ℝ) ^ (-(n : ℝ) * α))) ≤
      729 * Real.exp (-c' * X) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    have h9 : (9 : ℝ) ^ j * (3 : ℝ) ^ (-(n : ℝ) * α) =
        (3 : ℝ) ^ (((2 * j : ℕ) : ℝ) - n * α) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_natCast, pow_mul, neg_mul]
      norm_num
    rw [h9]
    have hge : X / 729 ≤ (3 : ℝ) ^ (((2 * j : ℕ) : ℝ) - n * α) := by
      rw [hXr, div_le_iff₀ (by norm_num), show (729 : ℝ) = (3 : ℝ) ^ ((6 : ℕ) : ℝ) by
        rw [Real.rpow_natCast]; norm_num, ← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      have hnα : (n : ℝ) * α ≤ n / 4 := by
        have := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      have hmα : (m : ℝ) * (α / 48) ≤ m / 192 := by
        have := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
      linarith
    have : c' * X ≤ X / 729 := by nlinarith only [hc'3, hX0]
    linarith
  linarith

/-- **Proposition 5.2 of Armstrong and Dario with stretched-exponential tails** (dimension two,
`p > p_c(2)`): there are `K, β, s, c, K'` with
`P[PlanarSubaddGood p ω □_m K β fails] ≤ K' exp(-c 3^{m s})` for every `m`. -/
theorem exists_planarSubaddGood_tail {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K β s c K' : ℝ, 0 ≤ K ∧ 0 < β ∧ 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ 0 ≤ K' ∧ ∀ m : ℕ,
      latticeBondLaw 2 p {ω | ¬ PlanarSubaddGood p ω ⟨m, 0⟩ K β} ≤
        ENNReal.ofReal (K' * Real.exp (-c * ((3 : ℝ) ^ m) ^ s)) := by
  obtain ⟨α, C, θ, c, hα0, hα, hC, hθ, hc, C₂, hC₂, htail⟩ := exists_planarRho_tail hpc
  obtain ⟨S, hS0, hS⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  obtain ⟨Sa, hSa0, hSa⟩ := exists_abs_mulVec_le (planarAhom p)
  have hKF0 := planarSubaddConst_nonneg hC hS0
  have hs0 : 0 < α / 48 := by positivity
  have ha₁0 : 0 < 1 / (9 * θ) := by positivity
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nine_pow_mul_exp_rpow_le ha₁0 hs0
  obtain ⟨K₂, hK₂, h₂⟩ := exists_nine_pow_mul_exp_rpow_le hc hs0
  obtain ⟨c', hc'⟩ : ∃ c', c' = min (1 / (9 * θ) / 2) (min (c / 2) (1 / 729)) := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by
    rw [hc']; exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hc'1 : c' ≤ 1 / (9 * θ) / 2 := by rw [hc']; exact min_le_left _ _
  have hc'2 : c' ≤ c / 2 := by rw [hc']; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc'3 : c' ≤ 1 / 729 := by rw [hc']; exact (min_le_right _ _).trans (min_le_right _ _)
  have hC₂0 : 0 ≤ C₂.toReal := ENNReal.toReal_nonneg
  refine ⟨3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2), α / 6, α / 48, c',
    max (2 * K₁ + 2 * C₂.toReal * K₂ + 729) (Real.exp (c' * 3 ^ 8)), by positivity,
    by positivity, hs0, by linarith, hc'0, le_max_of_le_right (Real.exp_pos _).le,
    fun m => ?_⟩
  by_cases hm8 : m < 8
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hX : ((3 : ℝ) ^ m) ^ (α / 48) ≤ 3 ^ 8 := by
      rw [three_rpow_natCast_mul]
      calc (3 : ℝ) ^ ((m : ℝ) * (α / 48)) ≤ 3 ^ ((8 : ℕ) : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have : (m : ℝ) ≤ 8 := by exact_mod_cast hm8.le
            nlinarith only [this, hα, hα0]
        _ = 3 ^ 8 := by rw [Real.rpow_natCast]
    calc (1 : ℝ) = Real.exp (c' * 3 ^ 8) * Real.exp (-c' * 3 ^ 8) := by
          rw [← Real.exp_add]; simp
      _ ≤ _ := by
          apply mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 (by nlinarith only [hX, hc'0]))
            (by positivity) (by positivity)
  push Not at hm8
  obtain ⟨n, hn⟩ : ∃ n, n = m / 2 := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, j = m - n - 3 := ⟨_, rfl⟩
  have hmn : m = n + 3 + j := by omega
  have hn2 : (2 : ℝ) * n ≤ m := by exact_mod_cast (show 2 * n ≤ m by omega)
  have hn3 : (m : ℝ) ≤ 2 * n + 1 := by exact_mod_cast (show m ≤ 2 * n + 1 by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = ⌊(n : ℝ) * α / 24⌋₊ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = (3 : ℝ) ^ ((n : ℝ) * α / 24) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = ((3 : ℝ) ^ m) ^ (α / 48) := ⟨_, rfl⟩
  obtain ⟨hw1, hu, hwu, hr, hsq, hℓn, hinv, hX1⟩ := tail_params hα0 hα hn3 hℓ hw hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- the event
  have hsub : {ω | ¬ PlanarSubaddGood p ω ⟨m, 0⟩ (3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2))
      (α / 6)} ⊆ {ω | ¬ (PlanarReachLe ω ⟨n + 3 + j, 0⟩ ℓ ∧
        planarRho p ω ⟨n + 3 + j, 0⟩ ≤ planarRhoThreshold α C S n ℓ)} := by
    intro ω hω hG
    apply hω
    obtain ⟨hP, hres, hμb, hνb⟩ :=
      planarSubaddGood_of_event hpc hS0 hS hSa hC hw1 hu hr hsq hG
    rw [← hmn] at hres hμb hνb
    have h1 : (0 : ℝ) < 1 + 2 * Sa ^ 2 := by positivity
    have hr3 : 0 < (3 : ℝ) ^ (-(m : ℝ) * (α / 6)) := by positivity
    have hKw : planarSubaddConst C S / w ^ 8 * (1 + 2 * Sa ^ 2) ≤
        3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * (α / 6)) := by
      have := mul_le_mul_of_nonneg_left hinv hKF0
      calc planarSubaddConst C S / w ^ 8 * (1 + 2 * Sa ^ 2)
          = planarSubaddConst C S * (1 / w ^ 8) * (1 + 2 * Sa ^ 2) := by ring
        _ ≤ planarSubaddConst C S * (3 * (3 : ℝ) ^ (-(m : ℝ) * (α / 6))) * (1 + 2 * Sa ^ 2) :=
            mul_le_mul_of_nonneg_right this h1.le
        _ = _ := by ring
    have hKF8 : 0 ≤ planarSubaddConst C S / w ^ 8 := div_nonneg hKF0 (by positivity)
    refine ⟨hP, hres, fun q => ?_, fun ξ => ?_⟩
    · refine (hμb q).trans ?_
      show planarSubaddConst C S / w ^ 8 * (q 0 ^ 2 + q 1 ^ 2) ≤
        3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2) * (q 0 ^ 2 + q 1 ^ 2) *
          (3 : ℝ) ^ (-(m : ℝ) * (α / 6))
      have hq : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
      have h2 : planarSubaddConst C S / w ^ 8 ≤ planarSubaddConst C S / w ^ 8 * (1 + 2 * Sa ^ 2) :=
        le_mul_of_one_le_right hKF8 (by nlinarith only [sq_nonneg Sa])
      calc planarSubaddConst C S / w ^ 8 * (q 0 ^ 2 + q 1 ^ 2)
          ≤ 3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * (α / 6)) *
              (q 0 ^ 2 + q 1 ^ 2) := mul_le_mul_of_nonneg_right (h2.trans hKw) hq
        _ = _ := by ring
    · refine (hνb ξ).trans ?_
      show planarSubaddConst C S / w ^ 8 * (2 * Sa ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2)) ≤
        3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2) * (ξ 0 ^ 2 + ξ 1 ^ 2) *
          (3 : ℝ) ^ (-(m : ℝ) * (α / 6))
      have hq : 0 ≤ ξ 0 ^ 2 + ξ 1 ^ 2 := by positivity
      have h2 : planarSubaddConst C S / w ^ 8 * (2 * Sa ^ 2) ≤
          planarSubaddConst C S / w ^ 8 * (1 + 2 * Sa ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hKF8
      calc planarSubaddConst C S / w ^ 8 * (2 * Sa ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2))
          = planarSubaddConst C S / w ^ 8 * (2 * Sa ^ 2) * (ξ 0 ^ 2 + ξ 1 ^ 2) := by ring
        _ ≤ 3 * planarSubaddConst C S * (1 + 2 * Sa ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * (α / 6)) *
              (ξ 0 ^ 2 + ξ 1 ^ 2) := mul_le_mul_of_nonneg_right (h2.trans hKw) hq
        _ = _ := by ring
  refine (measure_mono hsub).trans ((htail hS0 hS n j ℓ hℓn).trans ?_)
  have hXr : X = (3 : ℝ) ^ ((m : ℝ) * (α / 48)) := by rw [hX, three_rpow_natCast_mul]
  have hX9 : X / 9 ≤ (3 : ℝ) ^ ℓ := by linarith
  have h₁' := h₁ m
  have h₂' := h₂ m
  rw [← hX] at h₁' h₂'
  have hsum := tail_terms hα0 hα hθ hc hC₂0 hK₁ hK₂ hc'1 hc'2 hc'3 hX0 hXr h₁' h₂' hmn hn2 hn3
    hn4 hX9
  have e2 : ENNReal.ofReal ((9 : ℝ) ^ (3 + j)) *
      (2 * C₂ * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n))) =
      ENNReal.ofReal ((9 : ℝ) ^ (3 + j) * (2 * C₂.toReal * Real.exp (-c * (3 : ℝ) ^ n))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₂, ENNReal.ofReal_ofNat]
  rw [e2, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← hX]
  apply ENNReal.ofReal_le_ofReal
  exact hsum.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

end Rigidity.Proofs.Cluster
