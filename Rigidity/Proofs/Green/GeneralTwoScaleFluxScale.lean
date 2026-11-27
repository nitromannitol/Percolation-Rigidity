import Rigidity.Proofs.Green.GeneralTwoScaleCutoff

/-!
# One scale of the multiscale estimate of Step 3 of Proposition 4.3 of Dario–Gu on `ℤ^d`

Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2333-2405 of the source) tests the
centered flux against `φ = A u` with `A = (η_m - η_{m-1}) D_i D_k p̄` and `u = w`, on the balls
`𝒞_∞ ∩ B_{2^{m+2}√t}(y)`, and uses the bound of Proposition 2.13 on the weak norm (1.33). On
`ℤ^d` the normalized Sobolev norm (1.32) carries the factor `|V|^{-1/d}`:

* `card_mul_clusterH1NormD`: `|V| ‖φ‖_{H̲¹(V)} = |V|^{-1/d} |V|^{1/2} ‖φ‖_{L²(V)}
  + |V|^{1/2} ‖∇φ‖_{L²(V)}`;
* `neg_sum_le_of_weakNormLeD`: if `‖g‖_{H̲^{-1}(V)} ≤ B`, `|V| ≤ Λ`, `d ≥ 2` and `φ` vanishes on
  `V \ int_a(V)`, then `-Σ_{x ∈ V} g φ ≤ B (Λ^{1/2 - 1/d} ‖φ‖_{L²(V)} + Λ^{1/2} ‖∇φ‖_{L²(V)})`;
* `openGradNormD_sq_le`: `|∇φ|(x)² ≤ 2d Σ_i (a_i(x) (φ(x + e_i) - φ(x))² + a_i(x - e_i)
  (φ(x - e_i) - φ(x))²)`;
* `neg_tsum_le_of_weakNormLe_coeffD`: if moreover `|A| ≤ a`, `|A(x + e_i) - A(x)| ≤ b` and `A u`
  vanishes outside `int_a(V)`, then `-Σ_x g A u ≤ B (Λ^{1/2 - 1/d} a ‖u‖₂ +
  Λ^{1/2} (3 √d a E(u)^{1/2} + 3 d b ‖u‖₂))`, the planar `neg_tsum_le_of_weakNormLe_coeff` on
  `ℤ^d`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

theorem openGradNormD_neg (ω : Configuration d) (V : Finset (Vertex d)) (φ : Vertex d → ℝ)
    (x : Vertex d) : openGradNormD ω V (fun z => -φ z) x = openGradNormD ω V φ x := by
  unfold openGradNormD
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs
  · rw [show -φ z - -φ x = -(φ z - φ x) by ring, abs_neg]
  · rfl

theorem clusterH1NormD_neg (ω : Configuration d) (V : Finset (Vertex d)) (φ : Vertex d → ℝ) :
    clusterH1NormD ω V (fun z => -φ z) = clusterH1NormD ω V φ := by
  unfold clusterH1NormD
  simp only [openGradNormD_neg, neg_sq]

/-- `|V| ‖φ‖_{H̲¹(V)} = |V|^{-1/d} |V|^{1/2} ‖φ‖_{L²(V)} + |V|^{1/2} ‖∇φ‖_{L²(V)}` for
`V ≠ ∅`. -/
theorem card_mul_clusterH1NormD {ω : Configuration d} {V : Finset (Vertex d)}
    (hV : 0 < (V.card : ℝ)) (φ : Vertex d → ℝ) :
    (V.card : ℝ) * clusterH1NormD ω V φ =
      (V.card : ℝ) ^ (-(1 / d : ℝ)) * Real.sqrt (V.card : ℝ) * Real.sqrt (∑ x ∈ V, φ x ^ 2) +
        Real.sqrt (V.card : ℝ) * Real.sqrt (∑ x ∈ V, openGradNormD ω V φ x ^ 2) := by
  set n : ℝ := (V.card : ℝ) with hn
  unfold clusterH1NormD
  rw [← hn, Real.sqrt_mul (inv_nonneg.2 hV.le), Real.sqrt_mul (inv_nonneg.2 hV.le), Real.sqrt_inv]
  have hdiv : n * (Real.sqrt n)⁻¹ = Real.sqrt n := by rw [← div_eq_mul_inv, Real.div_sqrt]
  rw [show ∀ a b c : ℝ, n * (a * ((Real.sqrt n)⁻¹ * b) + (Real.sqrt n)⁻¹ * c) =
    a * (n * (Real.sqrt n)⁻¹) * b + (n * (Real.sqrt n)⁻¹) * c from fun a b c => by ring, hdiv]

theorem card_pow_mul_sqrt_le {n Λ : ℝ} (hd : 2 ≤ d) (hn : 0 < n) (hnΛ : n ≤ Λ) :
    n ^ (-(1 / d : ℝ)) * Real.sqrt n ≤ Λ ^ ((1 : ℝ) / 2 - 1 / d) := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he : (0 : ℝ) ≤ 1 / 2 - 1 / d := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd0
    linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  rw [show -(1 / (d : ℝ)) + 1 / 2 = 1 / 2 - 1 / d by ring]
  exact Real.rpow_le_rpow hn.le hnΛ he

/-- **The duality with the weak norm** on a finite set `V` of `ℤ^d`, `d ≥ 2`. -/
theorem neg_sum_le_of_weakNormLeD {ω : Configuration d} {V : Finset (Vertex d)}
    {g φ : Vertex d → ℝ} {B Λ : ℝ} (hd : 2 ≤ d) (h : WeakNormLeD ω V g B) (hB : 0 ≤ B)
    (hΛ : (V.card : ℝ) ≤ Λ) (hφ : ∀ x ∈ V, x ∉ openInteriorD ω V → φ x = 0) :
    -(∑ x ∈ V, g x * φ x) ≤ B * (Λ ^ ((1 : ℝ) / 2 - 1 / d) * Real.sqrt (∑ x ∈ V, φ x ^ 2) +
      Real.sqrt Λ * Real.sqrt (∑ x ∈ V, openGradNormD ω V φ x ^ 2)) := by
  rcases Nat.eq_zero_or_pos V.card with h0 | hpos
  · have hV0 : V = ∅ := Finset.card_eq_zero.1 h0
    have hs : ∑ x ∈ V, g x * φ x = 0 := by rw [hV0, Finset.sum_empty]
    have hΛ0 : 0 ≤ Λ := by
      refine le_trans ?_ hΛ
      exact Nat.cast_nonneg _
    rw [hs, neg_zero]
    have : 0 ≤ Λ ^ ((1 : ℝ) / 2 - 1 / d) := Real.rpow_nonneg hΛ0 _
    positivity
  have hV : 0 < (V.card : ℝ) := by exact_mod_cast hpos
  have h1 := h (fun z => -φ z) (fun x hx hx' => by rw [hφ x hx hx', neg_zero])
  rw [clusterH1NormD_neg] at h1
  have e : (V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * -φ x = -((V.card : ℝ)⁻¹ * ∑ x ∈ V, g x * φ x) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hV.le
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_left_comm,
    card_mul_clusterH1NormD hV] at h2
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ hB)
  have k1 := card_pow_mul_sqrt_le hd hV hΛ
  have k2 : Real.sqrt (V.card : ℝ) ≤ Real.sqrt Λ := Real.sqrt_le_sqrt hΛ
  have p1 := Real.sqrt_nonneg (∑ x ∈ V, φ x ^ 2)
  have p2 := Real.sqrt_nonneg (∑ x ∈ V, openGradNormD ω V φ x ^ 2)
  exact add_le_add (mul_le_mul_of_nonneg_right k1 p1) (mul_le_mul_of_nonneg_right k2 p2)

theorem openCondD_le_one (ω : Configuration d) (i : Fin d) (x : Vertex d) :
    openCondD ω i x ≤ 1 :=
  (le_abs_self _).trans (abs_openCondD_le ω i x)

theorem openCondD_back (ω : Configuration d) (i : Fin d) (x : Vertex d) :
    openCondD ω i (x - Pi.single i 1) =
      if (openGraph ω).Adj x (x - Pi.single i 1) then 1 else 0 := by
  unfold openCondD
  rw [sub_add_cancel]
  by_cases h : (openGraph ω).Adj x (x - Pi.single i 1)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

/-- `|∇φ|(x)` is at most the sum of the differences of `φ` along the open edges at `x`. -/
theorem openGradNormD_le (ω : Configuration d) (V : Finset (Vertex d)) (φ : Vertex d → ℝ)
    (x : Vertex d) : openGradNormD ω V φ x ≤ ∑ i,
      (openCondD ω i x * |φ (x + Pi.single i 1) - φ x| +
        openCondD ω i (x - Pi.single i 1) * |φ (x - Pi.single i 1) - φ x|) := by
  unfold openGradNormD
  rw [Rigidity.Proofs.Regularity.sum_nbrFinset]
  refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
  · unfold openCondD unit
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · rw [one_mul]
      exact abs_nonneg _
    · rw [zero_mul]
  · rw [openCondD_back]
    unfold unit
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · rw [one_mul]
      exact abs_nonneg _
    · rw [zero_mul]

/-- `|∇φ|(x)² ≤ 2d Σ_i (a_i(x) (φ(x + e_i) - φ(x))² + a_i(x - e_i) (φ(x - e_i) - φ(x))²)`. -/
theorem openGradNormD_sq_le (ω : Configuration d) (V : Finset (Vertex d)) (φ : Vertex d → ℝ)
    (x : Vertex d) : openGradNormD ω V φ x ^ 2 ≤ 2 * d * ∑ i,
      (openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 +
        openCondD ω i (x - Pi.single i 1) * (φ (x - Pi.single i 1) - φ x) ^ 2) := by
  have h0 : 0 ≤ openGradNormD ω V φ x := by
    unfold openGradNormD
    exact Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  have h1 := pow_le_pow_left₀ h0 (openGradNormD_le ω V φ x) 2
  refine h1.trans ?_
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => openCondD ω i x * |φ (x + Pi.single i 1) - φ x| +
      openCondD ω i (x - Pi.single i 1) * |φ (x - Pi.single i 1) - φ x|)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  refine h2.trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have key : ∀ (z : Vertex d) (u : ℝ), (openCondD ω i z * |u|) ^ 2 = openCondD ω i z * u ^ 2 := by
    intro z u
    rw [mul_pow, openCondD_sq, sq_abs]
  have k1 := key x (φ (x + Pi.single i 1) - φ x)
  have k2 := key (x - Pi.single i 1) (φ (x - Pi.single i 1) - φ x)
  set a := openCondD ω i x * |φ (x + Pi.single i 1) - φ x|
  set b := openCondD ω i (x - Pi.single i 1) * |φ (x - Pi.single i 1) - φ x|
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  calc (d : ℝ) * (a + b) ^ 2 ≤ d * (2 * (a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_left hab hd0
    _ = _ := by rw [k1, k2]; ring

theorem summable_edge_sqD (ω : Configuration d) {u : Vertex d → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    Summable fun x => ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 := by
  refine summable_sum fun i _ => ?_
  exact Summable.of_nonneg_of_le (fun x => mul_nonneg (openCondD_nonneg ω i x) (sq_nonneg _))
    (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCondD_le_one ω i x))
    (summable_sq_subD (summable_sq_add_shiftD hu (Pi.single i 1)) hu)

theorem summable_edge_sq_backD (ω : Configuration d) {u : Vertex d → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    Summable fun x => ∑ i, openCondD ω i (x - Pi.single i 1) *
      (u (x - Pi.single i 1) - u x) ^ 2 := by
  refine summable_sum fun i _ => ?_
  exact Summable.of_nonneg_of_le
    (fun x => mul_nonneg (openCondD_nonneg ω i _) (sq_nonneg _))
    (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCondD_le_one ω i _))
    (summable_sq_subD (summable_sq_sub_shiftD hu (Pi.single i 1)) hu)

/-- The backward edges are the forward edges. -/
theorem tsum_edge_sq_back_eqD (ω : Configuration d) {u : Vertex d → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    ∑' x, ∑ i, openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) ^ 2 =
      ∑' x, ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 := by
  have hb : ∀ i : Fin d, Summable fun x =>
      openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) ^ 2 :=
    fun i => Summable.of_nonneg_of_le
      (fun x => mul_nonneg (openCondD_nonneg ω i _) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCondD_le_one ω i _))
      (summable_sq_subD (summable_sq_sub_shiftD hu (Pi.single i 1)) hu)
  have hf : ∀ i : Fin d, Summable fun x =>
      openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 :=
    fun i => Summable.of_nonneg_of_le (fun x => mul_nonneg (openCondD_nonneg ω i x) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCondD_le_one ω i x))
      (summable_sq_subD (summable_sq_add_shiftD hu (Pi.single i 1)) hu)
  rw [Summable.tsum_finsetSum fun i _ => hb i, Summable.tsum_finsetSum fun i _ => hf i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (Equiv.addRight (Pi.single i 1 : Vertex d)).tsum_eq
    (fun x => openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) ^ 2)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
  rw [← this]
  exact tsum_congr fun x => by ring

/-- **One scale of Step 3** on `ℤ^d`: the duality with the weak norm and the product rule. -/
theorem neg_tsum_le_of_weakNormLe_coeffD {ω : Configuration d} {V : Finset (Vertex d)}
    {g A u : Vertex d → ℝ} {B Λ a b : ℝ} (hd : 2 ≤ d) (h : WeakNormLeD ω V g B) (hB : 0 ≤ B)
    (hΛ : (V.card : ℝ) ≤ Λ) (hu : Summable fun x => u x ^ 2) (ha : ∀ x, |A x| ≤ a)
    (hb : ∀ x i, |A (x + Pi.single i 1) - A x| ≤ b)
    (hsupp : ∀ x, A x * u x ≠ 0 → x ∈ V ∧ x ∈ openInteriorD ω V) :
    -(∑' x, g x * (A x * u x)) ≤ B * (Λ ^ ((1 : ℝ) / 2 - 1 / d) * (a * Real.sqrt (∑' x, u x ^ 2)) +
      Real.sqrt Λ * (3 * Real.sqrt d * a * Real.sqrt (openEnergyD ω u) +
        3 * d * b * Real.sqrt (∑' x, u x ^ 2))) := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := by
    have hd1 : 0 < d := by omega
    exact (abs_nonneg _).trans (hb 0 ⟨0, hd1⟩)
  set φ : Vertex d → ℝ := fun x => A x * u x with hφdef
  have hφ2 : ∀ x, φ x ^ 2 ≤ a ^ 2 * u x ^ 2 := fun x => by
    have hA : A x ^ 2 ≤ a ^ 2 := by
      have := ha x
      nlinarith [abs_nonneg (A x), sq_abs (A x)]
    rw [hφdef, mul_pow]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  have hφs : Summable fun x => φ x ^ 2 :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) hφ2 (hu.mul_left _)
  have hU0 : 0 ≤ ∑' x, u x ^ 2 := tsum_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ openEnergyD ω u := openEnergyD_nonneg ω u
  have hsumV : ∑' x, g x * (A x * u x) = ∑ x ∈ V, g x * φ x := by
    refine tsum_eq_sum fun x hx => ?_
    by_cases h0 : A x * u x = 0
    · rw [h0, mul_zero]
    · exact absurd (hsupp x h0).1 hx
  have hbd : ∀ x ∈ V, x ∉ openInteriorD ω V → φ x = 0 := by
    intro x _ hx
    by_contra h0
    exact hx (hsupp x h0).2
  have hΛ0 : 0 ≤ Λ := le_trans (Nat.cast_nonneg _) hΛ
  have hmain := neg_sum_le_of_weakNormLeD hd h hB hΛ hbd
  rw [hsumV]
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hB)
  -- the `L²` part
  have hL2 : Real.sqrt (∑ x ∈ V, φ x ^ 2) ≤ a * Real.sqrt (∑' x, u x ^ 2) := by
    have h1 : ∑ x ∈ V, φ x ^ 2 ≤ a ^ 2 * ∑' x, u x ^ 2 :=
      (hφs.sum_le_tsum V fun x _ => sq_nonneg _).trans
        ((Summable.tsum_le_tsum hφ2 hφs (hu.mul_left _)).trans (le_of_eq tsum_mul_left))
    calc Real.sqrt (∑ x ∈ V, φ x ^ 2) ≤ Real.sqrt (a ^ 2 * ∑' x, u x ^ 2) := Real.sqrt_le_sqrt h1
      _ = a * Real.sqrt (∑' x, u x ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0]
  -- the gradient part
  have hedge : ∀ x (i : Fin d), openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 ≤
      2 * a ^ 2 * (openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2) + 2 * b ^ 2 * u x ^ 2 := by
    intro x i
    have hc0 := openCondD_nonneg ω i x
    have hc1 := openCondD_le_one ω i x
    have e : φ (x + Pi.single i 1) - φ x =
        A (x + Pi.single i 1) * (u (x + Pi.single i 1) - u x) +
          (A (x + Pi.single i 1) - A x) * u x := by
      rw [hφdef]
      ring
    have hA2 : A (x + Pi.single i 1) ^ 2 ≤ a ^ 2 := by
      have := ha (x + Pi.single i 1)
      nlinarith [abs_nonneg (A (x + Pi.single i 1)), sq_abs (A (x + Pi.single i 1))]
    have hB2 : (A (x + Pi.single i 1) - A x) ^ 2 ≤ b ^ 2 := by
      have := hb x i
      nlinarith [abs_nonneg (A (x + Pi.single i 1) - A x), sq_abs (A (x + Pi.single i 1) - A x)]
    have hsq : (φ (x + Pi.single i 1) - φ x) ^ 2 ≤
        2 * (A (x + Pi.single i 1) ^ 2 * (u (x + Pi.single i 1) - u x) ^ 2) +
          2 * ((A (x + Pi.single i 1) - A x) ^ 2 * u x ^ 2) := by
      rw [e]
      nlinarith [sq_nonneg (A (x + Pi.single i 1) * (u (x + Pi.single i 1) - u x) -
        (A (x + Pi.single i 1) - A x) * u x)]
    have h1 : A (x + Pi.single i 1) ^ 2 * (u (x + Pi.single i 1) - u x) ^ 2 ≤
        a ^ 2 * (u (x + Pi.single i 1) - u x) ^ 2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
    have h2 : (A (x + Pi.single i 1) - A x) ^ 2 * u x ^ 2 ≤ b ^ 2 * u x ^ 2 :=
      mul_le_mul_of_nonneg_right hB2 (sq_nonneg _)
    have h3 : openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 ≤
        openCondD ω i x * (2 * (a ^ 2 * (u (x + Pi.single i 1) - u x) ^ 2) +
          2 * (b ^ 2 * u x ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : openCondD ω i x * (2 * (b ^ 2 * u x ^ 2)) ≤ 2 * b ^ 2 * u x ^ 2 := by
      have : 0 ≤ 2 * (b ^ 2 * u x ^ 2) := by positivity
      nlinarith
    nlinarith
  have hsF := summable_edge_sqD ω hφs
  have hsB := summable_edge_sq_backD ω hφs
  have hsU := summable_edge_sqD ω hu
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgrad : ∑ x ∈ V, openGradNormD ω V φ x ^ 2 ≤
      8 * d * a ^ 2 * openEnergyD ω u + 8 * d ^ 2 * b ^ 2 * ∑' x, u x ^ 2 := by
    have h1 : ∑ x ∈ V, openGradNormD ω V φ x ^ 2 ≤ ∑ x ∈ V, 2 * d * ∑ i,
        (openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 +
          openCondD ω i (x - Pi.single i 1) * (φ (x - Pi.single i 1) - φ x) ^ 2) :=
      Finset.sum_le_sum fun x _ => openGradNormD_sq_le ω V φ x
    have hs2 : Summable fun x => 2 * (d : ℝ) * ∑ i,
        (openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 +
          openCondD ω i (x - Pi.single i 1) * (φ (x - Pi.single i 1) - φ x) ^ 2) := by
      refine (hsF.add hsB).mul_left (2 * (d : ℝ)) |>.congr fun x => ?_
      rw [Finset.sum_add_distrib]
    have h2 := hs2.sum_le_tsum V fun x _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
        add_nonneg (mul_nonneg (openCondD_nonneg ω i _) (sq_nonneg _))
          (mul_nonneg (openCondD_nonneg ω i _) (sq_nonneg _)))
    have e2 : ∑' x, 2 * (d : ℝ) * ∑ i,
        (openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 +
          openCondD ω i (x - Pi.single i 1) * (φ (x - Pi.single i 1) - φ x) ^ 2) =
        4 * d * ∑' x, ∑ i, openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 := by
      rw [tsum_mul_left]
      simp only [Finset.sum_add_distrib]
      rw [hsF.tsum_add hsB, tsum_edge_sq_back_eqD ω hφs]
      ring
    have h3 : ∑' x, ∑ i, openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 ≤
        2 * a ^ 2 * openEnergyD ω u + 2 * d * b ^ 2 * ∑' x, u x ^ 2 := by
      have hpt : ∀ x, ∑ i, openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2 ≤
          2 * a ^ 2 * ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 +
            2 * d * b ^ 2 * u x ^ 2 := by
        intro x
        calc ∑ i, openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2
            ≤ ∑ i, (2 * a ^ 2 * (openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2) +
                2 * b ^ 2 * u x ^ 2) := Finset.sum_le_sum fun i _ => hedge x i
          _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
              ring
      have hsR : Summable fun x => 2 * a ^ 2 * ∑ i,
          openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 + 2 * d * b ^ 2 * u x ^ 2 :=
        (hsU.mul_left _).add (hu.mul_left _)
      calc ∑' x, ∑ i, openCondD ω i x * (φ (x + Pi.single i 1) - φ x) ^ 2
          ≤ ∑' x, (2 * a ^ 2 * ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) ^ 2 +
              2 * d * b ^ 2 * u x ^ 2) := Summable.tsum_le_tsum hpt hsF hsR
        _ = 2 * a ^ 2 * openEnergyD ω u + 2 * d * b ^ 2 * ∑' x, u x ^ 2 := by
            rw [(hsU.mul_left _).tsum_add (hu.mul_left _), tsum_mul_left, tsum_mul_left]
            rfl
    calc ∑ x ∈ V, openGradNormD ω V φ x ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := e2
      _ ≤ 4 * d * (2 * a ^ 2 * openEnergyD ω u + 2 * d * b ^ 2 * ∑' x, u x ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 8 * d * a ^ 2 * openEnergyD ω u + 8 * d ^ 2 * b ^ 2 * ∑' x, u x ^ 2 := by ring
  have hsqrt : Real.sqrt (∑ x ∈ V, openGradNormD ω V φ x ^ 2) ≤
      3 * Real.sqrt d * a * Real.sqrt (openEnergyD ω u) +
        3 * d * b * Real.sqrt (∑' x, u x ^ 2) := by
    refine (Real.sqrt_le_sqrt hgrad).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    have hsE := Real.sq_sqrt hE0
    have hsU2 := Real.sq_sqrt hU0
    have hsd := Real.sq_sqrt hd0
    have p0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have p1 : 0 ≤ Real.sqrt (openEnergyD ω u) := Real.sqrt_nonneg _
    have p2 : 0 ≤ Real.sqrt (∑' x, u x ^ 2) := Real.sqrt_nonneg _
    have e : (3 * Real.sqrt d * a * Real.sqrt (openEnergyD ω u) +
        3 * d * b * Real.sqrt (∑' x, u x ^ 2)) ^ 2 =
        9 * d * a ^ 2 * openEnergyD ω u + 9 * d ^ 2 * b ^ 2 * ∑' x, u x ^ 2 +
          18 * (Real.sqrt d * d) * (a * b) *
            (Real.sqrt (openEnergyD ω u) * Real.sqrt (∑' x, u x ^ 2)) := by
      have : (3 * Real.sqrt d * a * Real.sqrt (openEnergyD ω u) +
          3 * d * b * Real.sqrt (∑' x, u x ^ 2)) ^ 2 =
          9 * Real.sqrt d ^ 2 * a ^ 2 * Real.sqrt (openEnergyD ω u) ^ 2 +
            9 * d ^ 2 * b ^ 2 * Real.sqrt (∑' x, u x ^ 2) ^ 2 +
            18 * (Real.sqrt d * d) * (a * b) *
              (Real.sqrt (openEnergyD ω u) * Real.sqrt (∑' x, u x ^ 2)) := by ring
      rw [this, hsE, hsU2, hsd]
    rw [e]
    have hc : 0 ≤ 18 * (Real.sqrt d * d) * (a * b) *
        (Real.sqrt (openEnergyD ω u) * Real.sqrt (∑' x, u x ^ 2)) := by positivity
    have hd1 : 8 * d * a ^ 2 * openEnergyD ω u ≤ 9 * d * a ^ 2 * openEnergyD ω u := by
      have : 0 ≤ d * a ^ 2 * openEnergyD ω u := by positivity
      linarith
    have hd2 : 8 * d ^ 2 * b ^ 2 * ∑' x, u x ^ 2 ≤ 9 * d ^ 2 * b ^ 2 * ∑' x, u x ^ 2 := by
      have : 0 ≤ (d : ℝ) ^ 2 * b ^ 2 * ∑' x, u x ^ 2 := by positivity
      linarith
    linarith
  have hΛs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hΛp : 0 ≤ Λ ^ ((1 : ℝ) / 2 - 1 / d) := Real.rpow_nonneg hΛ0 _
  exact add_le_add (mul_le_mul_of_nonneg_left hL2 hΛp) (mul_le_mul_of_nonneg_left hsqrt hΛs)

end Rigidity.Green.GeneralDim
