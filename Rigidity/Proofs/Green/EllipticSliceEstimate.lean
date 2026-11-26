import Rigidity.Proofs.Green.HarmonicReplacement

/-!
# The elliptic oscillation estimate for functions with bounded Laplacian

Let `G` be a locally finite graph with degrees at most `D > 0` and `B : ℝ → Finset V` an
increasing family of finite sets ("balls"), with interiors `int B_ρ = {x ∈ B_ρ : every neighbour of
x lies in B_ρ}` from which the outside is reachable. Write `‖f‖_S = (|S|^{-1} Σ_{x ∈ S} f(x)²)^{1/2}`
(`nL2`). Assume

* the order-zero estimate above a scale `X`: every `u` harmonic on `int B_{R'}`, `R' ≥ 2X`, has a
  constant `c` with `‖u - c‖_{B_r} ≤ C₀ (r/R') ‖u‖_{B_{R'}}` for `X ≤ r ≤ R'/2`;
* the heat kernel bound `Σ_{w ∈ int B_ρ} p_{Aρ²}(z, w) ≤ 1/2` for `z ∈ int B_ρ`, `ρ ≥ ρ₀`.

Then for `X ≤ r`, `ρ₀ ≤ 2r`, `2r ≤ R`, and `v` with `|v| ≤ U` on `B_R` and `|Δv| ≤ F` on `int B_R`,

  `‖v - c‖_{B_r} ≤ (C₀ + (10 C₀ + 32) A) r (U/R + R F)`  for some constant `c`

(`exists_nL2_sub_le_of_laplacian`). This is the elliptic estimate for time slices of the heat
equation in the proof of Theorem 3 of Dario–Gu given here. Proof: with `ρ_k = R/2^k` down to
`ρ_K ∈ [2r, 4r)`, let `h_k` be the harmonic replacement on `int B_{ρ_k}` of `v` truncated to
`B_{ρ_k}`. The exit-time bound gives `|v - h_k| ≤ 2Aρ_k² F` on `B_{ρ_k}`; the order-zero estimate
applies to `h_0` (bounded by `U`) and to each difference `h_{k+1} - h_k` (harmonic on
`int B_{ρ_{k+1}}`, bounded there by `10 A ρ_{k+1}² F`), and the contributions
`10 C₀ A r ρ_{k+1} F` sum to at most `10 C₀ A r R F`.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-! ### Normalized `L²` norms on finite sets -/

/-- `‖f‖_S = (|S|^{-1} Σ_{x ∈ S} f(x)²)^{1/2}`. -/
noncomputable def nL2 (S : Finset V) (f : V → ℝ) : ℝ :=
  Real.sqrt ((∑ x ∈ S, f x ^ 2) / S.card)

theorem nL2_nonneg (S : Finset V) (f : V → ℝ) : 0 ≤ nL2 S f := Real.sqrt_nonneg _

theorem nL2_congr {S : Finset V} {f g : V → ℝ} (h : ∀ x ∈ S, f x = g x) : nL2 S f = nL2 S g := by
  unfold nL2
  rw [Finset.sum_congr rfl fun x hx => by rw [h x hx]]

theorem nL2_le_of_abs_le {S : Finset V} {f : V → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ S, |f x| ≤ M) : nL2 S f ≤ M := by
  unfold nL2
  rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq hM).symm]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; positivity
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ x ∈ S, f x ^ 2 ≤ ∑ x ∈ S, M ^ 2 := Finset.sum_le_sum fun x hx => by
          have := h x hx
          nlinarith [sq_abs (f x), abs_nonneg (f x)]
      _ = M ^ 2 * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The triangle inequality for `‖·‖_S`. -/
theorem nL2_add_le (S : Finset V) {f g k : V → ℝ} (hk : ∀ x ∈ S, k x = f x + g x) :
    nL2 S k ≤ nL2 S f + nL2 S g := by
  unfold nL2
  have ha : 0 ≤ ∑ x ∈ S, f x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ x ∈ S, g x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S f g
  have e1 : ∑ x ∈ S, k x ^ 2 = ∑ x ∈ S, (f x + g x) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by rw [hk x hx]
  have e2 : ∑ x ∈ S, (f x + g x) ^ 2 =
      ∑ x ∈ S, f x ^ 2 + 2 * ∑ x ∈ S, f x * g x + ∑ x ∈ S, g x ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hsum : ∑ x ∈ S, k x ^ 2 ≤
      (Real.sqrt (∑ x ∈ S, f x ^ 2) + Real.sqrt (∑ x ∈ S, g x ^ 2)) ^ 2 := by
    rw [e1, e2, add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [hcs]
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  calc Real.sqrt ((∑ x ∈ S, k x ^ 2) / S.card)
      ≤ Real.sqrt ((Real.sqrt (∑ x ∈ S, f x ^ 2) + Real.sqrt (∑ x ∈ S, g x ^ 2)) ^ 2 / S.card) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum hn)
    _ = (Real.sqrt (∑ x ∈ S, f x ^ 2) + Real.sqrt (∑ x ∈ S, g x ^ 2)) / Real.sqrt S.card := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
    _ = Real.sqrt ((∑ x ∈ S, f x ^ 2) / S.card) + Real.sqrt ((∑ x ∈ S, g x ^ 2) / S.card) := by
        rw [add_div, Real.sqrt_div ha, Real.sqrt_div hb]

theorem nL2_le_add_of_abs_le (S : Finset V) {f g : V → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ S, |f x - g x| ≤ M) : nL2 S f ≤ nL2 S g + M :=
  (nL2_add_le S (f := g) (g := fun x => f x - g x) fun x _ => by ring).trans
    (add_le_add le_rfl (nL2_le_of_abs_le hM h))

/-! ### Interiors and truncations -/

variable (G) in
/-- The interior `{x ∈ S : every neighbour of x lies in S}`. -/
noncomputable def interiorOf (S : Finset V) : Finset V :=
  S.filter fun x => ∀ y, G.Adj x y → y ∈ S

omit [G.LocallyFinite] in
theorem mem_interiorOf {S : Finset V} {x : V} :
    x ∈ interiorOf G S ↔ x ∈ S ∧ ∀ y, G.Adj x y → y ∈ S := by
  unfold interiorOf
  rw [Finset.mem_filter]

omit [G.LocallyFinite] in
theorem interiorOf_mono {S S' : Finset V} (h : S ⊆ S') : interiorOf G S ⊆ interiorOf G S' :=
  fun x hx => by
    rw [mem_interiorOf] at hx ⊢
    exact ⟨h hx.1, fun y hy => h (hx.2 y hy)⟩

omit [G.LocallyFinite] in
theorem interiorOf_subset (S : Finset V) : interiorOf G S ⊆ S := fun _ hx => (mem_interiorOf.1 hx).1

/-- `v` on `S` and `0` off `S`. -/
noncomputable def truncate (S : Finset V) (v : V → ℝ) : V → ℝ := fun x => if x ∈ S then v x else 0

theorem truncate_of_mem {S : Finset V} {v : V → ℝ} {x : V} (hx : x ∈ S) : truncate S v x = v x :=
  if_pos hx

theorem abs_truncate_le {S : Finset V} {v : V → ℝ} {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ x ∈ S, |v x| ≤ U) (x : V) : |truncate S v x| ≤ U := by
  unfold truncate
  split_ifs with hx
  · exact hU x hx
  · rw [abs_zero]; exact hU0

theorem laplacian_truncate {S : Finset V} (v : V → ℝ) {x : V} (hx : x ∈ interiorOf G S) :
    LatticeProb.Graph.laplacian G (truncate S v) x = LatticeProb.Graph.laplacian G v x := by
  rw [mem_interiorOf] at hx
  unfold LatticeProb.Graph.laplacian
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [truncate_of_mem (hx.2 y ((G.mem_neighborFinset x y).1 hy)), truncate_of_mem hx.1]

/-! ### The estimate -/

/-- **The elliptic oscillation estimate.** -/
theorem exists_nL2_sub_le_of_laplacian (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D)
    {B : ℝ → Finset V} (hmono : ∀ ρ ρ', ρ ≤ ρ' → B ρ ⊆ B ρ')
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible G (interiorOf G (B ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : V → ℝ,
      (∀ x ∈ interiorOf G (B R'), LatticeProb.Graph.laplacian G u x = 0) →
        ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
          nL2 (B r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (B R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf G (B ρ),
      ∑ w ∈ interiorOf G (B ρ), vsrwHeat G D (A * ρ ^ 2) z w ≤ 1 / 2)
    {r R U F : ℝ} (hXr : X ≤ r) (hr : 0 < r) (hρ₀ : ρ₀ ≤ 2 * r) (hrR : 2 * r ≤ R)
    (hU0 : 0 ≤ U) (hF0 : 0 ≤ F) {v : V → ℝ} (hU : ∀ x ∈ B R, |v x| ≤ U)
    (hF : ∀ x ∈ interiorOf G (B R), |LatticeProb.Graph.laplacian G v x| ≤ F) :
    ∃ c : ℝ, nL2 (B r) (fun x => v x - c) ≤ (C₀ + (10 * C₀ + 32) * A) * r * (U / R + R * F) := by
  have hR : 0 < R := by linarith
  -- harmonic replacements and exit-time functions at every radius
  have hex : ∀ ρ : ℝ, ∃ h : V → ℝ,
      (∀ x ∈ interiorOf G (B ρ), LatticeProb.Graph.laplacian G h x = 0) ∧
        ∀ x, x ∉ interiorOf G (B ρ) → h x = truncate (B ρ) v x :=
    fun ρ => exists_dirichlet (hacc ρ) _
  choose h hh hgh using hex
  have hee : ∀ ρ : ℝ, ∃ e : V → ℝ,
      (∀ x ∈ interiorOf G (B ρ), LatticeProb.Graph.laplacian G e x = -1) ∧
        (∀ x, x ∉ interiorOf G (B ρ) → e x = 0) ∧ ∀ x, 0 ≤ e x :=
    fun ρ => exists_exitFunction (hacc ρ)
  choose e he he0 hnn using hee
  -- the replacement error
  have hF2 : ∀ ρ, ρ₀ ≤ ρ → ρ ≤ R → ∀ x, |truncate (B ρ) v x - h ρ x| ≤ 2 * A * ρ ^ 2 * F := by
    intro ρ hρ₀ρ hρR x
    have hcmp := abs_sub_le_mul_exitFunction (hacc ρ) (hh ρ) (hgh ρ) (F := F)
      (fun y hy => by
        rw [laplacian_truncate v hy]
        exact hF y (interiorOf_mono (hmono ρ R hρR) hy)) (he ρ) (he0 ρ) x
    have hexit := exitFunction_le_two_mul hD hdeg (he ρ) (he0 ρ) (hnn ρ)
      (mul_nonneg hA (sq_nonneg ρ)) (hHK ρ hρ₀ρ) x
    calc |truncate (B ρ) v x - h ρ x| ≤ F * e ρ x := hcmp
      _ ≤ F * (2 * (A * ρ ^ 2)) := mul_le_mul_of_nonneg_left hexit hF0
      _ = 2 * A * ρ ^ 2 * F := by ring
  -- the dyadic radii
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, 2 * r ≤ R / 2 ^ K ∧ R / 2 ^ K < 4 * r := by
    have h1 : (1 : ℝ) ≤ R / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    refine ⟨n, ?_, ?_⟩
    · rw [le_div_iff₀ h2n]
      rw [le_div_iff₀ (by positivity)] at hn1
      linarith
    · rw [div_lt_iff₀ h2n]
      rw [div_lt_iff₀ (by positivity), pow_succ] at hn2
      linarith
  have hρpos : ∀ k : ℕ, 0 < R / 2 ^ k := fun k => by positivity
  have hρR : ∀ k : ℕ, R / 2 ^ k ≤ R := fun k =>
    div_le_self hR.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hρsucc : ∀ k : ℕ, R / 2 ^ (k + 1) = R / 2 ^ k / 2 := fun k => by rw [pow_succ, div_div]
  have hρge : ∀ k : ℕ, k ≤ K → 2 * r ≤ R / 2 ^ k := fun k hk =>
    hK1.trans (div_le_div_of_nonneg_left hR.le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk))
  -- the induction over the dyadic levels
  have hind : ∀ k, k ≤ K → ∃ c : ℝ, nL2 (B r) (fun x => h (R / 2 ^ k) x - c) ≤
      C₀ * (r / R) * U + 10 * C₀ * A * r * F * (R - R / 2 ^ k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, div_one]
      obtain ⟨c, hc⟩ := hOZ R (by linarith) (h R) (hh R)
      refine ⟨c, ?_⟩
      have hhU : nL2 (B R) (h R) ≤ U := nL2_le_of_abs_le hU0 fun x _ =>
        abs_le_of_dirichlet (hacc R) (hh R) (hgh R) (abs_truncate_le hU0 hU) x
      calc nL2 (B r) (fun x => h R x - c) ≤ C₀ * (r / R) * nL2 (B R) (h R) :=
            hc r hXr (by linarith)
        _ ≤ C₀ * (r / R) * U := mul_le_mul_of_nonneg_left hhU (by positivity)
        _ = C₀ * (r / R) * U + 10 * C₀ * A * r * F * (R - R) := by ring
    | succ k ih =>
      intro hk
      obtain ⟨c, hc⟩ := ih (by omega)
      set ρ := R / 2 ^ k with hρdef
      set ρ' := R / 2 ^ (k + 1) with hρ'def
      have hρρ' : ρ = 2 * ρ' := by rw [hρ'def, hρsucc k]; ring
      have hρ'ge : 2 * r ≤ ρ' := hρge (k + 1) hk
      have hρ'pos : 0 < ρ' := hρpos (k + 1)
      have hle : ρ' ≤ ρ := by rw [hρρ']; linarith
      have hsub : interiorOf G (B ρ') ⊆ interiorOf G (B ρ) := interiorOf_mono (hmono ρ' ρ hle)
      obtain ⟨c', hc'⟩ := hOZ ρ' (by linarith) (fun x => h ρ' x - h ρ x) (fun x hx => by
        rw [laplacian_sub_apply, hh ρ' x hx, hh ρ x (hsub hx), sub_zero])
      have hd := hc' r hXr (by linarith)
      have hdsup : nL2 (B ρ') (fun x => h ρ' x - h ρ x) ≤ 10 * A * ρ' ^ 2 * F := by
        refine nL2_le_of_abs_le (by positivity) fun x hx => ?_
        have h1 := hF2 ρ' (hρ₀.trans hρ'ge) (hρR (k + 1)) x
        have h2 := hF2 ρ (hρ₀.trans (hρge k (by omega))) (hρR k) x
        rw [truncate_of_mem hx] at h1
        rw [truncate_of_mem (hmono ρ' ρ hle hx)] at h2
        calc |h ρ' x - h ρ x| = |(v x - h ρ x) - (v x - h ρ' x)| := by ring_nf
          _ ≤ |v x - h ρ x| + |v x - h ρ' x| := abs_sub _ _
          _ ≤ 2 * A * ρ ^ 2 * F + 2 * A * ρ' ^ 2 * F := add_le_add h2 h1
          _ = 10 * A * ρ' ^ 2 * F := by rw [hρρ']; ring
      refine ⟨c + c', ?_⟩
      have htri := nL2_add_le (B r) (f := fun x => h ρ x - c)
        (g := fun x => (h ρ' x - h ρ x) - c') (k := fun x => h ρ' x - (c + c'))
        fun x _ => by ring
      calc nL2 (B r) (fun x => h ρ' x - (c + c'))
          ≤ nL2 (B r) (fun x => h ρ x - c) + nL2 (B r) (fun x => (h ρ' x - h ρ x) - c') := htri
        _ ≤ (C₀ * (r / R) * U + 10 * C₀ * A * r * F * (R - ρ)) +
            C₀ * (r / ρ') * (10 * A * ρ' ^ 2 * F) :=
          add_le_add hc (hd.trans (mul_le_mul_of_nonneg_left hdsup (by positivity)))
        _ = C₀ * (r / R) * U + 10 * C₀ * A * r * F * (R - ρ') := by
          rw [hρρ']
          field_simp
          ring
  -- the last step
  obtain ⟨c, hc⟩ := hind K le_rfl
  refine ⟨c, ?_⟩
  set ρ := R / 2 ^ K with hρdef
  have hlast : nL2 (B r) (fun x => v x - c) ≤ nL2 (B r) (fun x => h ρ x - c) +
      2 * A * ρ ^ 2 * F := by
    refine nL2_le_add_of_abs_le (B r) (by positivity) fun x hx => ?_
    have h1 := hF2 ρ (hρ₀.trans hK1) (hρR K) x
    rw [truncate_of_mem (hmono r ρ (by linarith) hx)] at h1
    calc |v x - c - (h ρ x - c)| = |v x - h ρ x| := by ring_nf
      _ ≤ _ := h1
  have hρ2 : ρ ^ 2 ≤ 16 * r ^ 2 := by nlinarith [hρpos K]
  have hrR' : r ≤ R := by linarith
  have hρ0 : 0 ≤ ρ := (hρpos K).le
  have hUR : 0 ≤ U / R := div_nonneg hU0 hR.le
  calc nL2 (B r) (fun x => v x - c)
      ≤ C₀ * (r / R) * U + 10 * C₀ * A * r * F * (R - ρ) + 2 * A * ρ ^ 2 * F :=
        hlast.trans (add_le_add hc le_rfl)
    _ ≤ C₀ * r * (U / R) + 10 * C₀ * A * r * F * R + 32 * A * r * R * F := by
        have e1 : C₀ * (r / R) * U = C₀ * r * (U / R) := by ring
        have e2 : 10 * C₀ * A * r * F * (R - ρ) ≤ 10 * C₀ * A * r * F * R :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have e3 : 2 * A * ρ ^ 2 * F ≤ 32 * A * r * R * F := by
          have : ρ ^ 2 ≤ 16 * (r * R) := hρ2.trans (by nlinarith)
          have hAF : 0 ≤ 2 * A * F := by positivity
          nlinarith
        linarith
    _ ≤ (C₀ + (10 * C₀ + 32) * A) * r * (U / R + R * F) := by
        have h1 : 0 ≤ (10 * C₀ + 32) * A * r * (U / R) := by positivity
        have h2 : 0 ≤ C₀ * r * (R * F) := by positivity
        nlinarith

end Rigidity.Green
