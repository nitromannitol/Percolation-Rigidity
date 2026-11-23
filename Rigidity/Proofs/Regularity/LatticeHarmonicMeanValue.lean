import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# An `ℓ^∞`–`ℓ¹` bound for lattice harmonic functions on `ℤ²`

For `g` harmonic on the box `Q_{2L}(z)` of `ℤ²`, `L ≥ 64`,
`max_{Q_L(z)} |g| ≤ C L^{-2} ∑_{Q_{2L}(z)} |g|` (`abs_le_sum_abs_of_latticeHarmonic`). The interior
bound `sq_le_of_latticeHarmonic` on a box `Q_{32h}(x₀)` gives
`g(x₀)² ≤ C₀ h^{-2} B S` with `B` a bound for `|g|` on the larger box and `S = ∑ |g|`, hence
`|g(x₀)| ≤ B / 8 + 2 C₀ h^{-2} S` (`abs_le_of_latticeHarmonic_step`); along the boxes
`Q_{j_k}(z)`, `j_k = L + 32 ∑_{i < k} h_i`, `h_k = ⌊L / (64 · 2^k)⌋`, the maxima `a_k` satisfy
`a_k ≤ a_{k+1} / 8 + b_k`, and the absorption (`le_of_eighth_step`) over `log₂(L / 64) + 1` steps
gives the bound, the factor `8^{-k}` beating the growth `4^k` of `h_k^{-2}`. On the balls of `ℤ²`:
`‖g‖_{L̲²(B_ρ(z))} ≤ C ρ^{-2} ∑_{B_{4ρ}(z)} |g|` for `g` harmonic on `B_{4ρ}(z)`
(`componentBallL2_le_sum_abs_of_latticeHarmonic`), the bound used to pass from `ℓ¹` to `ℓ²` in the
proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation

theorem mem_supBox_self (z : Fin 2 → ℤ) (h : ℕ) : z ∈ supBox z h := by
  simp only [supBox, Fintype.mem_piFinset, mem_Icc]
  intro i; constructor <;> omega

theorem supBox_subset_supBox {z x₀ : Fin 2 → ℤ} {j h L : ℕ} (hx₀ : x₀ ∈ supBox z j)
    (hjL : j + h ≤ L) : supBox x₀ h ⊆ supBox z L := by
  intro y hy
  simp only [supBox, Fintype.mem_piFinset, mem_Icc] at hy hx₀ ⊢
  intro i
  have h1 := hy i
  have h2 := hx₀ i
  constructor <;> omega

/-- **One absorption step.** -/
theorem abs_le_of_latticeHarmonic_step (g : (Fin 2 → ℤ) → ℝ) (z : Fin 2 → ℤ) {j h L : ℕ}
    (hh : 0 < h) (hjL : j + 32 * h ≤ L)
    (hg : ∀ x ∈ supBox z L, latticeLaplacian g x = 0) {B : ℝ}
    (hB : ∀ y ∈ supBox z (j + 32 * h), |g y| ≤ B) {x₀ : Fin 2 → ℤ} (hx₀ : x₀ ∈ supBox z j) :
    |g x₀| ≤ B / 8 + 2 * 262144 / (h : ℝ) ^ 2 * ∑ y ∈ supBox z L, |g y| := by
  have hsub : supBox x₀ (32 * h) ⊆ supBox z (j + 32 * h) :=
    supBox_subset_supBox hx₀ le_rfl
  have hsubL : supBox x₀ (32 * h) ⊆ supBox z L := supBox_subset_supBox hx₀ hjL
  have e32 : (4 : ℕ) ^ 2 * (2 * h) = 32 * h := by ring
  have h1 := sq_le_of_latticeHarmonic (d := 2) g x₀ hh
    (by rw [e32]; exact fun x hx => hg x (hsubL hx)) (mem_supBox_self x₀ h)
  rw [e32] at h1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x₀ (hsub (mem_supBox_self x₀ _)))
  set S := ∑ y ∈ supBox z L, |g y| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hsq : ∑ x ∈ supBox x₀ (32 * h), g x ^ 2 ≤ B * S := by
    calc ∑ x ∈ supBox x₀ (32 * h), g x ^ 2 = ∑ x ∈ supBox x₀ (32 * h), |g x| * |g x| :=
          sum_congr rfl fun x _ => by rw [← sq, sq_abs]
      _ ≤ ∑ x ∈ supBox x₀ (32 * h), B * |g x| :=
          sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (hB x (hsub hx)) (abs_nonneg _)
      _ = B * ∑ x ∈ supBox x₀ (32 * h), |g x| := (mul_sum _ _ _).symm
      _ ≤ B * S := mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hsubL fun _ _ _ => abs_nonneg _) hB0
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : (4 : ℝ) ^ 2 * (64 * ((2 : ℕ) : ℝ)) ^ 2 / ((h : ℝ) + 1) ^ 2 ≤ 262144 / (h : ℝ) ^ 2 := by
    rw [show (4 : ℝ) ^ 2 * (64 * ((2 : ℕ) : ℝ)) ^ 2 = 262144 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hh'.le (by linarith) 2)
  have h2 : g x₀ ^ 2 ≤ 262144 / (h : ℝ) ^ 2 * (B * S) :=
    h1.trans (mul_le_mul hc hsq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
  set a := B / 8 with ha
  set b := 2 * 262144 / (h : ℝ) ^ 2 * S with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hab : 262144 / (h : ℝ) ^ 2 * (B * S) = 4 * a * b := by
    rw [ha, hb]; field_simp; ring
  have hsq' : |g x₀| ^ 2 ≤ (a + b) ^ 2 := by
    rw [sq_abs]; nlinarith [sq_nonneg (a - b)]
  nlinarith [abs_nonneg (g x₀)]

/-- **Absorption.** If `a_k ≤ a_{k+1} / 8 + b_k` for `k < n`, then
`a_0 ≤ a_n / 8^n + ∑_{k < n} b_k / 8^k`. -/
theorem le_of_eighth_step {a b : ℕ → ℝ} (n : ℕ) (h : ∀ k < n, a k ≤ a (k + 1) / 8 + b k) :
    a 0 ≤ a n / 8 ^ n + ∑ k ∈ range n, b k / 8 ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih fun k hk => h k (by omega)
    have h2 := h n (by omega)
    have h8 : (0 : ℝ) < 8 ^ n := by positivity
    have h3 : a n / 8 ^ n ≤ a (n + 1) / 8 ^ (n + 1) + b n / 8 ^ n := by
      have := div_le_div_of_nonneg_right h2 h8.le
      rw [add_div, div_div, ← pow_succ'] at this
      exact this
    rw [sum_range_succ]
    linarith

/-- **`ℓ^∞`–`ℓ¹` bound for lattice harmonic functions on the boxes of `ℤ²`.** -/
theorem abs_le_sum_abs_of_latticeHarmonic (g : (Fin 2 → ℤ) → ℝ) (z : Fin 2 → ℤ) {L : ℕ}
    (hL : 64 ≤ L) (hg : ∀ x ∈ supBox z (2 * L), latticeLaplacian g x = 0) :
    ∀ x ∈ supBox z L, |g x| ≤ 17179873280 / (L : ℝ) ^ 2 * ∑ y ∈ supBox z (2 * L), |g y| := by
  classical
  set S := ∑ y ∈ supBox z (2 * L), |g y| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hL' : (64 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  set K := Nat.log 2 (L / 64) with hK
  have hL64 : 1 ≤ L / 64 := (Nat.one_le_div_iff (by norm_num)).2 hL
  have hpowK : 2 ^ K ≤ L / 64 := Nat.pow_log_le_self 2 (by omega)
  have hpowK1 : L / 64 < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set hs : ℕ → ℕ := fun k => L / (64 * 2 ^ k) with hhs
  have hs_pos : ∀ k ≤ K, 0 < hs k := by
    intro k hk
    have : 64 * 2 ^ k ≤ L := by
      have h1 : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hk
      have h2 := Nat.mul_le_of_le_div 64 _ _ hpowK
      nlinarith
    exact Nat.div_pos this (by positivity)
  have hs_le : ∀ k, (hs k : ℝ) ≤ L / (64 * 2 ^ k) := by
    intro k
    have := Nat.cast_div_le (m := L) (n := 64 * 2 ^ k) (α := ℝ)
    simpa [hhs] using this
  have hs_ge : ∀ k ≤ K, (L : ℝ) / (128 * 2 ^ k) ≤ hs k := by
    intro k hk
    have hpos := hs_pos k hk
    have hlt : L < (hs k + 1) * (64 * 2 ^ k) := by
      have := Nat.lt_succ_iff.2 (le_refl (L / (64 * 2 ^ k)))
      exact (Nat.div_lt_iff_lt_mul (by positivity)).1 this
    have hlt' : (L : ℝ) < ((hs k : ℝ) + 1) * (64 * 2 ^ k) := by exact_mod_cast hlt
    have h1 : (1 : ℝ) ≤ hs k := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  set js : ℕ → ℕ := fun k => L + 32 * ∑ i ∈ range k, hs i with hjs
  have hjs_succ : ∀ k, js (k + 1) = js k + 32 * hs k := by
    intro k; simp only [hjs, sum_range_succ]; ring
  have hjs_le : ∀ k, js k ≤ 2 * L := by
    intro k
    have hsum : ((∑ i ∈ range k, hs i : ℕ) : ℝ) ≤ L / 32 := by
      push_cast
      calc ∑ i ∈ range k, (hs i : ℝ) ≤ ∑ i ∈ range k, (L : ℝ) / 64 * (1 / 2) ^ i :=
            sum_le_sum fun i _ => (hs_le i).trans (le_of_eq (by rw [one_div_pow]; field_simp))
        _ = (L : ℝ) / 64 * ∑ i ∈ range k, (1 / 2 : ℝ) ^ i := (mul_sum _ _ _).symm
        _ ≤ (L : ℝ) / 64 * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have := sum_geometric_two_le k
            simpa [one_div] using this
        _ = L / 32 := by ring
    have : ((js k : ℕ) : ℝ) ≤ 2 * L := by
      simp only [hjs]; push_cast at hsum ⊢; linarith
    exact_mod_cast this
  -- the maxima of `|g|` on the boxes
  set as : ℕ → ℝ := fun k => (supBox z (js k)).sup' ⟨z, mem_supBox_self z _⟩ fun y => |g y|
    with has
  have has_ge : ∀ k, ∀ y ∈ supBox z (js k), |g y| ≤ as k := fun k y hy =>
    le_sup' (fun y => |g y|) hy
  have hstep : ∀ k < K + 1, as k ≤ as (k + 1) / 8 + 2 * 262144 / (hs k : ℝ) ^ 2 * S := by
    intro k hk
    apply sup'_le
    intro x hx
    have hjL : js k + 32 * hs k ≤ 2 * L := by rw [← hjs_succ]; exact hjs_le _
    have := abs_le_of_latticeHarmonic_step g z (hs_pos k (by omega)) hjL hg
      (B := as (k + 1)) (fun y hy => has_ge (k + 1) y (by rw [hjs_succ]; exact hy)) hx
    exact this
  have habs := le_of_eighth_step (a := as) (b := fun k => 2 * 262144 / (hs k : ℝ) ^ 2 * S)
    (K + 1) hstep
  -- the last maximum
  have hlast : as (K + 1) ≤ S := by
    apply sup'_le
    intro y hy
    have hy' : y ∈ supBox z (2 * L) := by
      simp only [supBox, Fintype.mem_piFinset, mem_Icc] at hy ⊢
      intro i; have := hy i; have := hjs_le (K + 1); constructor <;> omega
    exact single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) hy'
  have h8 : ((L : ℝ) / 64) ^ 2 ≤ 8 ^ (K + 1) := by
    have h1 : (L : ℝ) / 64 ≤ 2 ^ (K + 1) := by
      have : ((L / 64 : ℕ) : ℝ) < 2 ^ (K + 1) := by exact_mod_cast hpowK1
      have h2 := Nat.cast_div_le (m := L) (n := 64) (α := ℝ)
      have h3 : (L : ℝ) / 64 < ((L / 64 : ℕ) : ℝ) + 1 := by
        have := Nat.lt_div_mul_add (a := L) (b := 64) (by norm_num)
        have h4 : (L : ℝ) < ((L / 64 : ℕ) : ℝ) * 64 + 64 := by exact_mod_cast this
        rw [div_lt_iff₀ (by norm_num)]; linarith
      have h5 : ((L / 64 : ℕ) : ℝ) + 1 ≤ 2 ^ (K + 1) := by
        have : L / 64 + 1 ≤ 2 ^ (K + 1) := hpowK1
        exact_mod_cast this
      linarith
    have h1' : 1 ≤ (L : ℝ) / 64 := by rw [le_div_iff₀ (by norm_num)]; linarith
    calc ((L : ℝ) / 64) ^ 2 ≤ ((L : ℝ) / 64) ^ 3 := pow_le_pow_right₀ h1' (by norm_num)
      _ ≤ (2 ^ (K + 1)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = 8 ^ (K + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hfirst : as (K + 1) / 8 ^ (K + 1) ≤ 4096 / (L : ℝ) ^ 2 * S := by
    have h8pos : (0 : ℝ) < 8 ^ (K + 1) := by positivity
    rw [div_le_iff₀ h8pos]
    calc as (K + 1) ≤ S := hlast
      _ = 4096 / (L : ℝ) ^ 2 * S * ((L : ℝ) / 64) ^ 2 := by field_simp; ring
      _ ≤ 4096 / (L : ℝ) ^ 2 * S * 8 ^ (K + 1) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
  have hsecond : ∑ k ∈ range (K + 1), 2 * 262144 / (hs k : ℝ) ^ 2 * S / 8 ^ k ≤
      4 * 262144 * 16384 / (L : ℝ) ^ 2 * S := by
    have hterm : ∀ k ∈ range (K + 1), 2 * 262144 / (hs k : ℝ) ^ 2 * S / 8 ^ k ≤
        2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * (1 / 2) ^ k := by
      intro k hk
      have hk' : k ≤ K := Nat.lt_succ_iff.1 (mem_range.1 hk)
      have hge := hs_ge k hk'
      have hpos : (0 : ℝ) < (L : ℝ) / (128 * 2 ^ k) := by positivity
      have hsq : 1 / (hs k : ℝ) ^ 2 ≤ 1 / ((L : ℝ) / (128 * 2 ^ k)) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hge 2)
      have e : 1 / ((L : ℝ) / (128 * 2 ^ k)) ^ 2 = 16384 * 4 ^ k / (L : ℝ) ^ 2 := by
        rw [div_pow, mul_pow, one_div_div, show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        norm_num
      rw [e] at hsq
      have e2 : 2 * 262144 / (hs k : ℝ) ^ 2 * S / 8 ^ k =
          2 * 262144 * S / 8 ^ k * (1 / (hs k : ℝ) ^ 2) := by ring
      rw [e2]
      calc 2 * 262144 * S / 8 ^ k * (1 / (hs k : ℝ) ^ 2)
          ≤ 2 * 262144 * S / 8 ^ k * (16384 * 4 ^ k / (L : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * (4 ^ k / 8 ^ k) := by ring
        _ = 2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * (1 / 2) ^ k := by
            rw [← div_pow]; norm_num
    calc ∑ k ∈ range (K + 1), 2 * 262144 / (hs k : ℝ) ^ 2 * S / 8 ^ k
        ≤ ∑ k ∈ range (K + 1), 2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * (1 / 2) ^ k :=
          sum_le_sum hterm
      _ = 2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * ∑ k ∈ range (K + 1), (1 / 2 : ℝ) ^ k :=
          (mul_sum _ _ _).symm
      _ ≤ 2 * 262144 * 16384 / (L : ℝ) ^ 2 * S * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := sum_geometric_two_le (K + 1)
          simpa [one_div] using this
      _ = 4 * 262144 * 16384 / (L : ℝ) ^ 2 * S := by ring
  intro x hx
  have hx' : x ∈ supBox z (js 0) := by simpa [hjs] using hx
  have h0 := has_ge 0 x hx'
  have : as 0 ≤ 17179873280 / (L : ℝ) ^ 2 * S := by
    refine habs.trans ?_
    have e : (17179873280 : ℝ) / (L : ℝ) ^ 2 * S =
        4096 / (L : ℝ) ^ 2 * S + 4 * 262144 * 16384 / (L : ℝ) ^ 2 * S := by ring
    rw [e]
    exact add_le_add hfirst hsecond
  exact h0.trans this

/-- **`ℓ²`–`ℓ¹` bound for lattice harmonic functions on the balls of `ℤ²`**: for `g` harmonic
on `B_{4ρ}(z)`, `ρ ≥ 64`, `‖g‖_{L̲²(B_ρ(z))} ≤ C ρ^{-2} ∑_{B_{4ρ}(z)} |g|`. -/
theorem componentBallL2_le_sum_abs_of_latticeHarmonic (g : (Fin 2 → ℤ) → ℝ) (z : Vertex 2)
    {ρ : ℝ} (hρ : 64 ≤ ρ)
    (hg : ∀ y : Fin 2 → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) <
      4 * ρ → latticeLaplacian g y = 0) :
    componentBallL2 (latticeComponent 2) z ρ (fun x => g x.val) ≤
      17179873280 / ρ ^ 2 * ∑ x ∈ componentEuclideanBall (latticeComponent 2) z (4 * ρ),
        |g x.val| := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set L := ⌈ρ⌉₊ with hLdef
  have hρL : ρ ≤ L := Nat.le_ceil ρ
  have hLρ : (L : ℝ) < ρ + 1 := Nat.ceil_lt_add_one hρ0.le
  have hL64 : 64 ≤ L := by exact_mod_cast hρ.trans hρL
  have hs2 : Real.sqrt ((2 : ℕ) : ℝ) < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hbox : Real.sqrt ((2 : ℕ) : ℝ) * ((2 * L : ℕ) : ℝ) < 4 * ρ := by
    have h0 : (0 : ℝ) ≤ ((2 * L : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.sqrt ((2 : ℕ) : ℝ) * ((2 * L : ℕ) : ℝ) ≤ 3 / 2 * ((2 * L : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hs2.le h0
      _ < 4 * ρ := by push_cast; nlinarith
  have hgbox : ∀ x ∈ supBox z (2 * L), latticeLaplacian g x = 0 := fun x hx =>
    hg x ((dist_le_of_mem_supBox hx).trans_lt hbox)
  have hmax := abs_le_sum_abs_of_latticeHarmonic g z hL64 hgbox
  set S := ∑ x ∈ componentEuclideanBall (latticeComponent 2) z (4 * ρ), |g x.val| with hS
  have hSbox : ∑ y ∈ supBox z (2 * L), |g y| ≤ S := by
    have hmem : ∀ y : Fin 2 → ℤ, y ∈ (latticeComponent 2).supp := mem_latticeComponent_supp
    rw [hS]
    calc ∑ y ∈ supBox z (2 * L), |g y|
        = ∑ x ∈ (supBox z (2 * L)).attach.map ⟨fun y => (⟨y.1, hmem y.1⟩ : latticeComponent 2),
            fun a b h => Subtype.ext (congrArg Subtype.val h : _)⟩, |g x.val| := by
          rw [sum_map]; exact (sum_attach _ (fun y => |g y|)).symm
      _ ≤ ∑ x ∈ componentEuclideanBall (latticeComponent 2) z (4 * ρ), |g x.val| := by
          apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => abs_nonneg _
          intro x hx
          rw [mem_map] at hx
          obtain ⟨y, _, rfl⟩ := hx
          rw [mem_componentEuclideanBall]
          exact (dist_le_of_mem_supBox y.2).trans_lt hbox
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  have hLsq : 1 / (L : ℝ) ^ 2 ≤ 1 / ρ ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hρ0.le hρL 2)
  apply componentBallL2_le_of_abs_le _ _ _ (by positivity)
  intro x hx
  have hxbox : x.val ∈ supBox z L := by
    simp only [supBox, Fintype.mem_piFinset, mem_Icc]
    intro i
    have h1 := (abs_sub_le_dist_latticeEuclideanEmbedding x.val z i).trans_lt
      ((mem_componentEuclideanBall _ _ _ _).1 hx)
    have h2 : ((|x.val i - z i| : ℤ) : ℝ) < L := by push_cast; linarith
    have h3 : |x.val i - z i| < (L : ℤ) := by exact_mod_cast h2
    rw [abs_lt] at h3
    constructor <;> omega
  calc |g x.val| ≤ 17179873280 / (L : ℝ) ^ 2 * ∑ y ∈ supBox z (2 * L), |g y| := hmax _ hxbox
    _ ≤ 17179873280 / (L : ℝ) ^ 2 * S :=
        mul_le_mul_of_nonneg_left hSbox (by positivity)
    _ = 17179873280 * (1 / (L : ℝ) ^ 2) * S := by ring
    _ ≤ 17179873280 * (1 / ρ ^ 2) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq (by norm_num)) hS0
    _ = 17179873280 / ρ ^ 2 * S := by ring

end Rigidity.Proofs.Regularity
