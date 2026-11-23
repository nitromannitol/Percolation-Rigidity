import Rigidity.Proofs.Green.DarioGuPhiCalculus

/-!
# Weighted `L²` norms on the cluster

`WeightedL2Le K C t z f B` is `‖f exp(g(t, |· - z|)/C)‖_{L²(K)} ≤ B`. This file proves the
calculus of these norms used in §4.3 of Dario–Gu: monotonicity in the constant of the weight,
the triangle inequality, the norm of a function bounded by `ε Φ_{C₁}(t, · - z)`
(`weightedL2Le_of_abs_le_dgPhi`: at most `M ε t^{-1/2}`, the `t^{-d/4}` of the source), the
Cauchy–Schwarz inequality against the inverse weight (`summable_tsum_abs_mul_le`), and the bound
`Σ_y (Φ_{C₁}(s, y - z) exp(-g(s, |y - x|)/C₂))² ≤ M s^{-1} exp(-g(2s, |x - z|)/(2C*))` of the second
factor of (4.48)-a1 (`sum_sq_dgPhi_mul_exp_le`).
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

theorem exp_sq (a : ℝ) : Real.exp a ^ 2 = Real.exp (2 * a) := by
  rw [sq, ← Real.exp_add]
  ring_nf

theorem exp_dgExponent_le {C C' t r : ℝ} (hC : 0 < C) (hCC : C ≤ C') (ht : 0 < t) (hr : 0 ≤ r) :
    Real.exp (dgExponent C' t r) ≤ Real.exp (dgExponent C t r) := by
  rw [dgExponent_eq, dgExponent_eq]
  exact Real.exp_le_exp.2 (div_le_div_of_nonneg_left (dgShape_nonneg ht hr) hC hCC)

variable {K : Set (Vertex 2)} {C t : ℝ} {z : Vertex 2} {f g : Vertex 2 → ℝ} {A B : ℝ}

theorem WeightedL2Le.mono_const {C' : ℝ} (h : WeightedL2Le K C t z f B) (hC : 0 < C)
    (hCC : C ≤ C') (ht : 0 < t) : WeightedL2Le K C' t z f B := by
  intro S hS
  refine le_trans (Finset.sum_le_sum fun x _ => ?_) (h S hS)
  rw [mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le
    (exp_dgExponent_le hC hCC ht (latticeDist_nonneg x z)) 2) (sq_nonneg _)

theorem WeightedL2Le.mono_bound {B' : ℝ} (h : WeightedL2Le K C t z f B) (hB : 0 ≤ B)
    (hBB : B ≤ B') : WeightedL2Le K C t z f B' :=
  fun S hS => (h S hS).trans (pow_le_pow_left₀ hB hBB 2)

theorem WeightedL2Le.of_abs_le (h : WeightedL2Le K C t z g B) (hfg : ∀ x ∈ K, |f x| ≤ |g x|) :
    WeightedL2Le K C t z f B := by
  intro S hS
  refine le_trans (Finset.sum_le_sum fun x hx => ?_) (h S hS)
  rw [mul_pow, mul_pow, ← sq_abs (f x), ← sq_abs (g x)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hfg x (hS x hx)) 2)
    (sq_nonneg _)

theorem WeightedL2Le.add (hf : WeightedL2Le K C t z f A) (hg : WeightedL2Le K C t z g B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : WeightedL2Le K C t z (fun x => f x + g x) (A + B) := by
  intro S hS
  set w := fun x => Real.exp (dgExponent C t (latticeDist x z))
  have h1 := hf S hS
  have h2 := hg S hS
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => f x * w x) (fun x => g x * w x)
  have hcross : ∑ x ∈ S, (f x * w x) * (g x * w x) ≤ A * B := by
    have : (∑ x ∈ S, (f x * w x) * (g x * w x)) ^ 2 ≤ (A * B) ^ 2 := by
      calc _ ≤ (∑ x ∈ S, (f x * w x) ^ 2) * ∑ x ∈ S, (g x * w x) ^ 2 := hcs
        _ ≤ A ^ 2 * B ^ 2 :=
            mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ = (A * B) ^ 2 := by ring
    nlinarith [mul_nonneg hA hB]
  calc ∑ x ∈ S, ((f x + g x) * w x) ^ 2 = ∑ x ∈ S, (f x * w x) ^ 2 +
        2 * ∑ x ∈ S, (f x * w x) * (g x * w x) + ∑ x ∈ S, (g x * w x) ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ A ^ 2 + 2 * (A * B) + B ^ 2 := by linarith
    _ = (A + B) ^ 2 := by ring

theorem WeightedL2Le.sub (hf : WeightedL2Le K C t z f A) (hg : WeightedL2Le K C t z g B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : WeightedL2Le K C t z (fun x => f x - g x) (A + B) := by
  have hg' : WeightedL2Le K C t z (fun x => -g x) B :=
    hg.of_abs_le fun x _ => by rw [abs_neg]
  simpa [sub_eq_add_neg] using hf.add hg' hA hB

theorem WeightedL2Le.const_mul (hf : WeightedL2Le K C t z f B) (c : ℝ) :
    WeightedL2Le K C t z (fun x => c * f x) (|c| * B) := by
  intro S hS
  have := hf S hS
  calc ∑ x ∈ S, (c * f x * Real.exp (dgExponent C t (latticeDist x z))) ^ 2
      = c ^ 2 * ∑ x ∈ S, (f x * Real.exp (dgExponent C t (latticeDist x z))) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ c ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = (|c| * B) ^ 2 := by rw [mul_pow, sq_abs]

theorem rpow_neg_half_sq {t : ℝ} (ht : 0 < t) : (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num
  exact Real.rpow_neg_one t

/-- A function bounded by `ε Φ_{C₁}(t, · - z)` on `K` has weighted norm at most `M ε t^{-1/2}`
for the weight constant `2 C₁`. -/
theorem weightedL2Le_of_abs_le_dgPhi {C₁ : ℝ} (hC₁ : 0 < C₁) : ∃ M : ℝ, 0 < M ∧
    ∀ (K : Set (Vertex 2)) (t : ℝ), 1 ≤ t → ∀ (z : Vertex 2) (f : Vertex 2 → ℝ) (ε : ℝ),
      0 ≤ ε → (∀ x ∈ K, |f x| ≤ ε * dgPhi C₁ t (latticeDist x z)) →
        WeightedL2Le K (2 * C₁) t z f (M * ε * t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨L, hL, hsum⟩ := sum_exp_neg_dgShape_le hC₁
  refine ⟨C₁ * Real.sqrt L, by positivity, fun K t ht z f ε hε hf S hS => ?_⟩
  have ht0 : 0 < t := by linarith
  have hpt : ∀ x ∈ S, (f x * Real.exp (dgExponent (2 * C₁) t (latticeDist x z))) ^ 2 ≤
      ε ^ 2 * C₁ ^ 2 * t⁻¹ ^ 2 * Real.exp (-(dgShape t (latticeDist x z) / C₁)) := by
    intro x hx
    have h := hf x (hS x hx)
    rw [dgPhi_eq] at h
    rw [mul_pow, dgExponent_eq, ← sq_abs (f x)]
    have hfx : |f x| ^ 2 ≤
        (ε * (C₁ * t⁻¹ * Real.exp (-(dgShape t (latticeDist x z) / C₁)))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    calc |f x| ^ 2 * Real.exp (dgShape t (latticeDist x z) / (2 * C₁)) ^ 2
        ≤ (ε * (C₁ * t⁻¹ * Real.exp (-(dgShape t (latticeDist x z) / C₁)))) ^ 2 *
            Real.exp (dgShape t (latticeDist x z) / (2 * C₁)) ^ 2 :=
          mul_le_mul_of_nonneg_right hfx (sq_nonneg _)
      _ = ε ^ 2 * C₁ ^ 2 * t⁻¹ ^ 2 * (Real.exp (-(dgShape t (latticeDist x z) / C₁)) *
            Real.exp (dgShape t (latticeDist x z) / (2 * C₁))) ^ 2 := by ring
      _ = _ := by
          rw [← Real.exp_add, exp_sq]
          congr 2
          field_simp
          ring
  calc ∑ x ∈ S, (f x * Real.exp (dgExponent (2 * C₁) t (latticeDist x z))) ^ 2
      ≤ ∑ x ∈ S, ε ^ 2 * C₁ ^ 2 * t⁻¹ ^ 2 * Real.exp (-(dgShape t (latticeDist x z) / C₁)) :=
        Finset.sum_le_sum hpt
    _ = ε ^ 2 * C₁ ^ 2 * t⁻¹ ^ 2 * ∑ x ∈ S, Real.exp (-(dgShape t (latticeDist x z) / C₁)) := by
        rw [Finset.mul_sum]
    _ ≤ ε ^ 2 * C₁ ^ 2 * t⁻¹ ^ 2 * (L * t) :=
        mul_le_mul_of_nonneg_left (hsum t ht z S) (by positivity)
    _ = (C₁ * Real.sqrt L * ε * t ^ (-(1 / 2 : ℝ))) ^ 2 := by
        rw [mul_pow, rpow_neg_half_sq ht0, mul_pow, mul_pow, Real.sq_sqrt hL.le]
        field_simp

/-- **Cauchy–Schwarz** on `K` against the inverse weight. -/
theorem summable_tsum_abs_mul_le {w : Vertex 2 → ℝ} (hw : ∀ x, 0 < w x)
    (hf : ∀ S : Finset (Vertex 2), (∀ x ∈ S, x ∈ K) → ∑ x ∈ S, (f x * w x) ^ 2 ≤ A ^ 2)
    (hg : ∀ S : Finset (Vertex 2), (∀ x ∈ S, x ∈ K) → ∑ x ∈ S, (g x / w x) ^ 2 ≤ B ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Summable (fun x : K => |f x * g x|) ∧ ∑' x : K, |f x * g x| ≤ A * B := by
  have hfin : ∀ S : Finset K, ∑ x ∈ S, |f x * g x| ≤ A * B := by
    intro S
    have hS : ∀ x ∈ S.map (Function.Embedding.subtype _), x ∈ K := by
      intro x hx
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have h1 := hf _ hS
    have h2 := hg _ hS
    rw [Finset.sum_map] at h1 h2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun x : K => |f x * w x|)
      (fun x : K => |g x / w x|)
    have heq : ∀ x : K, |f x * w x| * |g x / w x| = |f x * g x| := by
      intro x
      rw [← abs_mul]
      congr 1
      field_simp [(hw x).ne']
    simp only [heq, sq_abs] at hcs
    have : (∑ x ∈ S, |f x * g x|) ^ 2 ≤ (A * B) ^ 2 := by
      calc _ ≤ (∑ x ∈ S, (f x * w x) ^ 2) * ∑ x ∈ S, (g x / w x) ^ 2 := hcs
        _ ≤ A ^ 2 * B ^ 2 :=
            mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ = (A * B) ^ 2 := by ring
    nlinarith [mul_nonneg hA hB, Finset.sum_nonneg (fun x (_ : x ∈ S) => abs_nonneg (f x * g x))]
  have hs : Summable (fun x : K => |f x * g x|) :=
    summable_of_sum_le (fun _ => abs_nonneg _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-- The second factor of (4.48)-a1 and (4.48)-a2:
`Σ_y (Φ_{C₁}(s, |y - z|) exp(-g(s, |y - x|)/C₂))² ≤ M s^{-1} exp(-g(2s, |x - z|)/(2C*))`,
`C* = max C₁ C₂`. -/
theorem sum_sq_dgPhi_mul_exp_le {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) : ∃ M : ℝ, 0 < M ∧
    ∀ s : ℝ, 1 ≤ s → ∀ (x z : Vertex 2) (S : Finset (Vertex 2)),
      ∑ y ∈ S, (dgPhi C₁ s (latticeDist y z) * Real.exp (-dgExponent C₂ s (latticeDist y x))) ^ 2 ≤
        M * s⁻¹ * Real.exp (-(dgShape (2 * s) (latticeDist x z) / (2 * max C₁ C₂))) := by
  set Cs := max C₁ C₂ with hCs
  have hCs0 : 0 < Cs := lt_max_of_lt_left hC₁
  obtain ⟨L, hL, hsum⟩ := sum_exp_neg_dgShape_le hCs0
  refine ⟨C₁ ^ 2 * L, by positivity, fun s hs x z S => ?_⟩
  have hs0 : 0 < s := by linarith
  set G := dgShape (2 * s) (latticeDist x z)
  have hpt : ∀ y ∈ S, (dgPhi C₁ s (latticeDist y z) *
      Real.exp (-dgExponent C₂ s (latticeDist y x))) ^ 2 ≤
      C₁ ^ 2 * s⁻¹ ^ 2 * Real.exp (-(G / (2 * Cs))) *
        Real.exp (-(dgShape s (latticeDist y z) / Cs)) := by
    intro y _
    have ga := dgShape_nonneg hs0 (latticeDist_nonneg y z)
    have gb := dgShape_nonneg hs0 (latticeDist_nonneg y x)
    have hG := dgShape_add_ge hs0 (latticeDist_nonneg y z) (latticeDist_nonneg y x)
      (latticeDist_nonneg x z) (latticeDist_triangle x y z)
    rw [dgPhi_eq, dgExponent_eq]
    have e1 : dgShape s (latticeDist y z) / Cs ≤ dgShape s (latticeDist y z) / C₁ :=
      div_le_div_of_nonneg_left ga hC₁ (le_max_left _ _)
    have e2 : dgShape s (latticeDist y x) / Cs ≤ dgShape s (latticeDist y x) / C₂ :=
      div_le_div_of_nonneg_left gb hC₂ (le_max_right _ _)
    have hexp : Real.exp (-(dgShape s (latticeDist y z) / C₁)) ^ 2 *
        Real.exp (-(dgShape s (latticeDist y x) / C₂)) ^ 2 ≤
        Real.exp (-(G / (2 * Cs))) * Real.exp (-(dgShape s (latticeDist y z) / Cs)) := by
      rw [exp_sq, exp_sq, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : G / (2 * Cs) ≤ (dgShape s (latticeDist y z) + dgShape s (latticeDist y x)) / Cs := by
        rw [div_le_div_iff₀ (by positivity) hCs0]
        nlinarith
      have h3 : (dgShape s (latticeDist y z) + dgShape s (latticeDist y x)) / Cs =
          dgShape s (latticeDist y z) / Cs + dgShape s (latticeDist y x) / Cs := add_div _ _ _
      linarith [div_nonneg gb hC₂.le]
    calc (C₁ * s⁻¹ * Real.exp (-(dgShape s (latticeDist y z) / C₁)) *
          Real.exp (-(dgShape s (latticeDist y x) / C₂))) ^ 2
        = C₁ ^ 2 * s⁻¹ ^ 2 * (Real.exp (-(dgShape s (latticeDist y z) / C₁)) ^ 2 *
            Real.exp (-(dgShape s (latticeDist y x) / C₂)) ^ 2) := by ring
      _ ≤ C₁ ^ 2 * s⁻¹ ^ 2 * (Real.exp (-(G / (2 * Cs))) *
            Real.exp (-(dgShape s (latticeDist y z) / Cs))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ y ∈ S, C₁ ^ 2 * s⁻¹ ^ 2 * Real.exp (-(G / (2 * Cs))) *
          Real.exp (-(dgShape s (latticeDist y z) / Cs)) := Finset.sum_le_sum hpt
    _ = C₁ ^ 2 * s⁻¹ ^ 2 * Real.exp (-(G / (2 * Cs))) *
          ∑ y ∈ S, Real.exp (-(dgShape s (latticeDist y z) / Cs)) := by rw [Finset.mul_sum]
    _ ≤ C₁ ^ 2 * s⁻¹ ^ 2 * Real.exp (-(G / (2 * Cs))) * (L * s) :=
        mul_le_mul_of_nonneg_left (hsum s hs z S) (by positivity)
    _ = C₁ ^ 2 * L * s⁻¹ * Real.exp (-(G / (2 * Cs))) := by
        field_simp

end Rigidity.Green
