import Rigidity.Steps.Section5.NoThickPaths
import Rigidity.Proofs.Section5.LoopFromCrossings

/-!
# Lemma 5.19: many disjoint paths from `γ` to the support of `u`

This file proves `ManyPathsStep` (`step:5.19-many-paths`, corrected draft L2040-2043). No
literature input is used: the only planar topology is the following
discrete fact about the winding number `windingNumber` of Lemma 5.14.

* `exists_eq_of_crossing`: a lattice loop in the annulus `Q_{2m} \ Q_m` with nonzero winding
  number around the origin meets every lattice path from `Q_m` to the complement of `Q_{2m}`.
  Its proof uses the sum `windAt β y` of the angle increments of the loop `β` seen from `y`. For
  adjacent lattice points `y`, `y'` off the loop, the increment `θ(y) - θ(y')` along a unit step
  `a → b` of the loop equals `h(b) - h(a)` with `h(p) = arg ((p - y) / (p - y'))`: the two sides
  agree modulo `2π`, and all four principal arguments lie in `(-π/2, π/2)` because two nonzero
  lattice vectors differing by a unit vector have a positive inner product. Summing over the
  closed loop gives `windAt β y = windAt β y'` (`windAt_eq_of_step`). Far from the loop the
  increments telescope (`windAt_eq_zero_of_not_mem_cube`), and `windAt` is constant on `Q_m`.

At each scale `m = S₀ 2^j` the loop of Lemma 5.14 meets the path of Lemma 5.18 from `Q_R` to the
complement of `Q_{2m+1}`, where `u ≠ 0`, and the bi-infinite path `γ`, which visits `Q_R` and
leaves every cube. Walking along the loop from its meeting point with the path of Lemma 5.18 to
its first vertex on `γ` and
reversing gives an arc `ρ` from `γ(k)` to a vertex where `u ≠ 0`, meeting `γ` only at its initial
point (`exists_arc_of_loop`). As `S₀` exceeds the scale of the stretch of `γ` between its first
and last visits to `Q_R`, each `k` lies on one of the two tails of `γ`; infinitely many scales
share a tail, and `N` of them give the paths. Arcs at different scales lie in disjoint annuli.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-! ### The winding number of a lattice loop around a lattice point -/

/-- The sum of the angle increments of the closed lattice path `β 0, …, β n, β 0` seen from `y`.
At `y = 0` it is `2π` times `windingNumber β`. -/
noncomputable def windAt {n : ℕ} (β : Fin (n + 1) → Vertex 2) (y : Vertex 2) : ℝ :=
  ∑ i : Fin (n + 1),
    Complex.arg ((toComplex (β (i + 1)) - toComplex y) / (toComplex (β i) - toComplex y))

theorem toComplex_zero : toComplex 0 = 0 := by
  apply Complex.ext <;> simp [toComplex]

theorem windingNumber_eq_windAt {n : ℕ} (β : Fin (n + 1) → Vertex 2) :
    windingNumber β = windAt β 0 / (2 * Real.pi) := by
  simp only [windingNumber, windAt, toComplex_zero, sub_zero]

theorem vertex_eq_of_coords {a b : Vertex 2} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext i
  fin_cases i
  exacts [h0, h1]

theorem toComplex_injective : Function.Injective toComplex := fun a b h =>
  vertex_eq_of_coords
    (by exact_mod_cast (toComplex_re a).symm.trans ((congrArg Complex.re h).trans (toComplex_re b)))
    (by exact_mod_cast (toComplex_im a).symm.trans ((congrArg Complex.im h).trans (toComplex_im b)))

theorem toComplex_sub_ne_zero {a b : Vertex 2} (h : a ≠ b) : toComplex a - toComplex b ≠ 0 :=
  sub_ne_zero.2 (toComplex_injective.ne h)

theorem toComplex_sub' (a b : Vertex 2) :
    toComplex a - toComplex b = ⟨((a 0 - b 0 : ℤ) : ℝ), ((a 1 - b 1 : ℤ) : ℝ)⟩ := by
  apply Complex.ext <;> simp [toComplex]

/-- Nonzero integers `x`, `x' = x ± 1` (or `y ≠ 0`) give `x' x + y² > 0`. -/
theorem dot_pos_aux {x x' y : ℤ} (hx : x' = x + 1 ∨ x' = x - 1) (h1 : ¬(x = 0 ∧ y = 0))
    (h2 : ¬(x' = 0 ∧ y = 0)) : 0 < x' * x + y * y := by
  have hxx : 0 ≤ x' * x := by
    rcases (by omega : x ≤ -1 ∨ x = 0 ∨ 1 ≤ x) with h | h | h <;>
      rcases hx with rfl | rfl <;> nlinarith
  rcases eq_or_ne y 0 with rfl | hy
  · have := lt_of_le_of_ne hxx
      (mul_ne_zero (fun h => h2 ⟨h, rfl⟩) (fun h => h1 ⟨h, rfl⟩)).symm
    linarith
  · have := mul_self_pos.2 hy
    linarith

/-- Two nonzero lattice vectors `v`, `w` with `w - v` a unit vector have a positive inner
product. -/
theorem dot_pos_of_unit {v0 v1 w0 w1 : ℤ} (h : |v0 - w0| + |v1 - w1| = 1)
    (hv : ¬(v0 = 0 ∧ v1 = 0)) (hw : ¬(w0 = 0 ∧ w1 = 0)) : 0 < w0 * v0 + w1 * v1 := by
  have hc : ((w0 = v0 + 1 ∨ w0 = v0 - 1) ∧ w1 = v1) ∨
      (w0 = v0 ∧ (w1 = v1 + 1 ∨ w1 = v1 - 1)) := by
    rcases abs_cases (v0 - w0) with ⟨h0, _⟩ | ⟨h0, _⟩ <;>
      rcases abs_cases (v1 - w1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  rcases hc with ⟨hx, rfl⟩ | ⟨rfl, hy⟩
  · exact dot_pos_aux hx hv hw
  · have := dot_pos_aux (y := w0) hy (fun h => hv ⟨h.2, h.1⟩) (fun h => hw ⟨h.2, h.1⟩)
    linarith

/-- The quotient of two nonzero lattice vectors differing by a unit vector lies in the open
right half-plane. -/
theorem re_div_pos_of_int {v0 v1 w0 w1 : ℤ} (h : |v0 - w0| + |v1 - w1| = 1)
    (hv : ¬(v0 = 0 ∧ v1 = 0)) (hw : ¬(w0 = 0 ∧ w1 = 0)) :
    0 < ((⟨w0, w1⟩ : ℂ) / ⟨v0, v1⟩).re := by
  have hdot : (0 : ℝ) < (w0 : ℝ) * v0 + (w1 : ℝ) * v1 := by
    exact_mod_cast dot_pos_of_unit h hv hw
  have hns : (0 : ℝ) < (v0 : ℝ) * v0 + (v1 : ℝ) * v1 := by
    have : 0 < v0 * v0 + v1 * v1 := by
      rcases not_and_or.1 hv with h0 | h0
      · have := mul_self_pos.2 h0
        nlinarith [mul_self_nonneg v1]
      · have := mul_self_pos.2 h0
        nlinarith [mul_self_nonneg v0]
    exact_mod_cast this
  rw [Complex.div_re, ← add_div, Complex.normSq_mk]
  exact div_pos hdot hns

/-- For lattice points with `(a - c) - (b - d)` a unit vector, `a ≠ c` and `b ≠ d`, the quotient
`(b - d) / (a - c)` lies in the open right half-plane. -/
theorem re_div_pos {a b c d : Vertex 2}
    (h : |(a 0 - c 0) - (b 0 - d 0)| + |(a 1 - c 1) - (b 1 - d 1)| = 1) (hac : a ≠ c)
    (hbd : b ≠ d) : 0 < ((toComplex b - toComplex d) / (toComplex a - toComplex c)).re := by
  rw [toComplex_sub', toComplex_sub']
  exact re_div_pos_of_int h (fun h' => hac (vertex_eq_of_coords (by omega) (by omega)))
    (fun h' => hbd (vertex_eq_of_coords (by omega) (by omega)))

/-- Principal arguments in `(-π/2, π/2)`: `arg (B/A) - arg (B'/A') = arg (B/B') - arg (A/A')`,
both sides agreeing modulo `2π`. -/
theorem arg_div_sub_arg_div {A B A' B' : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hA' : A' ≠ 0)
    (hB' : B' ≠ 0) (h1 : 0 < (B / A).re) (h2 : 0 < (B' / A').re) (h3 : 0 < (B / B').re)
    (h4 : 0 < (A / A').re) :
    Complex.arg (B / A) - Complex.arg (B' / A') =
      Complex.arg (B / B') - Complex.arg (A / A') := by
  have e1 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h1))
  have e2 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h2))
  have e3 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h3))
  have e4 := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl h4))
  have key : ((Complex.arg (B / A) - Complex.arg (B' / A') : ℝ) : Real.Angle) =
      ((Complex.arg (B / B') - Complex.arg (A / A') : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, Complex.arg_div_coe_angle hB hA,
      Complex.arg_div_coe_angle hB' hA', Complex.arg_div_coe_angle hB hB',
      Complex.arg_div_coe_angle hA hA']
    abel
  have := congrArg Real.Angle.toReal key
  rwa [Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩,
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩] at this

theorem abs_add_abs_of_latticeL1Dist {a b : Vertex 2} (h : latticeL1Dist a b = 1) :
    |a 0 - b 0| + |a 1 - b 1| = 1 := by
  simpa [latticeL1Dist, Fin.sum_univ_two] using h

/-- Adjacent lattice points off a lattice loop see it with the same winding number. -/
theorem windAt_eq_of_step {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {y y' : Vertex 2}
    (hyy : latticeL1Dist y y' = 1) (hy : ∀ i, β i ≠ y) (hy' : ∀ i, β i ≠ y') :
    windAt β y = windAt β y' := by
  set g : Fin (n + 1) → ℝ := fun i =>
    Complex.arg ((toComplex (β i) - toComplex y) / (toComplex (β i) - toComplex y')) with hg
  have hstep : ∀ i, |(β i 0 - y 0) - (β (i + 1) 0 - y 0)| +
      |(β i 1 - y 1) - (β (i + 1) 1 - y 1)| = 1 := fun i => by
    simp only [sub_sub_sub_cancel_right]
    exact abs_add_abs_of_latticeL1Dist (hβ i)
  have hstep' : ∀ i, |(β i 0 - y' 0) - (β (i + 1) 0 - y' 0)| +
      |(β i 1 - y' 1) - (β (i + 1) 1 - y' 1)| = 1 := fun i => by
    simp only [sub_sub_sub_cancel_right]
    exact abs_add_abs_of_latticeL1Dist (hβ i)
  have hmove : ∀ p : Vertex 2, |(p 0 - y' 0) - (p 0 - y 0)| + |(p 1 - y' 1) - (p 1 - y 1)| = 1 :=
    fun p => by
      simp only [sub_sub_sub_cancel_left]
      exact abs_add_abs_of_latticeL1Dist hyy
  have key : ∀ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
        (toComplex (β i) - toComplex y)) -
      Complex.arg ((toComplex (β (i + 1)) - toComplex y') / (toComplex (β i) - toComplex y')) =
      g (i + 1) - g i := fun i =>
    arg_div_sub_arg_div (toComplex_sub_ne_zero (hy i)) (toComplex_sub_ne_zero (hy (i + 1)))
      (toComplex_sub_ne_zero (hy' i)) (toComplex_sub_ne_zero (hy' (i + 1)))
      (re_div_pos (hstep i) (hy i) (hy (i + 1))) (re_div_pos (hstep' i) (hy' i) (hy' (i + 1)))
      (re_div_pos (hmove _) (hy' (i + 1)) (hy (i + 1))) (re_div_pos (hmove _) (hy' i) (hy i))
  have hsum : ∑ i, (Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
        (toComplex (β i) - toComplex y)) -
      Complex.arg ((toComplex (β (i + 1)) - toComplex y') / (toComplex (β i) - toComplex y'))) =
      ∑ i, (g (i + 1) - g i) := Finset.sum_congr rfl fun i _ => key i
  rw [← sub_eq_zero, windAt, windAt, ← Finset.sum_sub_distrib, hsum, Finset.sum_sub_distrib,
    sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) g

/-- If the loop lies in an open half-plane `{z : Re (c (z - y)) > 0}`, its increments seen from
`y` telescope and `windAt` vanishes. -/
theorem windAt_eq_zero_of_re_pos {n : ℕ} {β : Fin (n + 1) → Vertex 2} {y : Vertex 2} (c : ℂ)
    (hc : ∀ i, 0 < (c * (toComplex (β i) - toComplex y)).re) : windAt β y = 0 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa using hc 0
  set g : Fin (n + 1) → ℝ := fun i => Complex.arg (c * (toComplex (β i) - toComplex y)) with hg
  have key : ∀ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
      (toComplex (β i) - toComplex y)) = g (i + 1) - g i := by
    intro i
    rw [← mul_div_mul_left (toComplex (β (i + 1)) - toComplex y) _ hc0]
    exact arg_div_of_re_pos (hc i) (hc (i + 1))
  have hsum : ∑ i, Complex.arg ((toComplex (β (i + 1)) - toComplex y) /
      (toComplex (β i) - toComplex y)) = ∑ i, (g (i + 1) - g i) :=
    Finset.sum_congr rfl fun i _ => key i
  rw [windAt, hsum, Finset.sum_sub_distrib, sub_eq_zero]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) g

/-- Outside a cube containing the loop, `windAt` vanishes. -/
theorem windAt_eq_zero_of_not_mem_cube {n : ℕ} {β : Fin (n + 1) → Vertex 2} {M : ℕ}
    {y : Vertex 2} (hβ : ∀ i, β i ∈ cube M) (hy : y ∉ cube M) : windAt β y = 0 := by
  have hy' : ¬ |y 0| ≤ M ∨ ¬ |y 1| ≤ M := by
    by_contra h
    push Not at h
    exact hy fun i => by fin_cases i <;> [exact h.1; exact h.2]
  rcases hy' with h | h <;> rw [abs_le, not_and_or] at h <;> push Not at h
  · rcases h with h | h
    · refine windAt_eq_zero_of_re_pos 1 fun i => ?_
      have := (abs_le.1 (hβ i 0)).1
      have : (y 0 : ℝ) < β i 0 := by exact_mod_cast (by omega : y 0 < β i 0)
      simp [toComplex]
      linarith
    · refine windAt_eq_zero_of_re_pos (-1) fun i => ?_
      have := (abs_le.1 (hβ i 0)).2
      have : (β i 0 : ℝ) < y 0 := by exact_mod_cast (by omega : β i 0 < y 0)
      simp [toComplex]
      linarith
  · rcases h with h | h
    · refine windAt_eq_zero_of_re_pos (-Complex.I) fun i => ?_
      have := (abs_le.1 (hβ i 1)).1
      have : (y 1 : ℝ) < β i 1 := by exact_mod_cast (by omega : y 1 < β i 1)
      simp [toComplex]
      linarith
    · refine windAt_eq_zero_of_re_pos Complex.I fun i => ?_
      have := (abs_le.1 (hβ i 1)).2
      have : (β i 1 : ℝ) < y 1 := by exact_mod_cast (by omega : β i 1 < y 1)
      simp [toComplex]
      linarith

/-- `windAt` is constant along a lattice line `g` off the loop. -/
theorem windAt_eq_of_line {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) (g : ℤ → Vertex 2)
    (hg : ∀ k, latticeL1Dist (g k) (g (k + 1)) = 1) (lo : ℤ) :
    ∀ k : ℕ, (∀ j : ℕ, j ≤ k → ∀ i, β i ≠ g (lo + j)) →
      windAt β (g lo) = windAt β (g (lo + k)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hoff
    rw [ih fun j hj => hoff j (by omega)]
    have := windAt_eq_of_step hβ (hg (lo + k)) (hoff k (by omega))
      (by simpa [add_assoc] using hoff (k + 1) le_rfl)
    simpa [add_assoc] using this

/-- `windAt` is constant on a cube `Q_m` avoided by the loop. -/
theorem windAt_eq_of_mem_cube {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {m : ℕ} (hout : ∀ i, β i ∉ cube m)
    {x : Vertex 2} (hx : x ∈ cube m) : windAt β x = windAt β 0 := by
  have hoff : ∀ v : Vertex 2, |v 0| ≤ m → |v 1| ≤ m → ∀ i, β i ≠ v := by
    intro v h0 h1 i h
    apply hout i
    rw [h]
    intro j
    fin_cases j
    exacts [h0, h1]
  have h0 := abs_le.1 (hx 0)
  have h1 := abs_le.1 (hx 1)
  have hvert : ∀ a k : ℤ, latticeL1Dist (![a, k] : Vertex 2) ![a, k + 1] = 1 := fun a k => by
    simp [latticeL1Dist, Fin.sum_univ_two]
  have hhor : ∀ k : ℤ, latticeL1Dist (![k, 0] : Vertex 2) ![k + 1, 0] = 1 := fun k => by
    simp [latticeL1Dist, Fin.sum_univ_two]
  have hv : windAt β ![x 0, 0] = windAt β ![x 0, x 1] := by
    rcases le_total 0 (x 1) with h | h
    · have := windAt_eq_of_line hβ (fun k => ![x 0, k]) (fun k => hvert _ k) 0 (x 1).toNat
        fun j hj i => hoff ![x 0, 0 + (j : ℤ)] (hx 0) (show |(0 : ℤ) + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩) i
      simpa [Int.toNat_of_nonneg h] using this
    · have := windAt_eq_of_line hβ (fun k => ![x 0, k]) (fun k => hvert _ k) (x 1) (-x 1).toNat
        fun j hj i => hoff ![x 0, x 1 + (j : ℤ)] (hx 0) (show |x 1 + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩) i
      have he : x 1 + ((-x 1).toNat : ℤ) = 0 := by omega
      rw [he] at this
      exact this.symm
  have hh : windAt β ![0, 0] = windAt β ![x 0, 0] := by
    rcases le_total 0 (x 0) with h | h
    · have := windAt_eq_of_line hβ (fun k => ![k, 0]) hhor 0 (x 0).toNat
        fun j hj i => hoff ![0 + (j : ℤ), 0] (show |(0 : ℤ) + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩)
          (show |(0 : ℤ)| ≤ m by simp) i
      simpa [Int.toNat_of_nonneg h] using this
    · have := windAt_eq_of_line hβ (fun k => ![k, 0]) hhor (x 0) (-x 0).toNat
        fun j hj i => hoff ![x 0 + (j : ℤ), 0] (show |x 0 + j| ≤ m from abs_le.2 ⟨by omega, by omega⟩)
          (show |(0 : ℤ)| ≤ m by simp) i
      have he : x 0 + ((-x 0).toNat : ℤ) = 0 := by omega
      rw [he] at this
      exact this.symm
  have hx' : (![x 0, x 1] : Vertex 2) = x := vertex_eq_of_coords rfl rfl
  have hz : (![0, 0] : Vertex 2) = 0 := vertex_eq_of_coords rfl rfl
  calc windAt β x = windAt β ![x 0, x 1] := by rw [hx']
    _ = windAt β ![x 0, 0] := hv.symm
    _ = windAt β ![0, 0] := hh.symm
    _ = windAt β 0 := by rw [hz]

/-- **The crossing lemma.** A lattice loop in `Q_{2m} \ Q_m` with nonzero winding number around
the origin meets every lattice path from `Q_m` to the complement of `Q_{2m}`. -/
theorem exists_eq_of_crossing {n : ℕ} {β : Fin (n + 1) → Vertex 2}
    (hβ : ∀ i, latticeL1Dist (β i) (β (i + 1)) = 1) {m : ℕ}
    (hβm : ∀ i, β i ∈ cube (2 * m) \ cube m) (hw : windAt β 0 ≠ 0) {P : ℕ → Vertex 2} {L : ℕ}
    (hP : ∀ i < L, latticeL1Dist (P i) (P (i + 1)) = 1) (h0 : P 0 ∈ cube m)
    (hL : P L ∉ cube (2 * m)) : ∃ i ≤ L, ∃ t, β t = P i := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ i ≤ L, windAt β (P i) = windAt β (P 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [← ih (by omega)]
      exact (windAt_eq_of_step hβ (hP i (by omega)) (hcon i (by omega))
        (hcon (i + 1) hi)).symm
  apply hw
  rw [← windAt_eq_of_mem_cube hβ (fun i => (hβm i).2) h0, ← hconst L le_rfl]
  exact windAt_eq_zero_of_not_mem_cube (fun i => (hβm i).1) hL

/-! ### Arcs of the loops from `γ` to the support of `u` -/

variable {ω : Configuration 2}

theorem latticeL1Dist_eq_one_of_adj {C : OpenComponent ω} {x y : C}
    (h : (componentGraph C).Adj x y) : latticeL1Dist x.val y.val = 1 :=
  lattice_adj_iff_l1Dist.1 ((C.toSimpleGraph_adj x.2 y.2).1 h).1

open Fin.NatCast

/-- The index `min i n` of `Fin (n + 1)`. -/
def finClamp (n i : ℕ) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- At a scale `m`, a loop of `𝒞_∞` in `Q_{2m} \ Q_m` with nonzero winding number, a path of
`𝒞_∞` from `Q_m` to the complement of `Q_{2m}` on which `u ≠ 0`, and a bi-infinite path `γ`
visiting `Q_m` give an arc of the loop from a vertex `γ k` to a vertex where `u ≠ 0`, meeting `γ`
only at its initial point. -/
theorem exists_arc_of_loop {C : OpenComponent ω} {u : C → ℝ} {m n : ℕ} {β : Fin (n + 1) → C}
    (hβa : ∀ i, (componentGraph C).Adj (β i) (β (i + 1)))
    (hβm : ∀ i, (β i).val ∈ cube (2 * m) \ cube m)
    (hβw : windingNumber (fun i => (β i).val) ≠ 0) {n' : ℕ} {π : Fin (n' + 1) → C}
    (hπa : ∀ i : Fin n', (componentGraph C).Adj (π i.castSucc) (π i.succ))
    (hπ0 : (π 0).val ∈ cube m) (hπL : (π (Fin.last n')).val ∉ cube (2 * m))
    (hπu : ∀ i, u (π i) ≠ 0) {γ : ℤ → C} (hγi : Function.Injective γ)
    (hγa : ∀ k, (componentGraph C).Adj (γ k) (γ (k + 1))) {c : ℤ} (hc : (γ c).val ∈ cube m) :
    ∃ (k : ℤ) (ℓ : ℕ) (ρ : ℕ → C), (∀ i < ℓ, (componentGraph C).Adj (ρ i) (ρ (i + 1))) ∧
      ρ 0 = γ k ∧ (∀ i, 0 < i → i ≤ ℓ → ρ i ∉ Set.range γ) ∧
      (∀ i ≤ ℓ, (ρ i).val ∈ cube (2 * m) \ cube m) ∧ u (ρ ℓ) ≠ 0 := by
  have hβs : ∀ i, latticeL1Dist (β i).val (β (i + 1)).val = 1 := fun i =>
    latticeL1Dist_eq_one_of_adj (hβa i)
  have hw : windAt (fun i => (β i).val) 0 ≠ 0 := by
    intro h
    apply hβw
    rw [windingNumber_eq_windAt, h, zero_div]
  -- the loop meets the path where `u ≠ 0`
  obtain ⟨i0, -, t0, ht0⟩ := exists_eq_of_crossing (β := fun i => (β i).val) hβs hβm hw
    (P := fun i => (π (finClamp n' i)).val) (L := n')
    (fun i hi => by
      have e1 : finClamp n' i = Fin.castSucc ⟨i, hi⟩ := Fin.ext (by simp [finClamp]; omega)
      have e2 : finClamp n' (i + 1) = Fin.succ ⟨i, hi⟩ := Fin.ext (by simp [finClamp]; omega)
      simp only [e1, e2]
      exact latticeL1Dist_eq_one_of_adj (hπa ⟨i, hi⟩))
    (by rwa [show finClamp n' 0 = 0 from Fin.ext (by simp [finClamp])])
    (by rwa [show finClamp n' n' = Fin.last n' from Fin.ext (by simp [finClamp])])
  have ht0' : β t0 = π (finClamp n' i0) := Subtype.ext ht0
  -- the loop meets `γ`
  have hfin : {k : ℤ | (γ k).val ∈ cube (2 * m)}.Finite :=
    (cube_finite (2 * m)).preimage (Subtype.val_injective.comp hγi).injOn
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hn1 : (γ (c + ((max c (B + 1) - c).toNat : ℤ))).val ∉ cube (2 * m) := by
    intro h
    have := hB h
    omega
  obtain ⟨i1, -, t1, ht1⟩ := exists_eq_of_crossing (β := fun i => (β i).val) hβs hβm hw
    (P := fun i => (γ (c + (i : ℤ))).val) (L := (max c (B + 1) - c).toNat)
    (fun i _ => by
      have := latticeL1Dist_eq_one_of_adj (hγa (c + i))
      rwa [show c + (i : ℤ) + 1 = c + ((i + 1 : ℕ) : ℤ) by push_cast; ring] at this)
    (by simpa using hc) hn1
  have ht1' : β t1 = γ (c + i1) := Subtype.ext ht1
  -- walk along the loop from `β t0` to its first vertex on `γ`
  have hex : ∃ s : ℕ, β (t0 + (s : Fin (n + 1))) ∈ Set.range γ :=
    ⟨(t1 - t0).val, by rw [Fin.cast_val_eq_self, show t0 + (t1 - t0) = t1 by abel]; exact ⟨_, ht1'.symm⟩⟩
  classical
  obtain ⟨s, ⟨k, hk⟩, hmin⟩ : ∃ s : ℕ, β (t0 + (s : Fin (n + 1))) ∈ Set.range γ ∧
      ∀ s' < s, β (t0 + (s' : Fin (n + 1))) ∉ Set.range γ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s' h => Nat.find_min hex h⟩
  refine ⟨k, s, fun i => β (t0 + ((s - i : ℕ) : Fin (n + 1))), fun i hi => ?_, ?_,
    fun i hi hle => hmin _ (by omega), fun i _ => hβm _, ?_⟩
  · show (componentGraph C).Adj (β (t0 + ((s - i : ℕ) : Fin (n + 1))))
      (β (t0 + ((s - (i + 1) : ℕ) : Fin (n + 1))))
    rw [show s - i = s - (i + 1) + 1 by omega, Nat.cast_succ, ← add_assoc]
    exact (hβa _).symm
  · show β (t0 + ((s - 0 : ℕ) : Fin (n + 1))) = γ k
    rw [Nat.sub_zero]
    exact hk.symm
  · show u (β (t0 + ((s - s : ℕ) : Fin (n + 1)))) ≠ 0
    rw [Nat.sub_self, Nat.cast_zero, add_zero, ht0']
    exact hπu _

/-- **Step `step:5.19-many-paths`** of Lemma 5.19: the loops of Lemma 5.14 at the scales
`S₀ 2^j` and the nonzero paths of Lemma 5.18 give, for every `N`, `N` disjoint paths outside
`Q_{R+1}` from vertices of `γ` on one tail to vertices where `u ≠ 0`, meeting `γ` only at their
initial points. -/
theorem manyPathsStep : ManyPathsStep := by
  intro ω C f u hL hN γ hγi hγa R hR0 hRf hc N
  obtain ⟨c, hc⟩ := hc
  obtain ⟨M, hM⟩ := hL
  -- the visits of `γ` to `Q_R` lie in a stretch `γ [a, b]`, inside a cube `Q_S`
  have hfin : {k : ℤ | (γ k).val ∈ cube R}.Finite :=
    (cube_finite R).preimage (Subtype.val_injective.comp hγi).injOn
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨S, -, hS⟩ := exists_subset_cube ((Set.finite_Icc a b).image fun k => (γ k).val)
  have hscale : ∀ j : ℕ, M + S + R + 1 ≤ (M + S + R + 1) * 2 ^ j := fun j =>
    Nat.le_mul_of_pos_right _ (by positivity)
  have scale : ∀ j : ℕ, ∃ (k : ℤ) (ℓ : ℕ) (ρ : ℕ → C),
      (∀ i < ℓ, (componentGraph C).Adj (ρ i) (ρ (i + 1))) ∧ ρ 0 = γ k ∧
      (∀ i, 0 < i → i ≤ ℓ → ρ i ∉ Set.range γ) ∧
      (∀ i ≤ ℓ, (ρ i).val ∈ cube (2 * ((M + S + R + 1) * 2 ^ j)) \
        cube ((M + S + R + 1) * 2 ^ j)) ∧ u (ρ ℓ) ≠ 0 := by
    intro j
    have hm := hscale j
    obtain ⟨n, β, hβa, hβm, hβw⟩ := hM ((M + S + R + 1) * 2 ^ j) (by omega)
    obtain ⟨n', π, hπa, hπ0, hπL, hπu⟩ :=
      hN R hR0 hRf (2 * ((M + S + R + 1) * 2 ^ j) + 1) (by omega)
    exact exists_arc_of_loop hβa hβm hβw hπa (cube_mono (by omega) hπ0)
      (fun h => hπL (cube_mono (by omega) h)) hπu hγi hγa (cube_mono (by omega) hc)
  choose k ℓ ρ hρa hρ0 hργ hρm hρu using scale
  -- each arc starts on one of the two tails of `γ`
  have hside : ∀ j, k j < a ∨ b < k j := by
    intro j
    by_contra h
    push Not at h
    have hmem : (γ (k j)).val ∈ cube S := hS ⟨k j, ⟨h.1, h.2⟩, rfl⟩
    have hout := (hρm j 0 (Nat.zero_le _)).2
    rw [hρ0 j] at hout
    exact hout (cube_mono (by have := hscale j; omega) hmem)
  obtain ⟨P, hP, hinf⟩ : ∃ P : ℤ → Prop, (∀ k₁ k₂ n, P k₁ → P k₂ → min k₁ k₂ ≤ n →
      n ≤ max k₁ k₂ → (γ n).val ∉ cube R) ∧ {j | P (k j)}.Infinite := by
    rcases Set.infinite_union.1 (show ({j | b < k j} ∪ {j | b < k j}ᶜ).Infinite by
      rw [Set.union_compl_self]; exact Set.infinite_univ) with h | h
    · exact ⟨(b < ·), fun k₁ k₂ n h1 h2 hn _ hmem => by have := hb hmem; omega, h⟩
    · exact ⟨(· < a), fun k₁ k₂ n h1 h2 _ hn hmem => by have := ha hmem; omega,
        h.mono fun j hj => (hside j).resolve_right hj⟩
  set e := hinf.natEmbedding
  have hJ : ∀ i₁ i₂ : Fin N, i₁ ≠ i₂ → (e i₁.val).val ≠ (e i₂.val).val := fun i₁ i₂ h h' =>
    h (Fin.ext (e.injective (Subtype.ext h')))
  refine ⟨fun i => k (e i.val).val, fun i => ℓ (e i.val).val, fun i => ρ (e i.val).val,
    fun i => hρa _, fun i => hρ0 _, fun i => hργ _, fun i j hj h => ?_, fun i => hρu _,
    fun i₁ i₂ h j₁ hj₁ j₂ hj₂ heq => ?_,
    fun i₁ i₂ n h1 h2 => hP _ _ n (e i₁.val).2 (e i₂.val).2 h1 h2⟩
  · exact (hρm _ j hj).2 (cube_mono (by have := hscale (e i.val).val; omega) h)
  · have hdisj : ∀ j₁ j₂ : ℕ, j₁ < j₂ → ∀ x y : C,
        x.val ∈ cube (2 * ((M + S + R + 1) * 2 ^ j₁)) →
        y.val ∉ cube ((M + S + R + 1) * 2 ^ j₂) → x ≠ y := by
      intro j₁ j₂ hj x y hx hy hxy
      have hle : 2 * ((M + S + R + 1) * 2 ^ j₁) ≤ (M + S + R + 1) * 2 ^ j₂ :=
        calc 2 * ((M + S + R + 1) * 2 ^ j₁) = (M + S + R + 1) * 2 ^ (j₁ + 1) := by ring
          _ ≤ (M + S + R + 1) * 2 ^ j₂ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      exact hy (hxy ▸ cube_mono hle hx)
    rcases lt_or_gt_of_ne (hJ i₁ i₂ h) with hlt | hlt
    · exact hdisj _ _ hlt _ _ (hρm _ j₁ hj₁).1 (hρm _ j₂ hj₂).2 heq
    · exact hdisj _ _ hlt _ _ (hρm _ j₂ hj₂).1 (hρm _ j₁ hj₁).2 heq.symm

end Rigidity.Proofs.Section5
