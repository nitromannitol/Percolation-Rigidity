import Rigidity.Steps.S6.UpperBound

/-! # Section 6: the phase bound for a character of the sandpile group

`PhaseBoundStep` (step:6.5-upper, paper L2948-2951 of the corrected draft; D. C. Jerison,
L. Levine and J. Pike, arXiv 1511.00666, (11) and Theorem 3.8, run on the wired graph
`V ∪ {sink}`), with constant `C = (1 + 16 d²) / 8`.

Let `Δ_V θ ∈ ℤ^V` and `λ_θ = r e^{2πiτ}` with `τ = arg λ_θ / 2π ∈ (-1/2, 1/2]`. Write
`θ = τ + z + n` with `n = round(θ - τ) ∈ ℤ^V` and `|z| ≤ 1/2`.
* Eigenvalue: `m r = Σ_x cos 2πz(x)`, and `1 - cos 2πz ≥ 8 z²`, so `8 |z|² ≤ m (1 - r)`.
* Single exit: at a site `w` with one open edge leaving `V`, `Δ_V (τ + z) (w) = τ + Δ_V z (w)`,
  so `τ + Δ_V z (w) ∈ ℤ`; with `|τ| ≤ 1/2` this gives `|τ| ≤ |Δ_V z (w)| ≤ 4d |z|`.
* Dual lattice point: `y = (φ + s, s)` with `φ = τ + z` and `s` chosen so that `Σ y = 0`. Then
  `⟨y, b_x⟩ = Δ_V φ (x) = Δ_V θ (x) - Δ_V n (x) ∈ ℤ`, `y(x) - y(sink) = θ(x) - n(x)`, and,
  `y` being the centred version of `(φ, 0)`, `‖y‖² ≤ ‖(φ - τ, -τ)‖² = |z|² + τ²
  ≤ (1 + 16 d²) |z|² ≤ (1 + 16 d²) m (1 - r) / 8`. -/

open LatticeProb.Percolation Rigidity.Section6 Rigidity.Steps.S6 Classical

namespace Rigidity.Proofs.S6

variable {d : ℕ}

/-- `1 - cos 2πz ≥ 8 z²` for `|z| ≤ 1/2`. -/
theorem eight_mul_sq_le_one_sub_cos {z : ℝ} (hz : |z| ≤ 1 / 2) :
    8 * z ^ 2 ≤ 1 - Real.cos (2 * Real.pi * z) := by
  have hpi := Real.pi_pos
  have habs : |2 * Real.pi * z| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith
  have h := Real.cos_le_one_sub_mul_cos_sq habs
  have heq : 2 / Real.pi ^ 2 * (2 * Real.pi * z) ^ 2 = 8 * z ^ 2 := by
    field_simp
    ring
  linarith

/-- The open neighbours of `x ∈ V` inside `V`. -/
noncomputable def innerNeighbors (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    Finset V :=
  Finset.univ.filter fun y : V => (openGraph ω).Adj x.val y.val

/-- Every open edge at `x ∈ V` ends inside `V` or leaves `V`. -/
theorem degree_eq_card_innerNeighbors_add (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    (openGraph ω).degree x.val = (innerNeighbors ω V x).card + (exitNeighbors ω V x).card := by
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (openGraph ω).neighborFinset x.val) (· ∈ V)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  have h1 : (innerNeighbors ω V x).card =
      (((openGraph ω).neighborFinset x.val).filter (· ∈ V)).card := by
    refine Finset.card_bij (fun y _ => y.val) ?_ ?_ ?_
    · intro y hy
      simp only [innerNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp [SimpleGraph.mem_neighborFinset, hy]
    · intro a _ b _ h
      exact Subtype.val_injective h
    · intro b hb
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hb
      exact ⟨⟨b, hb.2⟩, by simp [innerNeighbors, hb.1], rfl⟩
  rw [h1, exitNeighbors]
  omega

/-- The neighbour sum of `realToppling` as a sum over the inner neighbours. -/
theorem sum_ite_adj_eq (ω : Configuration d) (V : Finset (Vertex d)) (f : V → ℝ) (x : V) :
    (∑ y : V, if (openGraph ω).Adj x.val y.val then f y else 0) =
      ∑ y ∈ innerNeighbors ω V x, f y := by
  rw [innerNeighbors, Finset.sum_filter]

theorem realToppling_sub (ω : Configuration d) (V : Finset (Vertex d)) (f g : V → ℝ) (x : V) :
    realToppling ω V (fun u => f u - g u) x = realToppling ω V f x - realToppling ω V g x := by
  simp only [realToppling, sum_ite_adj_eq, Finset.sum_sub_distrib]
  ring

theorem realToppling_add_const (ω : Configuration d) (V : Finset (Vertex d)) (f : V → ℝ)
    (c : ℝ) (x : V) :
    realToppling ω V (fun u => f u + c) x =
      realToppling ω V f x + (exitNeighbors ω V x).card * c := by
  simp only [realToppling, sum_ite_adj_eq, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  rw [degree_eq_card_innerNeighbors_add]
  push_cast
  ring

/-- `Δ_V` maps `ℤ^V` into `ℤ^V`. -/
theorem realToppling_intCast (ω : Configuration d) (V : Finset (Vertex d)) (n : V → ℤ) (x : V) :
    ∃ k : ℤ, realToppling ω V (fun u => (n u : ℝ)) x = k :=
  ⟨(openGraph ω).degree x.val * n x - ∑ y ∈ innerNeighbors ω V x, n y, by
    simp only [realToppling, sum_ite_adj_eq]
    push_cast
    ring⟩

/-- `Σ_u g(u) b_x(u) = Δ_V g (x)`: the `V`-part of the wired column. -/
theorem sum_mul_wiredColumn_some (ω : Configuration d) (V : Finset (Vertex d)) (g : V → ℝ)
    (x : V) : ∑ u : V, g u * wiredColumn ω V x (some u) = realToppling ω V g x := by
  have hpt : ∀ u : V, g u * wiredColumn ω V x (some u) =
      (if u = x then g u * (openGraph ω).degree x.val else 0) -
        if (openGraph ω).Adj x.val u.val then g u else 0 := by
    intro u
    rw [wiredColumn_some]
    by_cases hu : u = x
    · have ha : ¬ (openGraph ω).Adj x.val u.val := by
        rw [hu]
        exact (openGraph ω).loopless.irrefl _
      simp [hu]
    · by_cases ha : (openGraph ω).Adj x.val u.val <;> simp [hu, ha]
  simp only [hpt, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    realToppling]
  ring

/-- `⟨(φ + s, s), b_x⟩ = Δ_V φ (x)`: the constant shift is killed by the column, whose entries
sum to zero. -/
theorem inner_wiredColumn (ω : Configuration d) (V : Finset (Vertex d)) (φ : V → ℝ) (s : ℝ)
    (x : V) :
    inner ℝ (WithLp.toLp 2 fun o : Option V => Option.elim o s fun u => φ u + s :
        EuclideanSpace ℝ (Option V)) (wiredColumn ω V x) = realToppling ω V φ x := by
  rw [PiLp.inner_apply, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, wiredColumn_none,
    Real.inner_apply]
  have h := sum_mul_wiredColumn_some ω V (fun u => φ u + s) x
  rw [realToppling_add_const] at h
  rw [h]
  ring

/-- Centring decreases the sum of squares: if `a + Σ v = 0` then
`a² + Σ v² ≤ (a - c)² + Σ (v - c)²`. -/
theorem sq_add_sum_sq_le_of_sum_eq_zero {ι : Type*} [Fintype ι] (a c : ℝ) (v : ι → ℝ)
    (h : a + ∑ i, v i = 0) :
    a ^ 2 + ∑ i, v i ^ 2 ≤ (a - c) ^ 2 + ∑ i, (v i - c) ^ 2 := by
  have hexp : ∑ i, (v i - c) ^ 2 =
      ∑ i, v i ^ 2 + (-2 * c) * ∑ i, v i + Fintype.card ι * c ^ 2 := by
    rw [Finset.mul_sum]
    simp only [show ∀ i, (v i - c) ^ 2 = v i ^ 2 + -2 * c * v i + c ^ 2 from fun i => by ring,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexp]
  have hv : ∑ i, v i = -a := by linarith
  rw [hv]
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  nlinarith [mul_nonneg hcard (sq_nonneg c)]

/-- If `|τ| ≤ 1/2` and `τ + A ∈ ℤ`, then `|τ| ≤ |A|`. -/
theorem abs_le_abs_of_add_eq_int {τ A : ℝ} (hτ : |τ| ≤ 1 / 2) {K : ℤ} (hK : τ + A = K) :
    |τ| ≤ |A| := by
  rcases eq_or_ne K 0 with h | h
  · rw [h, Int.cast_zero] at hK
    rw [show A = -τ by linarith, abs_neg]
  · have h1 : (1 : ℝ) ≤ |(K : ℝ)| := by exact_mod_cast Int.one_le_abs h
    have h2 : |(K : ℝ)| ≤ |τ| + |A| := hK ▸ abs_add_le τ A
    linarith

/-- step:6.5-upper, phase bound (JLP (11) and Theorem 3.8, single-exit form), with
`C = (1 + 16 d²) / 8`. -/
theorem phaseBoundStep : PhaseBoundStep d := by
  refine ⟨(1 + 16 * (d : ℝ) ^ 2) / 8, by positivity, ?_⟩
  rintro ω V ⟨w, hwV, hw⟩ θ hθ
  set m : ℝ := (V.card : ℝ) with hm
  have hcard : (Fintype.card V : ℝ) = m := by rw [hm, Fintype.card_coe]
  have hmpos : 0 < m := by
    rw [hm]
    exact_mod_cast Finset.card_pos.2 ⟨w, hwV⟩
  set lam := phaseEigenvalue V θ with hlam
  set r := ‖lam‖ with hr
  set τ : ℝ := Complex.arg lam / (2 * Real.pi) with hτdef
  set n : V → ℤ := fun x => round (θ x - τ) with hn
  set z : V → ℝ := fun x => θ x - τ - n x with hz
  set φ : V → ℝ := fun x => z x + τ with hφ
  set s : ℝ := -(∑ x, φ x) / (m + 1) with hs
  set y : EuclideanSpace ℝ (Option V) :=
    WithLp.toLp 2 fun o : Option V => Option.elim o s fun u => φ u + s with hy
  have hyn : y none = s := rfl
  have hys : ∀ u, y (some u) = φ u + s := fun _ => rfl
  have hpi := Real.pi_pos
  -- `Σ y = 0`
  have hsum : ∑ o, y o = 0 := by
    rw [Fintype.sum_option, hyn]
    simp only [hys, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcard, hs]
    field_simp
    ring
  -- the phases: `|τ| ≤ 1/2`, `|z| ≤ 1/2`
  have hτ : |τ| ≤ 1 / 2 := by
    rw [hτdef, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      div_le_iff₀ (by positivity)]
    have := Complex.neg_pi_lt_arg lam
    have := Complex.arg_le_pi lam
    rw [abs_le]
    constructor <;> linarith
  have hzabs : ∀ x, |z x| ≤ 1 / 2 := fun x => abs_sub_round (θ x - τ)
  -- the eigenvalue: `m r = Σ cos 2πz`
  have hmr : m * r = ∑ x, Real.cos (2 * Real.pi * z x) := by
    have harg : Complex.arg lam = 2 * Real.pi * τ := by
      rw [hτdef]
      field_simp
    have h1 : ((m * r : ℝ) : ℂ) =
        ∑ x, Complex.exp (((2 * Real.pi * (θ x - τ) : ℝ) : ℂ) * Complex.I) := by
      have hl : lam = r * Complex.exp (((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I) := by
        rw [hr, ← harg]
        exact (Complex.norm_mul_exp_arg_mul_I lam).symm
      have hl' : (m : ℂ) * lam = ∑ x, Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I) := by
        rw [hlam, phaseEigenvalue, ← mul_assoc, hm, Complex.ofReal_natCast,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨w, hwV⟩).ne'), one_mul]
      have he : ∀ x : V, Complex.exp (((2 * Real.pi * (θ x - τ) : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((2 * Real.pi * θ x : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-(((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I)) := by
        intro x
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hE : Complex.exp (((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      simp only [he, ← Finset.sum_mul, ← hl', hl]
      push_cast at hE ⊢
      linear_combination (-((r : ℂ) * (m : ℂ))) * hE
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, Complex.re_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.exp_ofReal_mul_I_re]
    have : 2 * Real.pi * (θ x - τ) = 2 * Real.pi * z x + (n x : ℤ) * (2 * Real.pi) := by
      rw [hz]
      ring
    rw [this, Real.cos_add_int_mul_two_pi]
  -- `8 |z|² ≤ m (1 - r)`
  have hz2 : 8 * ∑ x, z x ^ 2 ≤ m * (1 - r) := by
    have h := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
      eight_mul_sq_le_one_sub_cos (hzabs x)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcard, mul_one, ← hmr] at h
    linarith
  -- the single exit: `|τ| ≤ |Δ_V z (w)| ≤ 4d |z|`
  set w' : V := ⟨w, hwV⟩
  set Z : ℝ := Real.sqrt (∑ x, z x ^ 2) with hZ
  have hzZ : ∀ x, |z x| ≤ Z := fun x => Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun x => z x ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x))
  have hA : |realToppling ω V z w'| ≤ 4 * d * Z := by
    have hdeg : ((openGraph ω).degree w : ℝ) ≤ 2 * d := by exact_mod_cast openGraph_degree_le ω w
    have hinn : ((innerNeighbors ω V w').card : ℝ) ≤ 2 * d := by
      have := degree_eq_card_innerNeighbors_add ω V w'
      have h' : (innerNeighbors ω V w').card ≤ 2 * d := by
        have := openGraph_degree_le ω w
        simp only [w'] at *
        omega
      exact_mod_cast h'
    have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
    rw [realToppling, sum_ite_adj_eq]
    calc |((openGraph ω).degree w' : ℝ) * z w' - ∑ y ∈ innerNeighbors ω V w', z y|
        ≤ |((openGraph ω).degree w' : ℝ) * z w'| + |∑ y ∈ innerNeighbors ω V w', z y| :=
          abs_sub _ _
      _ ≤ (openGraph ω).degree w' * Z + (innerNeighbors ω V w').card * Z := by
          gcongr
          · rw [abs_mul, Nat.abs_cast]
            exact mul_le_mul_of_nonneg_left (hzZ w') (Nat.cast_nonneg _)
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_le_sum fun x _ => hzZ x
      _ ≤ 2 * d * Z + 2 * d * Z := by gcongr
      _ = 4 * d * Z := by ring
  have hτA : |τ| ≤ |realToppling ω V z w'| := by
    obtain ⟨k, hk⟩ := hθ w'
    obtain ⟨k', hk'⟩ := realToppling_intCast ω V n w'
    refine abs_le_abs_of_add_eq_int hτ (K := k - k') ?_
    have h1 := realToppling_sub ω V θ (fun u => (n u : ℝ)) w'
    have h2 : (fun u => θ u - (n u : ℝ)) = fun u => z u + τ := by
      funext u
      simp only [hz]
      ring
    rw [h2, realToppling_add_const, hw, hk, hk', Nat.cast_one, one_mul] at h1
    push_cast
    linarith
  have hτ2 : τ ^ 2 ≤ 16 * d ^ 2 * ∑ x, z x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg τ) (hτA.trans hA) 2
    rw [sq_abs, mul_pow, hZ, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
    linarith
  refine ⟨y, hsum, fun x => ?_, fun x => ⟨-n x, ?_⟩, ?_⟩
  · -- `⟨y, b_x⟩ = Δ_V θ (x) - Δ_V n (x)`
    obtain ⟨k, hk⟩ := hθ x
    obtain ⟨k', hk'⟩ := realToppling_intCast ω V n x
    refine ⟨k - k', ?_⟩
    rw [hy, inner_wiredColumn]
    have h2 : φ = fun u => θ u - (n u : ℝ) := by
      funext u
      simp only [hφ, hz]
      ring
    rw [h2, realToppling_sub, hk, hk']
    push_cast
    ring
  · rw [hys, hyn, hφ, hz]
    push_cast
    ring
  · -- `‖y‖² ≤ τ² + |z|² ≤ C m (1 - r)`
    have hcen := sq_add_sum_sq_le_of_sum_eq_zero s (s + τ) (fun u => φ u + s)
      (by rw [Fintype.sum_option, hyn] at hsum; simpa only [hys] using hsum)
    have hnorm : ‖y‖ ^ 2 = s ^ 2 + ∑ u, (φ u + s) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_option]
      simp only [Real.norm_eq_abs, sq_abs, hyn, hys]
    have hrhs : (s - (s + τ)) ^ 2 + ∑ u, (φ u + s - (s + τ)) ^ 2 = τ ^ 2 + ∑ u, z u ^ 2 := by
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun u _ => ?_
        rw [hφ]
        ring
    rw [hnorm]
    rw [hrhs] at hcen
    have hz0 : 0 ≤ ∑ u, z u ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc s ^ 2 + ∑ u, (φ u + s) ^ 2 ≤ τ ^ 2 + ∑ u, z u ^ 2 := hcen
      _ ≤ (1 + 16 * d ^ 2) * ∑ u, z u ^ 2 := by linarith
      _ ≤ (1 + 16 * d ^ 2) * (m * (1 - r) / 8) := by gcongr; linarith
      _ = (1 + 16 * (d : ℝ) ^ 2) / 8 * V.card * (1 - ‖phaseEigenvalue V θ‖) := by
          rw [hm, hr, hlam]
          ring

end Rigidity.Proofs.S6
