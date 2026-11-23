import Rigidity.Proofs.Probability.BernoulliCube

/-!
# The generalized Efron-Stein inequalities on the Bernoulli cube

For `F : (ι → Bool) → ℝ` under the product Bernoulli law of parameter `p`, the vertical derivative
in the coordinate `i` is `F - E[F | coordinates other than i] = F - coordAvg p i F`, and
`vertVar p F = Σ_i (F - coordAvg p i F)²` is the quantity `𝕍[F]` of Dario, Proposition 2.17
(Armstrong and Lin, Proposition 2.2). With `Δ_i F(x) = F(x^{i,1}) - F(x^{i,0})` the vertical
derivative is `(1 - p) Δ_i F` where `x_i = 1` and `-p Δ_i F` where `x_i = 0`.

* `cubeExp_sq_sub_le_vertVar`: the Efron-Stein inequality `Var(F) ≤ E[𝕍[F]]`;
* `cubeExp_posPart_rpow_le`: Boucheron, Bousquet, Lugosi and Massart (Ann. Probab. 33 (2005)),
  Lemma 3 with `α = q - 1`, in the form available for two-point coordinates: for `q ≥ 2` and
  `Y₊ = max(Y, 0)`,
  `E[Y₊^q] ≤ E[Y₊^{q-1}]^{q/(q-1)} + (q / min(p, 1 - p)) E[Y₊^{q-2} 𝕍[Y]]`.
  It is the tensorization of the `φ`-entropy of `W = Y₊^{q-1}` for `φ(x) = x^{q/(q-1)}`
  (`rpowEntropy_le_sum_coordEntropy`) with the two-point bound
  `E_i[φ(W)] - φ(E_i W) ≤ p (1 - p) (W₁ - W₀)(φ'(W₁) - φ'(W₀))`; BBLM state it with the
  resampled quantity `V⁺`, and for two-point coordinates `p (1 - p) Δ_i² ≤ 𝕍`-terms up to the
  factor `min(p, 1 - p)`.
-/

namespace Rigidity.Probability

open Finset

variable {ι : Type*}

section Coordinate

variable [DecidableEq ι]

/-- The vertical derivative `F - coordAvg p i F` of `F` in the coordinate `i`. -/
def vertDiff (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  F x - coordAvg p i F x

/-- The discrete derivative `F(x^{i,1}) - F(x^{i,0})`. -/
def coordDiff (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  F (Function.update x i true) - F (Function.update x i false)

theorem vertDiff_update_true (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) :
    vertDiff p i F (Function.update x i true) = (1 - p) * coordDiff i F x := by
  simp only [vertDiff, coordAvg, coordDiff, Function.update_idem]
  ring

theorem vertDiff_update_false (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) :
    vertDiff p i F (Function.update x i false) = -(p * coordDiff i F x) := by
  simp only [vertDiff, coordAvg, coordDiff, Function.update_idem]
  ring

theorem vertDiff_sub_const (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (c : ℝ) (x : ι → Bool) :
    vertDiff p i (fun y => F y - c) x = vertDiff p i F x := by
  simp only [vertDiff, coordAvg]
  ring

theorem vertDiff_neg (p : ℝ) (i : ι) (F : (ι → Bool) → ℝ) (x : ι → Bool) :
    vertDiff p i (fun y => -F y) x = -vertDiff p i F x := by
  simp only [vertDiff, coordAvg]
  ring

/-- The average over `i` of `G (F - coordAvg p i F)²`. -/
theorem coordAvg_mul_vertDiff_sq (p : ℝ) (i : ι) (F G : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordAvg p i (fun y => G y * vertDiff p i F y ^ 2) x =
      p * (1 - p) * ((1 - p) * G (Function.update x i true) +
        p * G (Function.update x i false)) * coordDiff i F x ^ 2 := by
  simp only [coordAvg]
  rw [vertDiff_update_true, vertDiff_update_false]
  ring

end Coordinate

/-- The two-point bound on the Jensen gap: `E[φ(W)] - φ(E W) ≤ Cov(W, φ'(W))` for a two-point
law, `φ(x) = x^r`, `r ≥ 1`. -/
theorem jensenGap_le_mul {r p u v : ℝ} (hr : 1 ≤ r) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu : 0 ≤ u)
    (hv : 0 ≤ v) :
    jensenGap r p u v ≤ p * (1 - p) * ((u - v) * (r * u ^ (r - 1) - r * v ^ (r - 1))) := by
  have hq : 0 ≤ 1 - p := by linarith
  have hm : 0 ≤ p * u + (1 - p) * v := by positivity
  have h1 := bregmanRpow_nonneg hr hm hu
  have h2 := bregmanRpow_nonneg hr hm hv
  unfold bregmanRpow at h1 h2
  unfold jensenGap
  nlinarith [mul_le_mul_of_nonneg_left h1 hp0, mul_le_mul_of_nonneg_left h2 hq]

/-- `(a^α - b^α)(a - b) ≤ α (a^{α-1} + b^{α-1}) (a - b)²` for `a, b ≥ 0` and `α ≥ 1`. -/
theorem rpow_sub_rpow_mul_sub_le {α a b : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ α - b ^ α) * (a - b) ≤ α * (a ^ (α - 1) + b ^ (α - 1)) * (a - b) ^ 2 := by
  wlog hab : b ≤ a generalizing a b with H
  · have := H hb ha (le_of_not_ge hab)
    calc (a ^ α - b ^ α) * (a - b) = (b ^ α - a ^ α) * (b - a) := by ring
      _ ≤ α * (b ^ (α - 1) + a ^ (α - 1)) * (b - a) ^ 2 := this
      _ = α * (a ^ (α - 1) + b ^ (α - 1)) * (a - b) ^ 2 := by ring
  have h := bregmanRpow_nonneg hα hb ha
  unfold bregmanRpow at h
  have hd : 0 ≤ a - b := by linarith
  have h1 : (a ^ α - b ^ α) * (a - b) ≤ α * a ^ (α - 1) * (a - b) * (a - b) :=
    mul_le_mul_of_nonneg_right (by linarith) hd
  have hb' : 0 ≤ α * b ^ (α - 1) * (a - b) ^ 2 := by
    have : 0 ≤ b ^ (α - 1) := Real.rpow_nonneg hb _
    have : 0 ≤ α := by linarith
    positivity
  nlinarith

theorem jensenGap_two (p u v : ℝ) : jensenGap 2 p u v = p * (1 - p) * (u - v) ^ 2 := by
  unfold jensenGap
  simp only [Real.rpow_two]
  ring

section Moments

variable [Fintype ι] [DecidableEq ι]

/-- `𝕍[F] = Σ_i (F - coordAvg p i F)²`, the sum of the squared vertical derivatives. -/
def vertVar (p : ℝ) (F : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ := ∑ i, vertDiff p i F x ^ 2

theorem vertVar_nonneg (p : ℝ) (F : (ι → Bool) → ℝ) (x : ι → Bool) : 0 ≤ vertVar p F x :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem vertVar_sub_const (p : ℝ) (F : (ι → Bool) → ℝ) (c : ℝ) (x : ι → Bool) :
    vertVar p (fun y => F y - c) x = vertVar p F x := by
  simp only [vertVar, vertDiff_sub_const]

theorem vertVar_neg (p : ℝ) (F : (ι → Bool) → ℝ) (x : ι → Bool) :
    vertVar p (fun y => -F y) x = vertVar p F x := by
  simp only [vertVar, vertDiff_neg, neg_sq]

theorem cubeExp_sum {κ : Type*} (p : ℝ) (s : Finset κ) (f : κ → (ι → Bool) → ℝ) :
    cubeExp p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeExp p (f i) := by
  simp only [cubeExp, Finset.mul_sum]
  exact Finset.sum_comm

/-- `E[(G - E G)²] = E[G²] - E[G]²`. -/
theorem cubeExp_sq_sub (p : ℝ) (G : (ι → Bool) → ℝ) :
    cubeExp p (fun x => (G x - cubeExp p G) ^ 2) = cubeExp p (fun x => G x ^ 2) - cubeExp p G ^ 2 := by
  have h : (fun x => (G x - cubeExp p G) ^ 2) =
      fun x => (G x ^ 2 - (2 * cubeExp p G) * G x) + cubeExp p G ^ 2 := by
    funext x; ring
  rw [h, cubeExp_add, cubeExp_sub, cubeExp_const_mul, cubeExp_const]
  ring

/-- **The Efron-Stein inequality** on the Bernoulli cube: `Var(F) ≤ E[𝕍[F]]`. -/
theorem cubeExp_sq_sub_le_vertVar {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : (ι → Bool) → ℝ) :
    cubeExp p (fun x => (F x - cubeExp p F) ^ 2) ≤ cubeExp p (vertVar p F) := by
  set M : ℝ := ∑ x, |F x|
  set W : (ι → Bool) → ℝ := fun x => F x + M
  have hW : ∀ x, 0 ≤ W x := fun x => by
    have : |F x| ≤ M := Finset.single_le_sum (f := fun x => |F x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ x)
    simp only [W]
    linarith [neg_abs_le (F x)]
  have htens := rpowEntropy_le_sum_coordEntropy (r := 2) (by norm_num) le_rfl hp0 hp1 hW
  have hEW : cubeExp p W = cubeExp p F + M := by
    simp only [W]
    rw [cubeExp_add, cubeExp_const]
  have hlhs : cubeExp p (fun x => (F x - cubeExp p F) ^ 2) = rpowEntropy 2 p W := by
    have e : (fun x => (F x - cubeExp p F) ^ 2) = fun x => (W x - cubeExp p W) ^ 2 := by
      funext x
      simp only [W, hEW]
      ring
    rw [e, cubeExp_sq_sub]
    simp only [rpowEntropy, Real.rpow_two]
  have hpt : ∀ i x, coordEntropy 2 p i W x = coordAvg p i (fun y => vertDiff p i F y ^ 2) x := by
    intro i x
    simp only [coordEntropy, jensenGap_two, coordAvg]
    rw [vertDiff_update_true, vertDiff_update_false]
    simp only [W, coordDiff]
    ring
  have hpt' : ∀ i, coordEntropy 2 p i W = coordAvg p i (fun y => vertDiff p i F y ^ 2) :=
    fun i => funext (hpt i)
  have hrhs : ∑ i, cubeExp p (coordEntropy 2 p i W) = cubeExp p (vertVar p F) := by
    simp only [hpt', cubeExp_coordAvg]
    unfold vertVar
    rw [cubeExp_sum]
  rw [hlhs, ← hrhs]
  exact htens

omit [Fintype ι] in
/-- The pointwise bound on the entropy in the coordinate `i` of `W = Y₊^{q-1}` for
`φ(x) = x^{q/(q-1)}`. -/
theorem coordEntropy_posPart_le {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 2 ≤ q)
    (Y : (ι → Bool) → ℝ) (i : ι) (x : ι → Bool) :
    coordEntropy (q / (q - 1)) p i (fun y => max (Y y) 0 ^ (q - 1)) x ≤
      q / min p (1 - p) *
        coordAvg p i (fun y => max (Y y) 0 ^ (q - 2) * vertDiff p i Y y ^ 2) x := by
  set c := min p (1 - p) with hc_def
  have hc : 0 < c := lt_min hp0 (by linarith)
  have hq1 : 0 < q - 1 := by linarith
  set r := q / (q - 1) with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def, le_div_iff₀ hq1]; linarith
  set a := max (Y (Function.update x i true)) 0 with ha_def
  set b := max (Y (Function.update x i false)) 0 with hb_def
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hpow : ∀ t : ℝ, 0 ≤ t → (t ^ (q - 1)) ^ (r - 1) = t := by
    intro t ht
    rw [← Real.rpow_mul ht]
    have : (q - 1) * (r - 1) = 1 := by
      rw [hr_def]
      field_simp
      ring
    rw [this, Real.rpow_one]
  have h1 : coordEntropy r p i (fun y => max (Y y) 0 ^ (q - 1)) x ≤
      p * (1 - p) * ((a ^ (q - 1) - b ^ (q - 1)) * (r * a - r * b)) := by
    have := jensenGap_le_mul (r := r) (p := p) hr1 hp0.le hp1.le
      (Real.rpow_nonneg ha (q - 1)) (Real.rpow_nonneg hb (q - 1))
    rwa [hpow a ha, hpow b hb] at this
  have h2 : (a ^ (q - 1) - b ^ (q - 1)) * (a - b) ≤
      (q - 1) * (a ^ (q - 2) + b ^ (q - 2)) * (a - b) ^ 2 := by
    have := rpow_sub_rpow_mul_sub_le (α := q - 1) (by linarith) ha hb
    rwa [show q - 1 - 1 = q - 2 by ring] at this
  have h3 : (a - b) ^ 2 ≤ coordDiff i Y x ^ 2 := by
    have := abs_max_sub_max_le_abs (Y (Function.update x i true))
      (Y (Function.update x i false)) 0
    rw [← sq_abs (a - b), ← sq_abs (coordDiff i Y x)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hA : 0 ≤ a ^ (q - 2) := Real.rpow_nonneg ha _
  have hB : 0 ≤ b ^ (q - 2) := Real.rpow_nonneg hb _
  have hrq : r * (q - 1) = q := by rw [hr_def]; field_simp
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0.le (by linarith)
  have h4 : coordEntropy r p i (fun y => max (Y y) 0 ^ (q - 1)) x ≤
      p * (1 - p) * q * (a ^ (q - 2) + b ^ (q - 2)) * coordDiff i Y x ^ 2 := by
    have e : p * (1 - p) * ((a ^ (q - 1) - b ^ (q - 1)) * (r * a - r * b)) =
        p * (1 - p) * r * ((a ^ (q - 1) - b ^ (q - 1)) * (a - b)) := by ring
    have hr0 : 0 ≤ p * (1 - p) * r := mul_nonneg hpp (by linarith)
    calc _ ≤ p * (1 - p) * ((a ^ (q - 1) - b ^ (q - 1)) * (r * a - r * b)) := h1
      _ = p * (1 - p) * r * ((a ^ (q - 1) - b ^ (q - 1)) * (a - b)) := e
      _ ≤ p * (1 - p) * r * ((q - 1) * (a ^ (q - 2) + b ^ (q - 2)) * (a - b) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hr0
      _ ≤ p * (1 - p) * r * ((q - 1) * (a ^ (q - 2) + b ^ (q - 2)) * coordDiff i Y x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hr0
        exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hq1.le (add_nonneg hA hB))
      _ = p * (1 - p) * (r * (q - 1)) * (a ^ (q - 2) + b ^ (q - 2)) * coordDiff i Y x ^ 2 := by
        ring
      _ = _ := by rw [hrq]
  have key : c * (a ^ (q - 2) + b ^ (q - 2)) ≤ (1 - p) * a ^ (q - 2) + p * b ^ (q - 2) := by
    have hc1 : c ≤ p := min_le_left _ _
    have hc2 : c ≤ 1 - p := min_le_right _ _
    nlinarith
  rw [coordAvg_mul_vertDiff_sq]
  have hD : 0 ≤ coordDiff i Y x ^ 2 := sq_nonneg _
  calc coordEntropy r p i (fun y => max (Y y) 0 ^ (q - 1)) x
      ≤ p * (1 - p) * q * (a ^ (q - 2) + b ^ (q - 2)) * coordDiff i Y x ^ 2 := h4
    _ = q / c * (p * (1 - p) * (c * (a ^ (q - 2) + b ^ (q - 2))) * coordDiff i Y x ^ 2) := by
      field_simp
    _ ≤ q / c * (p * (1 - p) * ((1 - p) * a ^ (q - 2) + p * b ^ (q - 2)) *
          coordDiff i Y x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) hc.le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hpp) hD

/-- **The moment recursion** (Boucheron, Bousquet, Lugosi and Massart, Lemma 3 with
`α = q - 1`): for `q ≥ 2`, `Y₊ = max(Y, 0)` and `c = min(p, 1 - p)`,
`E[Y₊^q] ≤ E[Y₊^{q-1}]^{q/(q-1)} + (q/c) E[Y₊^{q-2} 𝕍[Y]]`. -/
theorem cubeExp_posPart_rpow_le {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 2 ≤ q)
    (Y : (ι → Bool) → ℝ) :
    cubeExp p (fun x => max (Y x) 0 ^ q) ≤
      cubeExp p (fun x => max (Y x) 0 ^ (q - 1)) ^ (q / (q - 1)) +
        q / min p (1 - p) * cubeExp p (fun x => max (Y x) 0 ^ (q - 2) * vertVar p Y x) := by
  have hq1 : 0 < q - 1 := by linarith
  have hr1 : 1 ≤ q / (q - 1) := by rw [le_div_iff₀ hq1]; linarith
  have hr2 : q / (q - 1) ≤ 2 := by rw [div_le_iff₀ hq1]; linarith
  have hW : ∀ x, 0 ≤ max (Y x) 0 ^ (q - 1) := fun x => Real.rpow_nonneg (le_max_right _ _) _
  have htens := rpowEntropy_le_sum_coordEntropy hr1 hr2 hp0.le hp1.le hW
  have hWr : ∀ x, (max (Y x) 0 ^ (q - 1)) ^ (q / (q - 1)) = max (Y x) 0 ^ q := by
    intro x
    rw [← Real.rpow_mul (le_max_right _ _), mul_div_cancel₀ _ hq1.ne']
  have hlhs : rpowEntropy (q / (q - 1)) p (fun x => max (Y x) 0 ^ (q - 1)) =
      cubeExp p (fun x => max (Y x) 0 ^ q) -
        cubeExp p (fun x => max (Y x) 0 ^ (q - 1)) ^ (q / (q - 1)) := by
    simp only [rpowEntropy, hWr]
  have hsum : ∑ i, cubeExp p (coordEntropy (q / (q - 1)) p i (fun y => max (Y y) 0 ^ (q - 1))) ≤
      q / min p (1 - p) * cubeExp p (fun x => max (Y x) 0 ^ (q - 2) * vertVar p Y x) := by
    calc ∑ i, cubeExp p (coordEntropy (q / (q - 1)) p i (fun y => max (Y y) 0 ^ (q - 1)))
        ≤ ∑ i, q / min p (1 - p) *
            cubeExp p (fun y => max (Y y) 0 ^ (q - 2) * vertDiff p i Y y ^ 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc cubeExp p (coordEntropy (q / (q - 1)) p i (fun y => max (Y y) 0 ^ (q - 1)))
              ≤ cubeExp p (fun x => q / min p (1 - p) * coordAvg p i
                  (fun y => max (Y y) 0 ^ (q - 2) * vertDiff p i Y y ^ 2) x) :=
                cubeExp_mono hp0.le hp1.le fun x => coordEntropy_posPart_le hp0 hp1 hq Y i x
            _ = q / min p (1 - p) *
                cubeExp p (fun y => max (Y y) 0 ^ (q - 2) * vertDiff p i Y y ^ 2) := by
                rw [cubeExp_const_mul, cubeExp_coordAvg]
      _ = q / min p (1 - p) * cubeExp p (fun x => max (Y x) 0 ^ (q - 2) * vertVar p Y x) := by
          rw [← Finset.mul_sum, ← cubeExp_sum]
          congr 1
          unfold vertVar
          congr 1
          funext x
          rw [Finset.mul_sum]
  linarith

end Moments

end Rigidity.Probability
