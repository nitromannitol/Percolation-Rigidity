import Rigidity.Proofs.Dirichlet.MesoscopicPoincare

/-!
# The mesoscopic interpolation of Lemma 6.2

Given `w`, a cutoff `η` with values in `[0, 1]` and `|∇η| ≤ 1/r`, and the mesoscopic average
`ξ = ξ_N(w)`, the interpolation `ũ = w + η (ξ − w)` (that is, `η ξ + (1 − η) w`) equals `w` where
`η = 0`, has gradient `∇ξ` on the edges where `η = 1` at both endpoints, and satisfies, for
`s ≥ 1` and `B ⊇ A + {0, …, N − 1}^d`,
`Σ_{x∈A} Σ_j |∇_j ũ(x)|^s ≤ 3^{s-1} (1 + 2^s + d^s (N/r)^s) Σ_{y∈B} Σ_j |∇_j w(y)|^s`.

This is the construction `ũ = η ξ + (1 − η) w` of the proof of Armstrong–Dario, Lemma 6.2, and
its estimate (6.28) (`⨍ |∇ũ|^{p'} ≤ C M^{p'}`, from `3^n ≤ 3^l`); on the lattice the gradient of
`ξ` is the mesoscopic average of the gradient of `w` (`cubeAverage_add_unit_sub`).
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The interpolation `ũ = w + η (ξ_N(w) − w)` between `w` and its mesoscopic average. -/
noncomputable def mesoInterpolation (N : ℕ) (η w : Vertex d → ℝ) (x : Vertex d) : ℝ :=
  w x + η x * (cubeAverage N w x - w x)

theorem mesoInterpolation_eq_of_eq_zero (N : ℕ) {η : Vertex d → ℝ} (w : Vertex d → ℝ)
    {x : Vertex d} (hx : η x = 0) : mesoInterpolation N η w x = w x := by
  simp [mesoInterpolation, hx]

theorem mesoInterpolation_eq_of_eq_one (N : ℕ) {η : Vertex d → ℝ} (w : Vertex d → ℝ)
    {x : Vertex d} (hx : η x = 1) : mesoInterpolation N η w x = cubeAverage N w x := by
  simp [mesoInterpolation, hx]

/-- **Discrete product rule** for the interpolation:
`∇_j ũ(x) = ∇_j w(x) + η(x + e_j) (∇_j ξ(x) − ∇_j w(x)) + (ξ(x) − w(x)) ∇_j η(x)`. -/
theorem mesoInterpolation_grad (N : ℕ) (η w : Vertex d → ℝ) (x : Vertex d) (j : Fin d) :
    mesoInterpolation N η w (x + unit j) - mesoInterpolation N η w x =
      (w (x + unit j) - w x) + η (x + unit j) * ((cubeAverage N w (x + unit j) -
        cubeAverage N w x) - (w (x + unit j) - w x)) +
        (cubeAverage N w x - w x) * (η (x + unit j) - η x) := by
  simp only [mesoInterpolation]
  ring

/-- The gradient of a cube average in `L^s`: `Σ_{x∈A} |∇_j ξ_N(x)|^s ≤ Σ_{y∈B} |∇_j w(y)|^s` for
`B ⊇ A + {0, …, N − 1}^d`. -/
theorem sum_abs_grad_cubeAverage_rpow_le (A B : Finset (Vertex d)) {N : ℕ} (hN : 0 < N)
    (w : Vertex d → ℝ) (j : Fin d) {s : ℝ} (hs : 1 ≤ s)
    (hB : ∀ x ∈ A, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    ∑ x ∈ A, |cubeAverage N w (x + unit j) - cubeAverage N w x| ^ s ≤
      ∑ y ∈ B, |w (y + unit j) - w y| ^ s := by
  classical
  set Z := (cornerCube (0 : Vertex d) N).vertices
  have hZcard : (#Z : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have hZpos : (0 : ℝ) < #Z := by rw [hZcard]; positivity
  set F : Vertex d → ℝ := fun y => w (y + unit j) - w y
  have hgrad : ∀ x, cubeAverage N w (x + unit j) - cubeAverage N w x =
      (∑ z ∈ Z, F (x + z)) / #Z := by
    intro x
    rw [cubeAverage_add_unit_sub, hZcard]
    congr 1
    have h := sum_cornerCube_add (0 : Vertex d) x N F
    rw [zero_add] at h
    rw [h]
    exact Finset.sum_congr rfl fun z _ => by
      simp only [F]
      rw [add_comm z x, add_right_comm]
  have hjensen : ∀ x, |cubeAverage N w (x + unit j) - cubeAverage N w x| ^ s ≤
      (∑ z ∈ Z, |F (x + z)| ^ s) / #Z := by
    intro x
    rw [hgrad, abs_div, abs_of_pos hZpos, Real.div_rpow (abs_nonneg _) hZpos.le,
      div_le_div_iff₀ (by positivity) hZpos]
    have h := abs_sum_rpow_le Z (fun z => F (x + z)) hs
    calc |∑ z ∈ Z, F (x + z)| ^ s * #Z
        ≤ (#Z : ℝ) ^ (s - 1) * (∑ z ∈ Z, |F (x + z)| ^ s) * #Z :=
          mul_le_mul_of_nonneg_right h hZpos.le
      _ = (∑ z ∈ Z, |F (x + z)| ^ s) * (#Z : ℝ) ^ s := by
          rw [mul_comm ((#Z : ℝ) ^ (s - 1)), mul_assoc, ← Real.rpow_add_one hZpos.ne',
            sub_add_cancel]
  have hshift : ∀ z ∈ Z, ∑ x ∈ A, |F (x + z)| ^ s ≤ ∑ y ∈ B, |F y| ^ s := by
    intro z hz
    calc ∑ x ∈ A, |F (x + z)| ^ s = ∑ y ∈ A.map (addRightEmbedding z), |F y| ^ s := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ y ∈ B, |F y| ^ s := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
            fun _ _ _ => by positivity
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
          exact hB x hx z hz
  calc ∑ x ∈ A, |cubeAverage N w (x + unit j) - cubeAverage N w x| ^ s
      ≤ ∑ x ∈ A, (∑ z ∈ Z, |F (x + z)| ^ s) / #Z := Finset.sum_le_sum fun x _ => hjensen x
    _ = (∑ z ∈ Z, ∑ x ∈ A, |F (x + z)| ^ s) / #Z := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ ≤ (∑ _z ∈ Z, ∑ y ∈ B, |F y| ^ s) / #Z :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hshift) hZpos.le
    _ = ∑ y ∈ B, |F y| ^ s := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp

/-- `(a + b + c)^s ≤ 3^{s-1} (a^s + b^s + c^s)` for `a, b, c ≥ 0` and `s ≥ 1`. -/
theorem add_add_rpow_le_of_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {s : ℝ}
    (hs : 1 ≤ s) : (a + b + c) ^ s ≤ (3 : ℝ) ^ (s - 1) * (a ^ s + b ^ s + c ^ s) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin 3))
    (f := ![a, b, c]) hs fun i _ => by fin_cases i <;> simpa
  simpa [Fin.sum_univ_three, add_assoc] using h

/-- **The `L^s` bound of the interpolation** (discrete form of Armstrong–Dario (6.28)): for
`0 ≤ η ≤ 1`, `|∇η| ≤ 1/r` at the points of `A`, `r > 0`, `s ≥ 1` and `B ⊇ A + {0, …, N − 1}^d`,
`Σ_{x∈A} Σ_j |∇_j ũ(x)|^s ≤ 3^{s-1} (1 + 2^s + d^s (N/r)^s) Σ_{y∈B} Σ_j |∇_j w(y)|^s`. -/
theorem sum_abs_grad_mesoInterpolation_rpow_le (A B : Finset (Vertex d)) {N r : ℕ} (hN : 0 < N)
    (hr : 0 < r) (η w : Vertex d → ℝ) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηg : ∀ x ∈ A, ∀ j : Fin d, |η (x + unit j) - η x| ≤ 1 / r) {s : ℝ} (hs : 1 ≤ s)
    (hB : ∀ x ∈ A, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    ∑ x ∈ A, ∑ j : Fin d,
        |mesoInterpolation N η w (x + unit j) - mesoInterpolation N η w x| ^ s ≤
      (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) *
        ∑ y ∈ B, ∑ j : Fin d, |w (y + unit j) - w y| ^ s := by
  classical
  have hs0 : 0 ≤ s := by linarith
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hAB : A ⊆ B := fun x hx => by
    have h0 : (0 : Vertex d) ∈ (cornerCube 0 N).vertices := by
      rw [IntegerCube.mem_vertices]
      intro k
      simp [cornerCube, hN]
    simpa using hB x hx 0 h0
  set G : Vertex d → ℝ := fun y => ∑ j : Fin d, |w (y + unit j) - w y| ^ s
  have hG : ∀ y, 0 ≤ G y := fun y => Finset.sum_nonneg fun _ _ => by positivity
  set ξ := cubeAverage N w
  -- pointwise bound
  have hpt : ∀ x ∈ A, ∀ j : Fin d,
      |mesoInterpolation N η w (x + unit j) - mesoInterpolation N η w x| ^ s ≤
        (3 : ℝ) ^ (s - 1) * (|ξ (x + unit j) - ξ x| ^ s + 2 ^ s * |w (x + unit j) - w x| ^ s +
          (1 / (r : ℝ)) ^ s * |ξ x - w x| ^ s) := by
    intro x hx j
    rw [mesoInterpolation_grad]
    set a := w (x + unit j) - w x
    set b := ξ (x + unit j) - ξ x
    set e := ξ x - w x
    have hη' := hη0 (x + unit j)
    have hη1' := hη1 (x + unit j)
    have hbound : |a + η (x + unit j) * (b - a) + e * (η (x + unit j) - η x)| ≤
        |b| + 2 * |a| + 1 / r * |e| := by
      have h1 : |η (x + unit j) * (b - a)| ≤ |b| + |a| := by
        rw [abs_mul, abs_of_nonneg hη']
        calc η (x + unit j) * |b - a| ≤ 1 * |b - a| :=
              mul_le_mul_of_nonneg_right hη1' (abs_nonneg _)
          _ ≤ |b| + |a| := by rw [one_mul]; exact abs_sub _ _
      have h2 : |e * (η (x + unit j) - η x)| ≤ 1 / r * |e| := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hηg x hx j) (abs_nonneg _)
      calc |a + η (x + unit j) * (b - a) + e * (η (x + unit j) - η x)|
          ≤ |a + η (x + unit j) * (b - a)| + |e * (η (x + unit j) - η x)| := abs_add_le _ _
        _ ≤ |a| + |η (x + unit j) * (b - a)| + |e * (η (x + unit j) - η x)| := by
            linarith [abs_add_le a (η (x + unit j) * (b - a))]
        _ ≤ |a| + (|b| + |a|) + 1 / r * |e| := by linarith
        _ = |b| + 2 * |a| + 1 / r * |e| := by ring
    have h3 := add_add_rpow_le_of_nonneg (abs_nonneg b) (by positivity : 0 ≤ 2 * |a|)
      (by positivity : 0 ≤ 1 / (r : ℝ) * |e|) hs
    rw [Real.mul_rpow (by norm_num) (abs_nonneg _), Real.mul_rpow (by positivity)
      (abs_nonneg _)] at h3
    exact (Real.rpow_le_rpow (abs_nonneg _) hbound hs0).trans h3
  -- the three sums
  have hS1 : ∑ x ∈ A, ∑ j : Fin d, |ξ (x + unit j) - ξ x| ^ s ≤ ∑ y ∈ B, G y := by
    rw [Finset.sum_comm]
    simp only [G]
    rw [Finset.sum_comm (s := B)]
    exact Finset.sum_le_sum fun j _ => sum_abs_grad_cubeAverage_rpow_le A B hN w j hs hB
  have hS2 : ∑ x ∈ A, ∑ j : Fin d, |w (x + unit j) - w x| ^ s ≤ ∑ y ∈ B, G y :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB fun y _ _ => hG y
  have hS3 : ∑ x ∈ A, ∑ _j : Fin d, |ξ x - w x| ^ s ≤
      (d : ℝ) * ((d : ℝ) ^ (s - 1) * (N : ℝ) ^ s * ∑ y ∈ B, G y) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_abs_cubeAverage_sub_rpow_le A B hN w hs hB)
      (Nat.cast_nonneg d)
  have hd3 : (d : ℝ) * ((d : ℝ) ^ (s - 1) * (N : ℝ) ^ s) * (1 / (r : ℝ)) ^ s =
      (d : ℝ) ^ s * ((N : ℝ) / r) ^ s := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp [Real.zero_rpow (show s ≠ 0 by linarith)]
    · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      rw [Real.rpow_sub_one hd'.ne', Real.div_rpow (Nat.cast_nonneg N) hr'.le,
        Real.div_rpow zero_le_one hr'.le, Real.one_rpow]
      field_simp
  calc ∑ x ∈ A, ∑ j : Fin d,
        |mesoInterpolation N η w (x + unit j) - mesoInterpolation N η w x| ^ s
      ≤ ∑ x ∈ A, ∑ j : Fin d, (3 : ℝ) ^ (s - 1) * (|ξ (x + unit j) - ξ x| ^ s +
          2 ^ s * |w (x + unit j) - w x| ^ s + (1 / (r : ℝ)) ^ s * |ξ x - w x| ^ s) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun j _ => hpt x hx j
    _ = (3 : ℝ) ^ (s - 1) * (∑ x ∈ A, ∑ j : Fin d, |ξ (x + unit j) - ξ x| ^ s +
          2 ^ s * ∑ x ∈ A, ∑ j : Fin d, |w (x + unit j) - w x| ^ s +
          (1 / (r : ℝ)) ^ s * ∑ x ∈ A, ∑ _j : Fin d, |ξ x - w x| ^ s) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ (3 : ℝ) ^ (s - 1) * (∑ y ∈ B, G y + 2 ^ s * ∑ y ∈ B, G y +
          (1 / (r : ℝ)) ^ s * ((d : ℝ) * ((d : ℝ) ^ (s - 1) * (N : ℝ) ^ s * ∑ y ∈ B, G y))) := by
        gcongr
    _ = (3 : ℝ) ^ (s - 1) * (1 + 2 ^ s + (d : ℝ) ^ s * ((N : ℝ) / r) ^ s) * ∑ y ∈ B, G y := by
        rw [← hd3]
        ring

end Rigidity.Dirichlet
