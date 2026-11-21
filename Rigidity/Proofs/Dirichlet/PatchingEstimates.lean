import Rigidity.Proofs.Dirichlet.AffineApproximation
import Rigidity.Proofs.Dirichlet.MesoscopicPoincare

/-!
# Mesoscopic slopes and values of neighbouring cubes

For the mesoscopic averages `ζ(y) = ⟨g⟩_{y + □}` and slopes `p_i(y) = ⟨∇_i g⟩_{y + □}` on cubes
of side `N`, and a shift `t e_j` with `t ≤ N`:
* `|p_i(y + t e_j) − p_i(y)|^s ≤ t^s N^{-d} Σ_B |∇_j∇_i g|^s` for `B` containing the segments
  `x + {0, …, t − 1} e_j`, `x ∈ y + □` (Jensen and one-dimensional telescoping);
* `ζ(y + N e_j) − ζ(y) − N p_j(y) = Σ_{t<N} (p_j(y + t e_j) − p_j(y))`, since `∇_j ζ = p_j`.

These are the two estimates of the proof of Armstrong–Dario, Lemma 6.3, Step 2, for the edges
joining neighbouring mesoscopic cubes `y + □_n` and `y' + □_n`:
`|p(y) − p(y')| ≤ C 3^n ⨍ |∇∇u_hom|` and `|p(y)·(y' − y) + ζ(y) − ζ(y')| ≤ C 3^{2n} ⨍ |∇∇u_hom|`.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Translation along a coordinate in `L^s`**: `Σ_{x∈A} |h(x + t e_j) − h(x)|^s ≤
  t^s Σ_{y∈B} |∇_j h(y)|^s` for `B ⊇ {x + r e_j : x ∈ A, r < t}`. -/
theorem sum_abs_sub_rpow_le_shift (A B : Finset (Vertex d)) (h : Vertex d → ℝ) (j : Fin d)
    (t : ℕ) {s : ℝ} (hs : 1 ≤ s) (hB : ∀ x ∈ A, ∀ r < t, x + (r : ℤ) • unit j ∈ B) :
    ∑ x ∈ A, |h (x + (t : ℤ) • unit j) - h x| ^ s ≤
      (t : ℝ) ^ s * ∑ y ∈ B, |h (y + unit j) - h y| ^ s := by
  have hshift : ∀ r < t, ∑ x ∈ A, |h (x + (r : ℤ) • unit j + unit j) - h (x + (r : ℤ) • unit j)| ^ s
      ≤ ∑ y ∈ B, |h (y + unit j) - h y| ^ s := by
    intro r hr
    calc ∑ x ∈ A, |h (x + (r : ℤ) • unit j + unit j) - h (x + (r : ℤ) • unit j)| ^ s
        = ∑ y ∈ A.map (addRightEmbedding ((r : ℤ) • unit j)), |h (y + unit j) - h y| ^ s := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ y ∈ B, |h (y + unit j) - h y| ^ s := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
            fun _ _ _ => by positivity
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
          exact hB x hx r hr
  calc ∑ x ∈ A, |h (x + (t : ℤ) • unit j) - h x| ^ s
      ≤ ∑ x ∈ A, (t : ℝ) ^ (s - 1) * ∑ r ∈ Finset.range t,
          |h (x + (r : ℤ) • unit j + unit j) - h (x + (r : ℤ) • unit j)| ^ s :=
        Finset.sum_le_sum fun x _ => abs_sub_rpow_le_line h x j t hs
    _ = (t : ℝ) ^ (s - 1) * ∑ r ∈ Finset.range t, ∑ x ∈ A,
          |h (x + (r : ℤ) • unit j + unit j) - h (x + (r : ℤ) • unit j)| ^ s := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (t : ℝ) ^ (s - 1) * ∑ _r ∈ Finset.range t, ∑ y ∈ B, |h (y + unit j) - h y| ^ s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r hr =>
          hshift r (Finset.mem_range.mp hr)) (by positivity)
    _ ≤ (t : ℝ) ^ s * ∑ y ∈ B, |h (y + unit j) - h y| ^ s := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          simp only [Nat.cast_zero, mul_zero]
          exact Real.rpow_nonneg le_rfl s
        · have ht' : (0 : ℝ) < t := by exact_mod_cast ht
          rw [← Real.rpow_add_one ht'.ne', sub_add_cancel]

/-- **Jensen for translated cube averages**: `|⟨h⟩_{y + v + □} − ⟨h⟩_{y + □}|^s ≤
  N^{-d} Σ_{x ∈ y + □} |h(x + v) − h(x)|^s`. -/
theorem abs_cubeAverage_add_sub_rpow_le {N : ℕ} (hN : 0 < N) (h : Vertex d → ℝ)
    (y v : Vertex d) {s : ℝ} (hs : 1 ≤ s) :
    |cubeAverage N h (y + v) - cubeAverage N h y| ^ s ≤
      (∑ x ∈ (cornerCube y N).vertices, |h (x + v) - h x| ^ s) / (N : ℝ) ^ d := by
  set Q := (cornerCube y N).vertices
  have hQcard : (#Q : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have hQpos : (0 : ℝ) < #Q := by rw [hQcard]; positivity
  have hdiff : cubeAverage N h (y + v) - cubeAverage N h y =
      (∑ x ∈ Q, (h (x + v) - h x)) / #Q := by
    rw [cubeAverage, cubeAverage, sum_cornerCube_add, hQcard, ← sub_div, Finset.sum_sub_distrib]
  rw [hdiff, abs_div, abs_of_pos hQpos, Real.div_rpow (abs_nonneg _) hQpos.le, ← hQcard,
    div_le_div_iff₀ (by positivity) hQpos]
  calc |∑ x ∈ Q, (h (x + v) - h x)| ^ s * #Q
      ≤ (#Q : ℝ) ^ (s - 1) * (∑ x ∈ Q, |h (x + v) - h x| ^ s) * #Q :=
        mul_le_mul_of_nonneg_right (abs_sum_rpow_le Q _ hs) hQpos.le
    _ = (∑ x ∈ Q, |h (x + v) - h x| ^ s) * (#Q : ℝ) ^ s := by
        rw [mul_comm ((#Q : ℝ) ^ (s - 1)), mul_assoc, ← Real.rpow_add_one hQpos.ne',
          sub_add_cancel]

/-- **Slopes of neighbouring cubes**:
`|p_i(y + t e_j) − p_i(y)|^s ≤ t^s N^{-d} Σ_{w∈B} |∇_j∇_i g(w)|^s` for
`B ⊇ {x + r e_j : x ∈ y + □, r < t}`. -/
theorem abs_cubeSlope_add_sub_rpow_le {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (y : Vertex d)
    (i j : Fin d) (t : ℕ) {s : ℝ} (hs : 1 ≤ s) (B : Finset (Vertex d))
    (hB : ∀ x ∈ (cornerCube y N).vertices, ∀ r < t, x + (r : ℤ) • unit j ∈ B) :
    |cubeSlope N g (y + (t : ℤ) • unit j) i - cubeSlope N g y i| ^ s ≤
      (t : ℝ) ^ s * (∑ w ∈ B, |(g (w + unit j + unit i) - g (w + unit j)) -
        (g (w + unit i) - g w)| ^ s) / (N : ℝ) ^ d := by
  have h1 := abs_cubeAverage_add_sub_rpow_le hN (fun x => g (x + unit i) - g x) y
    ((t : ℤ) • unit j) hs
  have h2 := sum_abs_sub_rpow_le_shift (cornerCube y N).vertices B
    (fun x => g (x + unit i) - g x) j t hs hB
  exact h1.trans (div_le_div_of_nonneg_right h2 (by positivity))

/-- **Values of neighbouring cubes**: `ζ(y + N e_j) − ζ(y) − N p_j(y) =
  Σ_{t<N} (p_j(y + t e_j) − p_j(y))`, where `ζ = ⟨g⟩` and `p_j = ⟨∇_j g⟩` on cubes of side `N`. -/
theorem cubeAverage_add_sub_sub_eq_sum (N : ℕ) (g : Vertex d → ℝ) (y : Vertex d) (j : Fin d) :
    cubeAverage N g (y + (N : ℤ) • unit j) - cubeAverage N g y - N * cubeSlope N g y j =
      ∑ t ∈ Finset.range N, (cubeSlope N g (y + (t : ℤ) • unit j) j - cubeSlope N g y j) := by
  have htel := Finset.sum_range_sub (fun t : ℕ => cubeAverage N g (y + (t : ℤ) • unit j)) N
  simp only [Nat.cast_zero, zero_smul, add_zero] at htel
  have hstep : ∀ t : ℕ, cubeAverage N g (y + ((t + 1 : ℕ) : ℤ) • unit j) -
      cubeAverage N g (y + (t : ℤ) • unit j) = cubeSlope N g (y + (t : ℤ) • unit j) j := by
    intro t
    rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc, cubeAverage_add_unit_sub]
    rfl
  rw [← htel]
  simp only [hstep]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Rigidity.Dirichlet
