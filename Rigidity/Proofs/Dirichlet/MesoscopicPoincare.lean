import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# Poincaré inequality for mesoscopic averages

For `s ≥ 1`, a cube size `N ≥ 1` and the cube average `ξ(x) = N^{-d} Σ_{x + □_N} g`,
`Σ_{x∈A} |ξ(x) − g(x)|^s ≤ d^{s-1} N^s Σ_{y∈B} Σ_i |∇_i g(y)|^s`
whenever `B` contains every `x + o` with `x ∈ A` and `o ∈ {0, …, N − 1}^d`: telescope
`g(x + z) − g(x)` along the staircase that changes one coordinate at a time, bound each
one-dimensional difference by Hölder's inequality and average over `z`.

This is the discrete form of the Poincaré step in the proof of Armstrong–Dario, Lemma 6.2,
Step 5 (`⨍_{y + □_n} |ξ − w|^{p'} ≤ C 3^{p'n} ⨍ |∇w|^{p'}`), and of the estimate of the affine
approximations in the proof of Lemma 6.3.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Power-mean inequality**: `|Σ_T f|^s ≤ #T^{s-1} Σ_T |f|^s` for `s ≥ 1`. -/
theorem abs_sum_rpow_le {ι : Type*} (T : Finset ι) (f : ι → ℝ) {s : ℝ} (hs : 1 ≤ s) :
    |∑ x ∈ T, f x| ^ s ≤ (#T : ℝ) ^ (s - 1) * ∑ x ∈ T, |f x| ^ s :=
  (Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (by linarith)).trans
    (Real.rpow_sum_le_const_mul_sum_rpow T f hs)

/-- **One-dimensional telescoping**: `|g(y + n e_i) − g(y)|^s ≤
  n^{s-1} Σ_{t<n} |∇_i g(y + t e_i)|^s`. -/
theorem abs_sub_rpow_le_line (g : Vertex d → ℝ) (y : Vertex d) (i : Fin d) (n : ℕ) {s : ℝ}
    (hs : 1 ≤ s) :
    |g (y + (n : ℤ) • unit i) - g y| ^ s ≤ (n : ℝ) ^ (s - 1) *
      ∑ t ∈ Finset.range n, |g (y + (t : ℤ) • unit i + unit i) - g (y + (t : ℤ) • unit i)| ^ s := by
  have htel : g (y + (n : ℤ) • unit i) - g y = ∑ t ∈ Finset.range n,
      (g (y + (t : ℤ) • unit i + unit i) - g (y + (t : ℤ) • unit i)) := by
    have h := Finset.sum_range_sub (fun t : ℕ => g (y + (t : ℤ) • unit i)) n
    simp only [Nat.cast_zero, zero_smul, add_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc]
  rw [htel]
  simpa using abs_sum_rpow_le (Finset.range n)
    (fun t : ℕ => g (y + (t : ℤ) • unit i + unit i) - g (y + (t : ℤ) • unit i)) hs

/-- The vector keeping the first `k` coordinates of `z` and setting the others to `0`. -/
def coordPrefix (z : Vertex d) (k : ℕ) : Vertex d := fun j => if (j : ℕ) < k then z j else 0

theorem coordPrefix_zero (z : Vertex d) : coordPrefix z 0 = 0 := by
  funext j
  simp [coordPrefix]

theorem coordPrefix_dim (z : Vertex d) : coordPrefix z d = z := by
  funext j
  simp [coordPrefix, j.isLt]

theorem coordPrefix_succ (z : Vertex d) (i : Fin d) :
    coordPrefix z ((i : ℕ) + 1) = coordPrefix z i + z i • unit i := by
  funext j
  simp only [coordPrefix, Pi.add_apply, Pi.smul_apply, unit, Pi.single_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    by_cases hlt : (j : ℕ) < i
    · simp [hji, hlt, show (j : ℕ) < i + 1 by omega]
    · simp [hji, hlt, show ¬ (j : ℕ) < i + 1 by omega]

/-- **Staircase telescoping**: `g(x + z) − g(x)` is the sum over the coordinates `i` of the
differences between consecutive prefixes of `z`. -/
theorem sub_eq_sum_coordPrefix (g : Vertex d → ℝ) (x z : Vertex d) :
    g (x + z) - g x =
      ∑ i : Fin d, (g (x + coordPrefix z ((i : ℕ) + 1)) - g (x + coordPrefix z i)) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g (x + coordPrefix z (k + 1)) -
    g (x + coordPrefix z k)) d, Finset.sum_range_sub (fun k => g (x + coordPrefix z k)) d,
    coordPrefix_dim, coordPrefix_zero, add_zero]

/-- **Staircase bound**: for `z` with coordinates in `[0, N)`,
`|g(x + z) − g(x)|^s ≤ d^{s-1} N^{s-1} Σ_i Σ_{t < z_i} |∇_i g(x + P_i(z) + t e_i)|^s`. -/
theorem abs_sub_rpow_le_staircase (g : Vertex d → ℝ) (x z : Vertex d) {N : ℕ}
    (hz : ∀ i, 0 ≤ z i ∧ z i < N) {s : ℝ} (hs : 1 ≤ s) :
    |g (x + z) - g x| ^ s ≤ (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) *
      ∑ i : Fin d, ∑ t ∈ Finset.range (z i).toNat,
        |g (x + coordPrefix z i + (t : ℤ) • unit i + unit i) -
          g (x + coordPrefix z i + (t : ℤ) • unit i)| ^ s := by
  rw [sub_eq_sum_coordPrefix]
  refine (abs_sum_rpow_le Finset.univ _ hs).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hzi : z i = ((z i).toNat : ℤ) := (Int.toNat_of_nonneg (hz i).1).symm
  have hstep : x + coordPrefix z ((i : ℕ) + 1) =
      x + coordPrefix z i + (((z i).toNat : ℕ) : ℤ) • unit i := by
    rw [coordPrefix_succ, ← hzi, add_assoc]
  rw [hstep]
  refine (abs_sub_rpow_le_line g (x + coordPrefix z i) i (z i).toNat hs).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
  refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by linarith)
  have : (z i).toNat ≤ N := by have := (hz i).2; omega
  exact_mod_cast this

/-- The points `P_i(z) + t e_i` of the staircase of `z ∈ {0, …, N − 1}^d` stay in
`{0, …, N − 1}^d`. -/
theorem coordPrefix_add_smul_mem (z : Vertex d) {N : ℕ} (hz : ∀ i, 0 ≤ z i ∧ z i < N)
    (i : Fin d) {t : ℕ} (ht : t < (z i).toNat) :
    coordPrefix z i + (t : ℤ) • unit i ∈ (cornerCube 0 N).vertices := by
  rw [IntegerCube.mem_vertices]
  intro j
  simp only [cornerCube, Pi.zero_apply, zero_add, coordPrefix, Pi.add_apply, Pi.smul_apply,
    unit, Pi.single_apply, smul_eq_mul]
  have hzj := hz j
  have hzi := hz i
  by_cases hji : j = i
  · subst hji
    simp only [lt_irrefl, if_false, if_true, mul_one, zero_add]
    omega
  · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    simp only [hji, if_false, mul_zero, add_zero]
    split_ifs <;> omega

/-- **Poincaré inequality for mesoscopic averages**: for `s ≥ 1`, `N ≥ 1` and `B` containing every
`x + o` with `x ∈ A`, `o ∈ {0, …, N − 1}^d`,
`Σ_{x∈A} |ξ_N(x) − g(x)|^s ≤ d^{s-1} N^s Σ_{y∈B} Σ_i |∇_i g(y)|^s`. -/
theorem sum_abs_cubeAverage_sub_rpow_le (A B : Finset (Vertex d)) {N : ℕ} (hN : 0 < N)
    (g : Vertex d → ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hB : ∀ x ∈ A, ∀ o ∈ (cornerCube 0 N).vertices, x + o ∈ B) :
    ∑ x ∈ A, |cubeAverage N g x - g x| ^ s ≤
      (d : ℝ) ^ (s - 1) * (N : ℝ) ^ s * ∑ y ∈ B, ∑ i : Fin d, |g (y + unit i) - g y| ^ s := by
  classical
  set Z := (cornerCube (0 : Vertex d) N).vertices
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hZcard : (#Z : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have hZ : ∀ z ∈ Z, ∀ i, 0 ≤ z i ∧ z i < N := fun z hz i => by
    have := (IntegerCube.mem_vertices _ z).mp hz i
    simpa [cornerCube] using this
  set G : Vertex d → ℝ := fun y => ∑ i : Fin d, |g (y + unit i) - g y| ^ s
  -- the average as an average over the translates
  have havg : ∀ x, cubeAverage N g x - g x = (∑ z ∈ Z, (g (x + z) - g x)) / #Z := by
    intro x
    have h := sum_cornerCube_add (0 : Vertex d) x N g
    rw [zero_add] at h
    rw [cubeAverage, h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hZcard]
    field_simp
    congr 1
    exact Finset.sum_congr rfl fun z _ => congrArg g (add_comm z x)
  -- the pointwise Jensen step
  have hjensen : ∀ x, |cubeAverage N g x - g x| ^ s ≤
      (∑ z ∈ Z, |g (x + z) - g x| ^ s) / #Z := by
    intro x
    have hZpos : (0 : ℝ) < #Z := by rw [hZcard]; positivity
    rw [havg, abs_div, abs_of_pos hZpos, Real.div_rpow (abs_nonneg _) hZpos.le,
      div_le_div_iff₀ (by positivity) hZpos]
    have h := abs_sum_rpow_le Z (fun z => g (x + z) - g x) hs
    calc |∑ z ∈ Z, (g (x + z) - g x)| ^ s * #Z
        ≤ (#Z : ℝ) ^ (s - 1) * (∑ z ∈ Z, |g (x + z) - g x| ^ s) * #Z :=
          mul_le_mul_of_nonneg_right h hZpos.le
      _ = (∑ z ∈ Z, |g (x + z) - g x| ^ s) * (#Z : ℝ) ^ s := by
          rw [mul_comm ((#Z : ℝ) ^ (s - 1)), mul_assoc, ← Real.rpow_add_one hZpos.ne',
            sub_add_cancel]
  -- the translated sums
  have hshift : ∀ o : Vertex d, (∀ x ∈ A, x + o ∈ B) → ∀ i : Fin d,
      ∑ x ∈ A, |g (x + o + unit i) - g (x + o)| ^ s ≤
        ∑ y ∈ B, |g (y + unit i) - g y| ^ s := by
    intro o ho i
    calc ∑ x ∈ A, |g (x + o + unit i) - g (x + o)| ^ s
        = ∑ y ∈ A.map (addRightEmbedding o), |g (y + unit i) - g y| ^ s := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ y ∈ B, |g (y + unit i) - g y| ^ s := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => ?_)
            fun _ _ _ => by positivity
          obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
          exact ho x hx
  -- the bound for one translate `z`
  have hone : ∀ z ∈ Z, ∑ x ∈ A, |g (x + z) - g x| ^ s ≤
      (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) * ((N : ℝ) * ∑ y ∈ B, G y) := by
    intro z hz
    calc ∑ x ∈ A, |g (x + z) - g x| ^ s
        ≤ ∑ x ∈ A, (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) *
            ∑ i : Fin d, ∑ t ∈ Finset.range (z i).toNat,
              |g (x + coordPrefix z i + (t : ℤ) • unit i + unit i) -
                g (x + coordPrefix z i + (t : ℤ) • unit i)| ^ s :=
          Finset.sum_le_sum fun x _ => abs_sub_rpow_le_staircase g x z (hZ z hz) hs
      _ = (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) *
            ∑ i : Fin d, ∑ t ∈ Finset.range (z i).toNat, ∑ x ∈ A,
              |g (x + (coordPrefix z i + (t : ℤ) • unit i) + unit i) -
                g (x + (coordPrefix z i + (t : ℤ) • unit i))| ^ s := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          simp only [add_assoc]
      _ ≤ (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) *
            ∑ i : Fin d, ∑ _t ∈ Finset.range N, ∑ y ∈ B, |g (y + unit i) - g y| ^ s := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
          have hsub : Finset.range (z i).toNat ⊆ Finset.range N := by
            intro t ht
            have := (hZ z hz i).2
            simp only [Finset.mem_range] at ht ⊢
            omega
          refine (Finset.sum_le_sum fun t ht => hshift _ (fun x hx => hB x hx _
            (coordPrefix_add_smul_mem z (hZ z hz) i (Finset.mem_range.mp ht))) i).trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            Finset.sum_nonneg fun y _ => by positivity
      _ = (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) * ((N : ℝ) * ∑ y ∈ B, G y) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, G]
          rw [← Finset.mul_sum, Finset.sum_comm]
  -- assemble
  have hZpos : (0 : ℝ) < #Z := by rw [hZcard]; positivity
  calc ∑ x ∈ A, |cubeAverage N g x - g x| ^ s
      ≤ ∑ x ∈ A, (∑ z ∈ Z, |g (x + z) - g x| ^ s) / #Z := Finset.sum_le_sum fun x _ => hjensen x
    _ = (∑ z ∈ Z, ∑ x ∈ A, |g (x + z) - g x| ^ s) / #Z := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ ≤ (∑ _z ∈ Z, (d : ℝ) ^ (s - 1) * (N : ℝ) ^ (s - 1) * ((N : ℝ) * ∑ y ∈ B, G y)) /
          #Z := div_le_div_of_nonneg_right (Finset.sum_le_sum hone) hZpos.le
    _ = (d : ℝ) ^ (s - 1) * (N : ℝ) ^ s * ∑ y ∈ B, G y := by
        rw [Finset.sum_const, nsmul_eq_mul, Real.rpow_sub_one hN'.ne']
        field_simp

end Rigidity.Dirichlet
