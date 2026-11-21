import Rigidity.Proofs.Dirichlet.CubeStokes
import Rigidity.Proofs.Dirichlet.SecondDifferences

/-!
# Cutoff functions of lattice cubes

For an integer cube `Q` of side `N` and `r ≥ 1`, the cutoff `η_Q` is the product over the
coordinates of the ramps `ρ(t) = clamp_{[0,1]}(min(t, N − 1 − t)/r)`, `t = x_k − z_k`. It takes
values in `[0, 1]`, vanishes unless `x` and all its lattice neighbours lie in `Q`, equals `1` at
depth at least `r` and has discrete gradient at most `1/r`. This is the discrete form of the
cutoff `η` of Armstrong–Dario (6.12) (`η = 1` on `□°_int`, `η = 0` off `□°`, `|∇η| ≤ C 3^{-l}`).

With it, the interior second-difference bound becomes: for constant-coefficient harmonic `v` on
a set containing `Q`, `Σ η_Q(x + e_j)² a_j (∇_j∇_i v)² ≤ 5 r^{-2} Σ a_j ((∇_i v(x + e_j))² +
(∇_i v(x))²)` (`sum_cubeCutoff_second_difference_le`), the discrete interior `H²` estimate of
Armstrong–Dario (6.30) on a cube.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The ramp `ρ(t) = max(0, min(1, min(t, N − 1 − t)/r))` on `ℤ`. -/
noncomputable def ramp (N r : ℕ) (t : ℤ) : ℝ :=
  max 0 (min 1 (min (t : ℝ) ((N : ℝ) - 1 - t) / r))

theorem ramp_nonneg (N r : ℕ) (t : ℤ) : 0 ≤ ramp N r t := le_max_left _ _

theorem ramp_le_one (N r : ℕ) (t : ℤ) : ramp N r t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The ramp vanishes at and beyond the two ends of `{0, …, N − 1}`. -/
theorem ramp_eq_zero (N r : ℕ) {t : ℤ} (ht : t ≤ 0 ∨ (N : ℤ) - 1 ≤ t) : ramp N r t = 0 := by
  have hmin : min (t : ℝ) ((N : ℝ) - 1 - t) ≤ 0 := by
    rcases ht with ht | ht
    · exact (min_le_left _ _).trans (by exact_mod_cast ht)
    · refine (min_le_right _ _).trans ?_
      have : ((N : ℤ) : ℝ) - 1 ≤ (t : ℝ) := by exact_mod_cast ht
      push_cast at this
      linarith
  have hdiv : min (t : ℝ) ((N : ℝ) - 1 - t) / r ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hmin (Nat.cast_nonneg r)
  exact max_eq_left ((min_le_right _ _).trans hdiv)

/-- The ramp equals `1` at distance at least `r ≥ 1` from both ends. -/
theorem ramp_eq_one (N : ℕ) {r : ℕ} (hr : 0 < r) {t : ℤ} (h1 : (r : ℤ) ≤ t)
    (h2 : t + r ≤ (N : ℤ) - 1) : ramp N r t = 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h1' : (r : ℝ) ≤ t := by exact_mod_cast h1
  have h2' : (t : ℝ) + r ≤ (N : ℝ) - 1 := by exact_mod_cast h2
  have hge : 1 ≤ min (t : ℝ) ((N : ℝ) - 1 - t) / r := by
    rw [le_div_iff₀ hr', one_mul]
    exact le_min h1' (by linarith)
  rw [ramp, min_eq_left hge, max_eq_right zero_le_one]

/-- **The ramp is `1/r`-Lipschitz.** -/
theorem abs_ramp_add_one_sub_le (N r : ℕ) (t : ℤ) :
    |ramp N r (t + 1) - ramp N r t| ≤ 1 / r := by
  have hm : |min ((t + 1 : ℤ) : ℝ) ((N : ℝ) - 1 - ((t + 1 : ℤ) : ℝ)) -
      min (t : ℝ) ((N : ℝ) - 1 - t)| ≤ 1 := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_) <;> push_cast <;>
      ring_nf <;> simp
  have hdiv : |min ((t + 1 : ℤ) : ℝ) ((N : ℝ) - 1 - ((t + 1 : ℤ) : ℝ)) / r -
      min (t : ℝ) ((N : ℝ) - 1 - t) / r| ≤ 1 / r := by
    rw [← sub_div, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right hm (Nat.cast_nonneg r)
  unfold ramp
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (by positivity) hdiv

/-- The cutoff `η_Q(x) = Π_k ρ(x_k − z_k)` of the cube `Q` with corner `z`. -/
noncomputable def cubeCutoff (Q : IntegerCube d) (r : ℕ) (x : Vertex d) : ℝ :=
  ∏ k, ramp Q.size r (x k - Q.corner k)

theorem cubeCutoff_nonneg (Q : IntegerCube d) (r : ℕ) (x : Vertex d) : 0 ≤ cubeCutoff Q r x :=
  Finset.prod_nonneg fun _ _ => ramp_nonneg _ _ _

theorem cubeCutoff_le_one (Q : IntegerCube d) (r : ℕ) (x : Vertex d) : cubeCutoff Q r x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => ramp_nonneg _ _ _) fun _ _ => ramp_le_one _ _ _

/-- Where the cutoff is nonzero, every coordinate lies strictly between the two extreme slices. -/
theorem coord_of_cubeCutoff_ne_zero (Q : IntegerCube d) (r : ℕ) {x : Vertex d}
    (hx : cubeCutoff Q r x ≠ 0) (k : Fin d) :
    Q.corner k + 1 ≤ x k ∧ x k + 2 ≤ Q.corner k + Q.size := by
  by_contra h
  refine hx (Finset.prod_eq_zero (Finset.mem_univ k) (ramp_eq_zero _ _ ?_))
  omega

/-- The cutoff vanishes unless `x` and all its lattice neighbours lie in `Q`. -/
theorem mem_vertices_of_cubeCutoff_ne_zero (Q : IntegerCube d) (r : ℕ) {x : Vertex d}
    (hx : cubeCutoff Q r x ≠ 0) :
    x ∈ Q.vertices ∧ ∀ i : Fin d, x + unit i ∈ Q.vertices ∧ x - unit i ∈ Q.vertices := by
  have hc := coord_of_cubeCutoff_ne_zero Q r hx
  refine ⟨(IntegerCube.mem_vertices Q x).mpr fun k => ⟨by linarith [(hc k).1],
    by linarith [(hc k).2]⟩, fun i => ⟨?_, ?_⟩⟩
  · refine (IntegerCube.mem_vertices Q _).mpr fun k => ?_
    rw [add_unit_apply]
    split_ifs <;> constructor <;> linarith [(hc k).1, (hc k).2]
  · refine (IntegerCube.mem_vertices Q _).mpr fun k => ?_
    have : (x - unit i) k = x k - if k = i then 1 else 0 := by
      simp [unit, Pi.single_apply]
    rw [this]
    split_ifs <;> constructor <;> linarith [(hc k).1, (hc k).2]

/-- The cutoff equals `1` at depth at least `r ≥ 1` in every coordinate. -/
theorem cubeCutoff_eq_one (Q : IntegerCube d) {r : ℕ} (hr : 0 < r) {x : Vertex d}
    (hx : ∀ k, Q.corner k + r ≤ x k ∧ x k + r + 1 ≤ Q.corner k + Q.size) :
    cubeCutoff Q r x = 1 :=
  Finset.prod_eq_one fun k _ => ramp_eq_one _ hr (by linarith [(hx k).1]) (by linarith [(hx k).2])

/-- **The cutoff has discrete gradient at most `1/r`.** -/
theorem abs_cubeCutoff_add_unit_sub_le (Q : IntegerCube d) (r : ℕ) (x : Vertex d) (j : Fin d) :
    |cubeCutoff Q r (x + unit j) - cubeCutoff Q r x| ≤ 1 / r := by
  classical
  have hrest : ∏ k ∈ Finset.univ \ {j}, ramp Q.size r ((x + unit j) k - Q.corner k) =
      ∏ k ∈ Finset.univ \ {j}, ramp Q.size r (x k - Q.corner k) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkj : k ≠ j := by simpa using hk
    rw [add_unit_apply, if_neg hkj, add_zero]
  have hP0 : 0 ≤ ∏ k ∈ Finset.univ \ {j}, ramp Q.size r (x k - Q.corner k) :=
    Finset.prod_nonneg fun _ _ => ramp_nonneg _ _ _
  have hP1 : ∏ k ∈ Finset.univ \ {j}, ramp Q.size r (x k - Q.corner k) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => ramp_nonneg _ _ _) fun _ _ => ramp_le_one _ _ _
  unfold cubeCutoff
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)
      (fun k => ramp _ _ (x k - _)),
    hrest, ← sub_mul, abs_mul, abs_of_nonneg hP0, add_unit_apply, if_pos rfl,
    show x j + 1 - Q.corner j = x j - Q.corner j + 1 by ring]
  calc |ramp Q.size r (x j - Q.corner j + 1) - ramp Q.size r (x j - Q.corner j)| *
        ∏ k ∈ Finset.univ \ {j}, ramp Q.size r (x k - Q.corner k)
      ≤ 1 / r * 1 :=
        mul_le_mul (abs_ramp_add_one_sub_le _ _ _) hP1 hP0 (by positivity)
    _ = 1 / r := mul_one _

/-- **Interior second differences on a cube**: for constant nonnegative conductances `a`, `v`
harmonic on a set containing `Q`, `r ≥ 1` and `S` covering the edges at `Q`,
`Σ_{x∈S} Σ_j η_Q(x + e_j)² a_j (∇_j∇_i v(x))² ≤
  5 r^{-2} Σ_{x∈S} Σ_j a_j ((∇_i v(x + e_j))² + (∇_i v(x))²)`. -/
theorem sum_cubeCutoff_second_difference_le (a : Fin d → ℝ) (ha : ∀ j, 0 ≤ a j)
    {U S : Finset (Site d)} (Q : IntegerCube d) (hQU : Q.vertices ⊆ U) {v : Site d → ℝ}
    (hv : ∀ x ∈ U, condLaplacian (constCond a) v x = 0) (i : Fin d) {r : ℕ}
    (hS : CoversEdges Q.vertices S) :
    ∑ x ∈ S, ∑ j : Fin d, cubeCutoff Q r (x + unit j) ^ 2 * a j *
        ((v (x + unit j + unit i) - v (x + unit j)) - (v (x + unit i) - v x)) ^ 2 ≤
      5 * (1 / r) ^ 2 * ∑ x ∈ S, ∑ j : Fin d, a j *
        ((v (x + unit j + unit i) - v (x + unit j)) ^ 2 + (v (x + unit i) - v x) ^ 2) := by
  have hS' : CoversEdges (Q.vertices.filter fun x => x + unit i ∈ Q.vertices) S :=
    fun x j hx => hS x j (hx.imp (fun h => (Finset.mem_filter.mp h).1)
      fun h => (Finset.mem_filter.mp h).1)
  refine sum_cutoff_second_difference_le a ha (U := Q.vertices)
    (fun x hx => hv x (hQU hx)) i hS' (cubeCutoff Q r) (fun x hx => ?_)
    fun x _ j => abs_cubeCutoff_add_unit_sub_le Q r x j
  by_contra hne
  obtain ⟨hxQ, hnb⟩ := mem_vertices_of_cubeCutoff_ne_zero Q r hne
  exact hx (Finset.mem_filter.mpr ⟨hxQ, (hnb i).1⟩)

end Rigidity.Dirichlet
