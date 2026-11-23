import Rigidity.Proofs.Regularity.PlanarCoarseBound
import Rigidity.Proofs.Dirichlet.InteriorLinfty
import Rigidity.Proofs.Dirichlet.TiledEnergy
import Rigidity.Proofs.Dirichlet.LayerEnergy

/-!
# Interior gradient bound for the discrete homogenized solution on a planar square

For `v` harmonic for the lattice Laplacian off the outer slices of the lattice square
`□_{i+3}`, the differences of `v` are harmonic one slice further in, and the interior `L^∞`
estimate (`abs_le_of_condLaplacian_constCond_eq_zero`) on cubes of side `3^i` gives
`|∇v| ≤ 80 · 3^{-i} (Σ_{edges in □_{i+3}} |∇v|²)^{1/2}` on the square of half-side `10 · 3^i - 5`
(`abs_grad_le_of_cubeInterior`). Along a staircase path the increments of `v` between two points
`y, z` are then at most `|z - y|_1` times this bound (`abs_sub_le_of_grad_le`).

These are the bounds on `∇w` in Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1,
(e.wgradbound), for the discrete homogenized solution `w = u_hom`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation Rigidity.Dirichlet

theorem two_mul_toIntegerCube_corner_add (n : ℕ) (k : Fin 2) :
    2 * (⟨n, 0⟩ : TriadicCube 2).toIntegerCube.corner k + 3 ^ n = 1 := by
  have ho : (3 : ℤ) ^ n % 2 = 1 := Int.odd_iff.mp (Odd.pow ⟨1, by norm_num⟩)
  have hd := Int.emod_add_mul_ediv ((3 : ℤ) ^ n) 2
  change 2 * ((3 : ℤ) ^ n * (0 : Vertex 2) k - (3 : ℤ) ^ n / 2) + 3 ^ n = 1
  rw [Pi.zero_apply, mul_zero, zero_sub]
  omega

theorem cast_toIntegerCube_size_zero (n : ℕ) :
    (((⟨n, 0⟩ : TriadicCube 2).toIntegerCube.size : ℕ) : ℤ) = 3 ^ n := by
  change ((3 ^ n : ℕ) : ℤ) = _
  push_cast
  rfl

theorem unit_apply_two (l k : Fin 2) : (unit l : Vertex 2) k = if k = l then 1 else 0 := by
  simp only [unit, Pi.single_apply]

/-- **Interior gradient bound**: for `v` harmonic for the lattice Laplacian on the interior of
the lattice square `□_{i+3}`, `i ≥ 2`, and `x` with `2|x_k| + 10 ≤ 20 · 3^i`,
`|v(x + e_l) - v(x)| ≤ 80 · 3^{-i} (Σ_{edges in □_{i+3}} |∇v|²)^{1/2}`. -/
theorem abs_grad_le_of_cubeInterior {i : ℕ} (hi : 2 ≤ i) {v : Vertex 2 → ℝ}
    (hv : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) v x = 0)
    {x : Vertex 2} (hx : ∀ k, 2 * |x k| + 10 ≤ 20 * 3 ^ i) (l : Fin 2) :
    |v (x + unit l) - v x| ≤ 80 / 3 ^ i *
      √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
        v) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : IntegerCube 2, Q = (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube :=
    ⟨_, rfl⟩
  rw [← hQ] at hv ⊢
  have hc : ∀ k, 2 * Q.corner k + 3 ^ (i + 3) = 1 := fun k => by
    rw [hQ]; exact two_mul_toIntegerCube_corner_add _ k
  have hs : ((Q.size : ℕ) : ℤ) = 3 ^ (i + 3) := by rw [hQ]; exact cast_toIntegerCube_size_zero _
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 3 ^ i := ⟨_, rfl⟩
  have hTz : ((T : ℕ) : ℤ) = 3 ^ i := by rw [hT]; push_cast; rfl
  have h27 : (3 : ℤ) ^ (i + 3) = 27 * 3 ^ i := by ring
  have hT9 : (9 : ℤ) ≤ 3 ^ i := by
    have : (3 : ℤ) ^ 2 ≤ 3 ^ i := pow_le_pow_right₀ (by norm_num) hi
    linarith
  -- the difference is harmonic one slice further in
  have hh : ∀ y ∈ (shrinkCube (shrinkCube Q 1) 1).vertices,
      condLaplacian (constCond fun _ => (1 : ℝ)) (fun y => v (y + unit l) - v y) y = 0 := by
    intro y hy
    refine condLaplacian_constCond_grad_eq_zero (fun _ => (1 : ℝ)) hv l y ?_
    rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff] at hy
    have hmem : ∀ w : Vertex 2, (∀ k, Q.corner k + 1 ≤ w k ∧ w k + 2 ≤ Q.corner k + Q.size) →
        w ∈ cubeInterior Q := by
      intro w hw
      unfold cubeInterior
      rw [Finset.mem_filter, IntegerCube.mem_vertices]
      refine ⟨fun k => ?_, hw⟩
      have := hw k
      constructor <;> omega
    rw [Finset.mem_filter]
    constructor
    · refine hmem y fun k => ?_
      have := hy k
      constructor <;> omega
    · refine hmem _ fun k => ?_
      have := hy k
      rw [Pi.add_apply, unit_apply_two]
      split_ifs <;> constructor <;> omega
  -- the cube of side `3^i` at `x`
  have hxM : (cornerCube x T).vertices ⊆
      (shrinkCube (shrinkCube Q 1) (2 * (T + 2))).vertices := by
    intro y hy
    rw [IntegerCube.mem_vertices] at hy
    rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff]
    intro k
    have h1 := hy k
    change x k ≤ y k ∧ y k < x k + ((T : ℕ) : ℤ) at h1
    have h2 := hx k
    have h3 := hc k
    have h4 := le_abs_self (x k)
    have h5 := neg_abs_le (x k)
    rw [h27] at h3
    rw [← hTz] at h2 h3 hT9
    generalize |x k| = a at h2 h4 h5
    constructor <;> omega
  have hT0 : (0 : ℝ) < T := by rw [hT]; positivity
  have hb := abs_le_of_condLaplacian_constCond_eq_zero (d := 2) (by norm_num) (fun _ => (1 : ℝ))
    (lam := 1) (Λ := 1) one_pos (fun _ => ⟨le_rfl, le_rfl⟩) (shrinkCube Q 1) hh
    (r := T) (by rw [hT]; positivity) (M := T) (by rw [hT]; positivity) hxM
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ y ∈ (shrinkCube Q 1).vertices, (v (y + unit l) - v y) ^ 2 :=
    ⟨_, rfl⟩
  rw [← hE] at hb
  have hE0 : 0 ≤ E := by rw [hE]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      (1 / (T : ℝ)) ^ (2 - S.card) * (√((T : ℝ) ^ 2) *
        √((10 * ((2 : ℕ) : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ S.card * E)) ≤ 20 / T * √E := by
    intro S _
    have hcard : S.card ≤ 2 := by simpa using Finset.card_le_univ S
    rw [Real.sqrt_sq hT0.le, Real.sqrt_mul (by positivity)]
    have hsE := Real.sqrt_nonneg E
    obtain ⟨c, hcdef⟩ : ∃ c, S.card = c := ⟨_, rfl⟩
    rw [hcdef] at hcard ⊢
    have e20 : 10 * ((2 : ℕ) : ℝ) * 1 / (1 * (T : ℝ) ^ 2) = 20 / (T : ℝ) ^ 2 := by
      push_cast; ring
    rw [e20]
    interval_cases c
    · simp only [pow_zero, Real.sqrt_one, one_mul, Nat.sub_zero]
      rw [div_pow, one_pow, show (1 : ℝ) / T ^ 2 * (T * √E) = √E / T by field_simp]
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hT0.le
    · simp only [pow_one, Nat.reduceSub]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hT0.le]
      have h20 : √(20 : ℝ) ≤ 20 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      rw [show 1 / (T : ℝ) * (T * (√20 / T * √E)) = √20 / T * √E by field_simp]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h20 hT0.le) hsE
    · simp only [Nat.sub_self, pow_zero, one_mul]
      rw [Real.sqrt_sq (by positivity)]
      rw [show (T : ℝ) * (20 / T ^ 2 * √E) = 20 / T * √E by field_simp]
  have hsum := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin 2)).powerset
    (fun S => (1 / (T : ℝ)) ^ (2 - S.card) * (√((T : ℝ) ^ 2) *
      √((10 * ((2 : ℕ) : ℝ) * 1 / (1 * (T : ℝ) ^ 2)) ^ S.card * E))) (20 / (T : ℝ) * √E) hterm
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hEI : E ≤ innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q v := by
    rw [hE]
    unfold innerEdgeEnergy
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ x ∈ Q.vertices.filter
      (fun x => x + unit j ∈ Q.vertices), constCond (fun _ => (1 : ℝ)) (x, j) *
        (v (x + unit j) - v x) ^ 2) (fun j _ => Finset.sum_nonneg fun x _ =>
          mul_nonneg (by simp [constCond]) (sq_nonneg _)) (Finset.mem_univ l))
    refine le_of_le_of_eq (b := ∑ y ∈ Q.vertices.filter (fun x => x + unit l ∈ Q.vertices),
      (v (y + unit l) - v y) ^ 2)
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _) ?_
    · intro y hy
      rw [mem_shrinkCube_iff] at hy
      rw [Finset.mem_filter, IntegerCube.mem_vertices, IntegerCube.mem_vertices]
      refine ⟨fun k => ?_, fun k => ?_⟩
      · have := hy k; constructor <;> omega
      · have := hy k
        rw [Pi.add_apply, unit_apply_two]
        split_ifs <;> constructor <;> omega
    · refine Finset.sum_congr rfl fun y _ => ?_
      simp [constCond]
  have hcast : ((T : ℕ) : ℝ) = (3 : ℝ) ^ i := by rw [hT]; push_cast; rfl
  calc |v (x + unit l) - v x| ≤ _ := hb
    _ ≤ ((2 ^ 2 : ℕ) : ℝ) * (20 / T * √E) := hsum
    _ = 80 / T * √E := by push_cast; ring
    _ ≤ 80 / T * √(innerEdgeEnergy (constCond fun _ => (1 : ℝ)) Q v) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEI) (by positivity)
    _ = _ := by rw [hcast]

/-- Increments along a line: `|g(b) - g(a)| ≤ |b - a| G` when the unit increments of `g` between
`a` and `b` are at most `G`. -/
theorem abs_sub_le_of_abs_succ_sub_le (g : ℤ → ℝ) {G : ℝ} (a b : ℤ)
    (h : ∀ k, min a b ≤ k → k < max a b → |g (k + 1) - g k| ≤ G) :
    |g b - g a| ≤ ((|b - a| : ℤ) : ℝ) * G := by
  have key : ∀ a b : ℤ, a ≤ b → (∀ k, a ≤ k → k < b → |g (k + 1) - g k| ≤ G) →
      |g b - g a| ≤ ((b - a : ℤ) : ℝ) * G := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => intro _; simp
    | succ n hn ih =>
        intro hk
        have h1 := ih fun k hk1 hk2 => hk k hk1 (by omega)
        have h2 := hk n hn (by omega)
        calc |g (n + 1) - g a| ≤ |g (n + 1) - g n| + |g n - g a| := abs_sub_le _ _ _
          _ ≤ G + ((n - a : ℤ) : ℝ) * G := add_le_add h2 h1
          _ = ((n + 1 - a : ℤ) : ℝ) * G := by push_cast; ring
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (show (0 : ℤ) ≤ b - a by omega)]
    exact key a b hab fun k hk1 hk2 => h k (by rw [min_eq_left hab]; exact hk1)
      (by rw [max_eq_right hab]; exact hk2)
  · rw [abs_sub_comm, abs_sub_comm b a, abs_of_nonneg (show (0 : ℤ) ≤ a - b by omega)]
    exact key b a hab fun k hk1 hk2 => h k (by rw [min_eq_right hab]; exact hk1)
      (by rw [max_eq_left hab]; exact hk2)

theorem vec_eq_two (y : Vertex 2) : y = ![y 0, y 1] := by
  funext k; fin_cases k <;> rfl

theorem vec_add_unit_zero (a b : ℤ) : (![a, b] : Vertex 2) + unit 0 = ![a + 1, b] := by
  funext k; fin_cases k <;> simp [unit_apply_two]

theorem vec_add_unit_one (a b : ℤ) : (![a, b] : Vertex 2) + unit 1 = ![a, b + 1] := by
  funext k; fin_cases k <;> simp [unit_apply_two]

/-- **Increments along a staircase**: if the unit increments of `v` on the box spanned by `y` and
`z` are at most `G`, then `|v(z) - v(y)| ≤ |z - y|_1 G`. -/
theorem abs_sub_le_of_grad_le (v : Vertex 2 → ℝ) {G : ℝ} (y z : Vertex 2)
    (h : ∀ p : Vertex 2, (∀ k, min (y k) (z k) ≤ p k ∧ p k ≤ max (y k) (z k)) →
      ∀ l, |v (p + unit l) - v p| ≤ G) :
    |v z - v y| ≤ (((|z 0 - y 0| + |z 1 - y 1|) : ℤ) : ℝ) * G := by
  have h0 := abs_sub_le_of_abs_succ_sub_le (fun k => v ![k, y 1]) (y 0) (z 0) fun k hk1 hk2 => by
    have := h ![k, y 1] (fun i => by
      fin_cases i
      · exact ⟨hk1, by simp; omega⟩
      · exact ⟨min_le_left _ _, le_max_left _ _⟩) 0
    rwa [vec_add_unit_zero] at this
  have h1 := abs_sub_le_of_abs_succ_sub_le (fun k => v ![z 0, k]) (y 1) (z 1) fun k hk1 hk2 => by
    have := h ![z 0, k] (fun i => by
      fin_cases i
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ⟨hk1, by simp; omega⟩) 1
    rwa [vec_add_unit_one] at this
  have h0' : |v ![z 0, y 1] - v ![y 0, y 1]| ≤ ((|z 0 - y 0| : ℤ) : ℝ) * G := h0
  have h1' : |v ![z 0, z 1] - v ![z 0, y 1]| ≤ ((|z 1 - y 1| : ℤ) : ℝ) * G := h1
  rw [← vec_eq_two y] at h0'
  rw [← vec_eq_two z] at h1'
  calc |v z - v y| ≤ |v z - v ![z 0, y 1]| + |v ![z 0, y 1] - v y| := abs_sub_le _ _ _
    _ ≤ ((|z 1 - y 1| : ℤ) : ℝ) * G + ((|z 0 - y 0| : ℤ) : ℝ) * G := add_le_add h1' h0'
    _ = _ := by push_cast; ring

end Rigidity.Proofs.Regularity
