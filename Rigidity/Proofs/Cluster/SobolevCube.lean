import Rigidity.Proofs.Cluster.SobolevFold

/-!
# The lattice Sobolev–Poincaré inequality on integer cubes

For `d ≥ 2`, `s ≥ d/(d-1)` and `s_* = sd/(s+d)` there is a constant `S(d, s)` such that every
integer cube `B` satisfies
`∑_{x ∈ B} |f(x) - (f)_B|^s ≤ S (∑_{x ∈ B} |∇f|^{s_*}(x))^{s/s_*}`,
the usual Sobolev inequality on `ℤ^d` used by Armstrong and Dario in the proof of
Proposition 3.4 (case of mean zero). With `g = f - (f)_B`, the function `η · (g ∘ φ)`, with `φ`
the fold of the triple cube `B'` onto `B` and `η` the product cutoff, vanishes on the lattice
boundary of `B'`, so the Sobolev inequality with zero boundary values applies on `B'`. Its
increments along the edges at `x` are at most `2√2 |∇f|(φ x) + |g(φ x)|/n`, the fibres of `φ`
have `3^d` points, and the `L^{s_*}` Poincaré inequality on `B` bounds `n^{-s_*} ∑_B |g|^{s_*}` by
`∑_B |∇f|^{s_*}`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The magnitude of the gradient is unchanged by subtracting a constant. -/
theorem gradNormIn_sub_const (G : SimpleGraph (Vertex d)) (S : Finset (Vertex d))
    (f : Vertex d → ℝ) (c : ℝ) (x : Vertex d) :
    gradNormIn G S (fun y => f y - c) x = gradNormIn G S f x := by
  simp only [gradNormIn, sub_sub_sub_cancel_right]

/-- **The lattice Sobolev–Poincaré inequality on integer cubes.** For `d ≥ 2`, `s ≥ d/(d-1)` and
`t = sd/(s+d)`, there is `S ≥ 0` such that every integer cube of positive side satisfies
`LatticeSobolevOn B.vertices s t S`. -/
theorem IntegerCube.exists_latticeSobolevOn (hd : 2 ≤ d) {s t : ℝ}
    (hs : (d : ℝ) / (d - 1) ≤ s) (ht : t = s * d / (s + d)) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ B : IntegerCube d, 0 < B.size → LatticeSobolevOn B.vertices s t S := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hdm : (0 : ℝ) < d - 1 := by linarith
  have hsd : (d : ℝ) ≤ s * (d - 1) := by rwa [div_le_iff₀ hdm] at hs
  have hs0 : 0 < s := by nlinarith
  have hsd0 : 0 < s + d := by linarith
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hsd0]
    nlinarith
  have ht0 : 0 < t := by linarith
  obtain ⟨S₀, hS₀, hzero⟩ := exists_sum_rpow_le_of_eq_zero_on_boundary hd hs ht
  obtain ⟨CP, hCP⟩ : ∃ c : ℝ, c = (d : ℝ) ^ (t - 1) * (d * √2 ^ t) := ⟨_, rfl⟩
  have hCP0 : 0 ≤ CP := by rw [hCP]; positivity
  obtain ⟨K, hK⟩ : ∃ c : ℝ,
      c = (2 * d : ℝ) ^ t * 3 ^ d * (2 ^ (t - 1) * ((2 * √2) ^ t + CP)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨S₀ * K ^ (s / t), mul_nonneg hS₀ (Real.rpow_nonneg hK0 _), ?_⟩
  intro B hB f
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∑ y ∈ B.vertices, f y) / B.vertices.card := ⟨_, rfl⟩
  rw [← hm]
  obtain ⟨g, hg⟩ : ∃ g : Vertex d → ℝ, g = fun x => f x - m := ⟨_, rfl⟩
  obtain ⟨Gr, hGr⟩ : ∃ G : Vertex d → ℝ,
      G = gradNormIn (nearestNeighborGraph d) B.vertices f := ⟨_, rfl⟩
  have hGg : gradNormIn (nearestNeighborGraph d) B.vertices g = Gr := by
    funext x
    rw [hg, hGr, gradNormIn_sub_const]
  have hGr0 : ∀ x, 0 ≤ Gr x := fun x => by
    rw [hGr]
    exact gradNormIn_nonneg _ _ _ _
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ x ∈ B.vertices, Gr x ^ t := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hGr0 x) _
  have hgoalR : ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices f x ^ t = T := by
    rw [hT, hGr]
  rw [hgoalR]
  have hn : (0 : ℝ) < B.size := by exact_mod_cast hB
  have hn1 : (1 : ℝ) / B.size ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast hB
  -- the reflected function, cut off near the boundary of the triple cube
  obtain ⟨h, hh⟩ : ∃ h : Vertex d → ℝ, h = fun x => B.cutoff x * g (B.fold x) := ⟨_, rfl⟩
  have hbd : ∀ x ∈ B.triple.vertices, ∀ y, (nearestNeighborGraph d).Adj x y →
      y ∉ B.triple.vertices → h x = 0 := by
    intro x hx y hxy hy
    simp only [hh, B.cutoff_eq_zero hx hy hxy, zero_mul]
  have hS := hzero B.triple.vertices h hbd
  have hleft : ∑ x ∈ B.vertices, |f x - m| ^ s ≤ ∑ x ∈ B.triple.vertices, |h x| ^ s := by
    calc ∑ x ∈ B.vertices, |f x - m| ^ s = ∑ x ∈ B.vertices, |h x| ^ s :=
          Finset.sum_congr rfl fun x hx => by
            simp only [hh, hg, B.cutoff_of_mem hB hx, B.fold_of_mem hx, one_mul]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg B.vertices_subset_triple fun _ _ _ =>
          Real.rpow_nonneg (abs_nonneg _) _
  -- the increments along the edges of the triple cube
  have hedge : ∀ x ∈ B.triple.vertices, ∀ y ∈ B.triple.vertices,
      (nearestNeighborGraph d).Adj x y →
      |h x - h y| ≤ 2 * √2 * Gr (B.fold x) + |g (B.fold x)| / B.size := by
    intro x hx y hy hxy
    have hφy := B.fold_mem hy
    have hG0 := hGr0 (B.fold x)
    have hgg : |g (B.fold x) - g (B.fold y)| ≤ √2 * Gr (B.fold x) := by
      rcases B.fold_adj hx hy hxy with he | he
      · rw [he, sub_self, abs_zero]
        exact mul_nonneg (Real.sqrt_nonneg _) hG0
      · rw [← hGg]
        exact abs_sub_le_sqrt_two_mul_gradNormIn _ _ _ hφy he
    have hηx0 := B.cutoff_nonneg hx
    have hηx1 := B.cutoff_le_one hB hx
    have hη := B.abs_cutoff_sub_le hB hx hy hxy
    have hgy : |g (B.fold y)| ≤ |g (B.fold x)| + √2 * Gr (B.fold x) := by
      calc |g (B.fold y)| = |g (B.fold x) + -(g (B.fold x) - g (B.fold y))| := by
            congr 1
            ring
        _ ≤ |g (B.fold x)| + |-(g (B.fold x) - g (B.fold y))| := abs_add_le _ _
        _ = |g (B.fold x)| + |g (B.fold x) - g (B.fold y)| := by rw [abs_neg]
        _ ≤ _ := by linarith
    have e : h x - h y = B.cutoff x * (g (B.fold x) - g (B.fold y)) +
        (B.cutoff x - B.cutoff y) * g (B.fold y) := by
      simp only [hh]
      ring
    have hsmall : (1 / B.size : ℝ) * (√2 * Gr (B.fold x)) ≤ √2 * Gr (B.fold x) := by
      calc (1 / B.size : ℝ) * (√2 * Gr (B.fold x)) ≤ 1 * (√2 * Gr (B.fold x)) :=
            mul_le_mul_of_nonneg_right hn1 (mul_nonneg (Real.sqrt_nonneg _) hG0)
        _ = _ := one_mul _
    rw [e]
    calc |B.cutoff x * (g (B.fold x) - g (B.fold y)) + (B.cutoff x - B.cutoff y) * g (B.fold y)|
        ≤ |B.cutoff x * (g (B.fold x) - g (B.fold y))| +
            |(B.cutoff x - B.cutoff y) * g (B.fold y)| := abs_add_le _ _
      _ = B.cutoff x * |g (B.fold x) - g (B.fold y)| +
            |B.cutoff x - B.cutoff y| * |g (B.fold y)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hηx0]
      _ ≤ 1 * (√2 * Gr (B.fold x)) + (1 / B.size) * (|g (B.fold x)| + √2 * Gr (B.fold x)) :=
          add_le_add (mul_le_mul hηx1 hgg (abs_nonneg _) zero_le_one)
            (mul_le_mul hη hgy (abs_nonneg _) (by positivity))
      _ = √2 * Gr (B.fold x) + |g (B.fold x)| / B.size + (1 / B.size) * (√2 * Gr (B.fold x)) := by
          ring
      _ ≤ √2 * Gr (B.fold x) + |g (B.fold x)| / B.size + √2 * Gr (B.fold x) := by linarith
      _ = 2 * √2 * Gr (B.fold x) + |g (B.fold x)| / B.size := by ring
  -- the gradient of the cut-off reflection
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Vertex d → ℝ, Φ = fun w => 2 * √2 * Gr w + |g w| / B.size := ⟨_, rfl⟩
  have hΦ0 : ∀ w, 0 ≤ Φ w := fun w => by
    simp only [hΦ]
    exact add_nonneg (mul_nonneg (by positivity) (hGr0 w)) (div_nonneg (abs_nonneg _) hn.le)
  have hgrad : ∀ x ∈ B.triple.vertices,
      gradNormIn (nearestNeighborGraph d) B.triple.vertices h x ≤ 2 * d * Φ (B.fold x) := by
    intro x hx
    refine (gradNormIn_le _ _ _ _).trans ?_
    have h1 : ∀ y ∈ B.triple.vertices,
        (if (nearestNeighborGraph d).Adj x y then |h x - h y| else 0) ≤
          (if (nearestNeighborGraph d).Adj x y then Φ (B.fold x) else 0) := by
      intro y hy
      split_ifs with hxy
      · simp only [hΦ]
        exact hedge x hx y hy hxy
      · exact le_rfl
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hΦ0 _)
    have hsub : B.triple.vertices.filter ((nearestNeighborGraph d).Adj x) ⊆
        (nearestNeighborGraph d).neighborFinset x := fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
    have hc := (Finset.card_le_card hsub).trans
      ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans
        (LatticeProb.Graph.Zd.degree_eq x).le)
    exact_mod_cast hc
  -- the Poincaré inequality for `g`
  have hP := B.sum_abs_sub_mean_rpow_le hB f ht1
  rw [← hm, ← hCP, hgoalR] at hP
  have hgsum : ∑ w ∈ B.vertices, (|g w| / B.size) ^ t ≤ CP * T := by
    have e : ∑ w ∈ B.vertices, (|g w| / B.size) ^ t =
        (∑ w ∈ B.vertices, |f w - m| ^ t) / (B.size : ℝ) ^ t := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.div_rpow (abs_nonneg _) hn.le]
      simp only [hg]
    rw [e, div_le_iff₀ (Real.rpow_pos_of_pos hn _)]
    calc _ ≤ CP * (B.size : ℝ) ^ t * T := hP
      _ = CP * T * (B.size : ℝ) ^ t := by ring
  have hΦsum : ∑ w ∈ B.vertices, Φ w ^ t ≤ 2 ^ (t - 1) * ((2 * √2) ^ t + CP) * T := by
    have hpt : ∀ w, Φ w ^ t ≤
        2 ^ (t - 1) * ((2 * √2) ^ t * Gr w ^ t + (|g w| / B.size) ^ t) := by
      intro w
      have h1 := add_rpow_le_two_rpow_mul
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * √2) (hGr0 w))
        (div_nonneg (abs_nonneg (g w)) hn.le) ht1
      rw [Real.mul_rpow (x := 2 * √2) (by positivity) (hGr0 w)] at h1
      simpa only [hΦ] using h1
    calc ∑ w ∈ B.vertices, Φ w ^ t
        ≤ ∑ w ∈ B.vertices, 2 ^ (t - 1) * ((2 * √2) ^ t * Gr w ^ t + (|g w| / B.size) ^ t) :=
          Finset.sum_le_sum fun w _ => hpt w
      _ = 2 ^ (t - 1) * ((2 * √2) ^ t * T + ∑ w ∈ B.vertices, (|g w| / B.size) ^ t) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hT]
      _ ≤ 2 ^ (t - 1) * ((2 * √2) ^ t * T + CP * T) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hgsum) (by positivity)
      _ = 2 ^ (t - 1) * ((2 * √2) ^ t + CP) * T := by ring
  have hsumgrad : ∑ x ∈ B.triple.vertices,
      gradNormIn (nearestNeighborGraph d) B.triple.vertices h x ^ t ≤ K * T := by
    calc ∑ x ∈ B.triple.vertices, gradNormIn (nearestNeighborGraph d) B.triple.vertices h x ^ t
        ≤ ∑ x ∈ B.triple.vertices, (2 * d : ℝ) ^ t * Φ (B.fold x) ^ t :=
          Finset.sum_le_sum fun x hx => by
            rw [← Real.mul_rpow (x := (2 * d : ℝ)) (by positivity) (hΦ0 _)]
            exact Real.rpow_le_rpow (gradNormIn_nonneg _ _ _ _) (hgrad x hx) ht0.le
      _ = (2 * d : ℝ) ^ t * ∑ x ∈ B.triple.vertices, Φ (B.fold x) ^ t := by
          rw [Finset.mul_sum]
      _ ≤ (2 * d : ℝ) ^ t * (3 ^ d * ∑ w ∈ B.vertices, Φ w ^ t) :=
          mul_le_mul_of_nonneg_left (B.sum_fold_le (fun w => Φ w ^ t)
            fun w => Real.rpow_nonneg (hΦ0 w) _) (by positivity)
      _ ≤ (2 * d : ℝ) ^ t * (3 ^ d * (2 ^ (t - 1) * ((2 * √2) ^ t + CP) * T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦsum (by positivity))
            (by positivity)
      _ = K * T := by
          rw [hK]
          ring
  have hS2 : (∑ x ∈ B.triple.vertices,
      gradNormIn (nearestNeighborGraph d) B.triple.vertices h x ^ t) ^ (s / t) ≤
        (K * T) ^ (s / t) :=
    Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
      Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) hsumgrad (by positivity)
  rw [Real.mul_rpow hK0 hT0] at hS2
  calc ∑ x ∈ B.vertices, |f x - m| ^ s ≤ ∑ x ∈ B.triple.vertices, |h x| ^ s := hleft
    _ ≤ S₀ * (∑ x ∈ B.triple.vertices,
          gradNormIn (nearestNeighborGraph d) B.triple.vertices h x ^ t) ^ (s / t) := hS
    _ ≤ S₀ * (K ^ (s / t) * T ^ (s / t)) := mul_le_mul_of_nonneg_left hS2 hS₀
    _ = S₀ * K ^ (s / t) * T ^ (s / t) := by ring

end Rigidity.Percolation
