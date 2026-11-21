import Rigidity.Proofs.Cluster.Gehring
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The Meyers estimate on clusters, deterministic part

Armstrong–Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(Comm. Pure Appl. Math. 2018), Proposition 3.8 (the bound on `ME_ε(□_m)`): there
are `ε > 0` and `t < ∞` such that, above the minimal scale of the partition `𝓡` on whose cubes the
reverse Hölder inequality of Lemma 3.6 holds,

`|□_m|⁻¹ ∫_{𝒞_*(□_m)} |∇u 1_{𝐚≠0}|^{2+ε} ≤ C (|□_{m+1}|⁻¹ ∫_{𝒞_*(□_{m+1})} |∇u 1_{𝐚≠0}|²)^{(2+ε)/2}`.

`meyers_triadic` is this statement for a function `G ≥ 0` (in the application
`G = |∇u 1_{𝐚≠0}|²` on `𝒞_*(□_{m+1})`, extended by zero) and a partition of `ℤ^d` into triadic cells
`cube (s x) x`, under the hypotheses

* neighbouring cells have comparable sizes (Proposition 2.1 (ii)): `supDist x y ≤ 1 → s y ≤ s x + 1`;
* the reverse Hölder inequality with exponent `θ = d/(d+1)` (`2d/(d+1)` for `|∇u|`) on every triadic
  cube `□'` containing a cell with `3□' ⊆ □_{m+1}` (Lemma 3.6 for the good cubes of `𝓡`);
* `□_{m+1}` is a union of cells, and the moment bound `∑_{x ∈ □_m} size(cell(x))^t ≤ K |□_m|`
  (the minimal scale condition `3^m ≥ 𝓜_t(𝓡)`).

The proof follows Armstrong and Dario: the reverse Hölder inequality passes to the cell averages
`f = avg_{cell} G^θ`, now on all triadic cubes with enlargement `9□'` (Step 1, cells meeting `3□'`
have scale at most one more than `□'` and lie in `9□'`), Gehring's lemma `gehring_triadic` applies to
`f^{1/θ}` (Step 2), and Hölder's inequality with the moment bound removes the cell sizes (Step 3).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- **Jensen's inequality for averages.** -/
theorem avg_rpow_le_avg_rpow {V : Type*} {S : Finset V} (hS : S.Nonempty) {h : V → ℝ}
    (hh : ∀ x ∈ S, 0 ≤ h x) {p : ℝ} (hp : 1 ≤ p) :
    avg S h ^ p ≤ avg S (fun x => h x ^ p) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hw : ∑ _x ∈ S, (1 / (S.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h1 := Real.rpow_arith_mean_le_arith_mean_rpow S (fun _ => 1 / (S.card : ℝ)) h
    (fun _ _ => by positivity) hw hh hp
  have e1 : avg S h = ∑ x ∈ S, 1 / (S.card : ℝ) * h x := by
    rw [avg, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : avg S (fun x => h x ^ p) = ∑ x ∈ S, 1 / (S.card : ℝ) * h x ^ p := by
    rw [avg, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2]
  exact h1

/-- Points of the enlargement `3□` of a cube `□` of scale `k` and of the cube of scale `k` containing
such a point are joined by points at sup-distance at most one. -/
theorem exists_close_points_of_mem_enl_one {k : ℕ} {y p : Vertex d} (hp : p ∈ enl 1 k y) :
    ∃ y' ∈ cube k y, ∃ p' ∈ cube k p, supDist y' p' ≤ 1 := by
  have hs : (0 : ℤ) < 3 ^ k := by positivity
  have h2 := two_mul_halfSide_add_one k
  have hpc : p ∈ cube k p := mem_cube_self k p
  rw [enl, mem_box] at hp
  rw [cube, mem_box] at hpc
  -- the index differences are `-1`, `0` or `1`
  have hδ : ∀ i, idx k p i - idx k y i = -1 ∨ idx k p i - idx k y i = 0 ∨
      idx k p i - idx k y i = 1 := by
    intro i
    have h3 : |center k p i - center k y i| ≤ halfSide (k + 1) + halfSide k := by
      have := abs_sub_le (center k p i) (p i) (center k y i)
      rw [abs_sub_comm (center k p i) (p i)] at this
      linarith [hpc i, hp i]
    have h4 : center k p i - center k y i = 3 ^ k * (idx k p i - idx k y i) := by
      unfold center
      ring
    have h5 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
    rw [h4, abs_mul, abs_of_pos hs, h5] at h3
    have h6 : 3 ^ k * |idx k p i - idx k y i| < 3 ^ k * 2 := by linarith
    have h7 := lt_of_mul_lt_mul_left h6 hs.le
    rw [abs_lt] at h7
    omega
  have hcen : ∀ i, center k p i = center k y i + 3 ^ k * (idx k p i - idx k y i) := by
    intro i
    unfold center
    ring
  set y' : Vertex d := fun i =>
    if idx k p i - idx k y i = 1 then center k y i + halfSide k
    else if idx k p i - idx k y i = -1 then center k y i - halfSide k else p i with hy'
  set p' : Vertex d := fun i =>
    if idx k p i - idx k y i = 1 then center k p i - halfSide k
    else if idx k p i - idx k y i = -1 then center k p i + halfSide k else p i with hp'
  have hcoord : ∀ i, |y' i - center k y i| ≤ halfSide k ∧ |p' i - center k p i| ≤ halfSide k ∧
      |y' i - p' i| ≤ 1 := by
    intro i
    have hpi := hpc i
    have hci := hcen i
    have hhk := halfSide_nonneg k
    rw [abs_le] at hpi
    simp only [hy', hp']
    split_ifs with h1 h2
    · rw [h1, mul_one] at hci
      refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
    · rw [h2] at hci
      refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
    · have h0 : idx k p i - idx k y i = 0 := by
        rcases hδ i with h | h | h
        · exact absurd h h2
        · exact h
        · exact absurd h h1
      rw [h0, mul_zero, add_zero] at hci
      refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
  refine ⟨y', ?_, p', ?_, ?_⟩
  · rw [cube, mem_box]
    exact fun i => (hcoord i).1
  · rw [cube, mem_box]
    exact fun i => (hcoord i).2.1
  · refine Finset.sup_le fun i _ => ?_
    have h := (hcoord i).2.2
    rw [abs_le] at h
    show (y' i - p' i).natAbs ≤ 1
    omega

/-- **Cells meeting the triple of a union of cells.** If every point has its cell `cube (s x) x`,
neighbouring cells have comparable scales and the cube `□ = cube k y` contains its cells
(`s y ≤ k`), then every cell meeting `3□` has scale at most `k + 1` and lies in `9□`. -/
theorem cell_subset_enl_two {s : Vertex d → ℕ} (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (hnb : ∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) {k : ℕ} {y z : Vertex d} (hy : s y ≤ k)
    (hz : (cube (s z) z ∩ enl 1 k y).Nonempty) : cube (s z) z ⊆ enl 2 k y := by
  obtain ⟨p, hp⟩ := hz
  rw [Finset.mem_inter] at hp
  have hsp : s p = s z := hcell z p hp.1
  -- the cells of the points of `□` have scale at most `k`
  have hsmall : ∀ w ∈ cube k y, s w ≤ k := by
    intro w hw
    by_contra hlt'
    have hlt : k < s w := not_le.mp hlt'
    have h1 : y ∈ cube (s w) w := cube_mono hlt.le w (mem_cube_comm.mp hw)
    have := hcell w y h1
    omega
  have hscale : s z ≤ k + 1 := by
    by_contra hlt'
    have hlt : k + 1 < s z := not_le.mp hlt'
    obtain ⟨y', hy', p', hp', hdist⟩ := exists_close_points_of_mem_enl_one hp.2
    have h1 : p' ∈ cube (s p) p := cube_mono (by omega) p hp'
    have h2 : s p' = s p := hcell p p' h1
    have h3 := hnb y' p' hdist
    have h4 := hsmall y' hy'
    omega
  have hcz : cube (s z) z ⊆ cube (k + 1) z := cube_mono hscale z
  have hpz : p ∈ cube (k + 1) z := hcz hp.1
  intro w hw
  have hw' := hcz hw
  rw [cube, mem_box] at hw' hpz
  have hp2 := hp.2
  rw [enl, mem_box] at hp2 ⊢
  intro i
  have e1 : halfSide (k + 2) = 3 * halfSide (k + 1) + 1 := rfl
  have e2 := abs_sub_le (w i) (center (k + 1) z i) (p i)
  have e3 := abs_sub_le (w i) (p i) (center k y i)
  rw [abs_sub_comm (center (k + 1) z i) (p i)] at e2
  rw [e1]
  linarith [hw' i, hpz i, hp2 i]

/-- The cell average `f x = avg_{cube (s x) x} G^θ`. -/
noncomputable def cellAvg (s : Vertex d → ℕ) (G : Vertex d → ℝ) (θ : ℝ) (x : Vertex d) : ℝ :=
  avg (cube (s x) x) (fun z => G z ^ θ)

theorem cellAvg_nonneg (s : Vertex d → ℕ) {G : Vertex d → ℝ} (hG : ∀ x, 0 ≤ G x) (θ : ℝ)
    (x : Vertex d) : 0 ≤ cellAvg s G θ x :=
  div_nonneg (Finset.sum_nonneg fun z _ => Real.rpow_nonneg (hG z) _) (Nat.cast_nonneg _)

theorem cellAvg_eq_of_mem {s : Vertex d → ℕ} (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (G : Vertex d → ℝ) (θ : ℝ) {x z : Vertex d} (hz : z ∈ cube (s x) x) :
    cellAvg s G θ z = cellAvg s G θ x := by
  unfold cellAvg
  rw [hcell x z hz, cube_eq_of_mem hz]

/-- On a union of cells, the sum of `(avg_{cell} G^θ)^{1/θ}` is at most the sum of `G`. -/
theorem sum_cellAvg_rpow_le {s : Vertex d → ℕ} (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    {G : Vertex d → ℝ} (hG : ∀ x, 0 ≤ G x) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {T : Finset (Vertex d)} (hT : ∀ z ∈ T, cube (s z) z ⊆ T) :
    ∑ z ∈ T, cellAvg s G θ z ^ (1 / θ) ≤ ∑ z ∈ T, G z := by
  have hp : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ, one_mul]; exact hθ1
  have h1 : ∀ z ∈ T, cellAvg s G θ z ^ (1 / θ) ≤
      (∑ w ∈ cube (s z) z, G w) / (cube (s z) z).card := by
    intro z _
    have := avg_rpow_le_avg_rpow (S := cube (s z) z) ⟨z, mem_cube_self _ z⟩
      (h := fun w => G w ^ θ) (fun w _ => Real.rpow_nonneg (hG w) _) hp
    refine this.trans (le_of_eq ?_)
    simp only [avg]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Real.rpow_mul (hG w), mul_one_div_cancel hθ.ne', Real.rpow_one]
  rw [sum_eq_sum_avg (fun z => cube (s z) z) (fun z _ => mem_cube_self _ z) hT
    (fun z _ z' hz' => by rw [hcell z z' hz', cube_eq_of_mem hz']) G]
  exact Finset.sum_le_sum h1

/-- **Step 1: the reverse Hölder inequality for the cell averages.** Under the reverse Hölder
inequality on the cubes containing a cell with triple in `Ω`, the function `g = f^{1/θ}`,
`f = avg_{cell} G^θ`, satisfies the reverse Hölder inequality with enlargement `9□` on every triadic
cube `□` with `9□ ⊆ Ω`, with constant `A₀ (3^{2d})^{1/θ}`. -/
theorem reverse_holder_cellAvg {s : Vertex d → ℕ} (hcell : ∀ x, ∀ z ∈ cube (s x) x, s z = s x)
    (hnb : ∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) {G : Vertex d → ℝ} (hG : ∀ x, 0 ≤ G x)
    {θ A₀ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hA₀ : 1 ≤ A₀) {Ω : Finset (Vertex d)}
    (hRH : ∀ k y, s y ≤ k → enl 1 k y ⊆ Ω →
      avg (cube k y) G ≤ A₀ * avg (enl 1 k y) (fun x => G x ^ θ) ^ (1 / θ))
    (k : ℕ) (y : Vertex d) (hΩ : enl 2 k y ⊆ Ω) :
    avg (cube k y) (fun x => cellAvg s G θ x ^ (1 / θ)) ≤
      A₀ * ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) *
        avg (enl 2 k y) (fun x => (cellAvg s G θ x ^ (1 / θ)) ^ θ) ^ (1 / θ) := by
  set f := cellAvg s G θ with hf
  have hf0 : ∀ x, 0 ≤ f x := cellAvg_nonneg s hG θ
  have h1θ : 0 ≤ 1 / θ := by positivity
  have hgθ : avg (enl 2 k y) (fun x => (f x ^ (1 / θ)) ^ θ) = avg (enl 2 k y) f := by
    simp only [avg]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Real.rpow_mul (hf0 x), one_div_mul_cancel hθ.ne', Real.rpow_one]
  rw [hgθ]
  have hcube := card_cube_pos k y
  have henl : ((enl 2 k y).card : ℝ) = (3 : ℝ) ^ (2 * d) * (cube k y).card := by
    rw [card_enl_eq, ← pow_mul]
  have havg0 : 0 ≤ avg (enl 2 k y) f :=
    div_nonneg (Finset.sum_nonneg fun x _ => hf0 x) (Nat.cast_nonneg _)
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
  rcases Nat.lt_or_ge k (s y) with hlt | hge
  · -- the cube lies in a cell, on which `f` is constant
    have hconst : ∀ z ∈ cube k y, f z = f y := fun z hz =>
      cellAvg_eq_of_mem hcell G θ (cube_mono hlt.le y hz)
    have hL : avg (cube k y) (fun x => f x ^ (1 / θ)) = f y ^ (1 / θ) := by
      simp only [avg]
      have h1 : ∑ z ∈ cube k y, f z ^ (1 / θ) = ∑ _z ∈ cube k y, f y ^ (1 / θ) :=
        Finset.sum_congr rfl fun z hz => by rw [hconst z hz]
      rw [h1, Finset.sum_const, nsmul_eq_mul]
      have := hcube.ne'
      field_simp
    have hfy : f y ≤ (3 : ℝ) ^ (2 * d) * avg (enl 2 k y) f := by
      have hsub : ∑ z ∈ cube k y, f z ≤ ∑ z ∈ enl 2 k y, f z :=
        Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_enl 2 k y) fun z _ _ => hf0 z
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsub
      simp only [avg]
      rw [henl]
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    rw [hL]
    calc f y ^ (1 / θ) ≤ ((3 : ℝ) ^ (2 * d) * avg (enl 2 k y) f) ^ (1 / θ) :=
          Real.rpow_le_rpow (hf0 y) hfy h1θ
      _ = ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) * avg (enl 2 k y) f ^ (1 / θ) :=
          Real.mul_rpow (by positivity) havg0
      _ ≤ A₀ * ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) * avg (enl 2 k y) f ^ (1 / θ) := by
          have : 0 ≤ ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) * avg (enl 2 k y) f ^ (1 / θ) :=
            mul_nonneg (by positivity) (Real.rpow_nonneg havg0 _)
          nlinarith
  · -- the cube is a union of cells
    have hsmall : ∀ w ∈ cube k y, s w ≤ k := by
      intro w hw
      by_contra hlt'
      have hlt : k < s w := not_le.mp hlt'
      have h1 : y ∈ cube (s w) w := cube_mono hlt.le w (mem_cube_comm.mp hw)
      have := hcell w y h1
      omega
    have hunion : ∀ z ∈ cube k y, cube (s z) z ⊆ cube k y := fun z hz => by
      rw [← cube_eq_of_mem hz]
      exact cube_mono (hsmall z hz) z
    have hJ : avg (cube k y) (fun x => f x ^ (1 / θ)) ≤ avg (cube k y) G := by
      simp only [avg]
      exact div_le_div_of_nonneg_right (sum_cellAvg_rpow_le hcell hG hθ hθ1 hunion)
        (Nat.cast_nonneg _)
    have hsub12 : enl 1 k y ⊆ enl 2 k y := box_mono _ (halfSide_mono (by omega))
    have hR := hRH k y hge (hsub12.trans hΩ)
    -- the points of `9□` whose cell meets `3□` form a union of cells containing `3□`
    set T := (enl 2 k y).filter (fun z => (cube (s z) z ∩ enl 1 k y).Nonempty) with hT
    have hTunion : ∀ z ∈ T, cube (s z) z ⊆ T := by
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      intro w hw
      refine Finset.mem_filter.mpr ⟨cell_subset_enl_two hcell hnb hge hz' hw, ?_⟩
      rw [hcell z w hw, cube_eq_of_mem hw]
      exact hz'
    have hT1 : enl 1 k y ⊆ T := fun w hw =>
      Finset.mem_filter.mpr ⟨hsub12 hw, ⟨w, Finset.mem_inter.mpr ⟨mem_cube_self _ w, hw⟩⟩⟩
    have hsumT : ∑ z ∈ enl 1 k y, G z ^ θ ≤ ∑ z ∈ enl 2 k y, f z := by
      calc ∑ z ∈ enl 1 k y, G z ^ θ ≤ ∑ z ∈ T, G z ^ θ :=
            Finset.sum_le_sum_of_subset_of_nonneg hT1 fun z _ _ => Real.rpow_nonneg (hG z) _
        _ = ∑ z ∈ T, f z := sum_eq_sum_avg (fun z => cube (s z) z) (fun z _ => mem_cube_self _ z)
              hTunion (fun z _ z' hz' => by rw [hcell z z' hz', cube_eq_of_mem hz']) _
        _ ≤ ∑ z ∈ enl 2 k y, f z :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun z _ _ => hf0 z
    have henl1 : ((enl 2 k y).card : ℝ) = (3 : ℝ) ^ d * (enl 1 k y).card := by
      rw [card_enl, card_enl, show k + 2 = (k + 1) + 1 by omega, pow_succ, mul_pow, mul_comm]
    have hA1 : avg (enl 1 k y) (fun x => G x ^ θ) ≤ (3 : ℝ) ^ d * avg (enl 2 k y) f := by
      simp only [avg]
      rw [henl1]
      have hpos : (0 : ℝ) < (enl 1 k y).card := by
        rw [card_enl]
        positivity
      rw [div_le_iff₀ hpos]
      calc ∑ z ∈ enl 1 k y, G z ^ θ ≤ ∑ z ∈ enl 2 k y, f z := hsumT
        _ = (3 : ℝ) ^ d * ((∑ z ∈ enl 2 k y, f z) / ((3 : ℝ) ^ d * (enl 1 k y).card)) *
              (enl 1 k y).card := by
            field_simp
    have hA10 : 0 ≤ avg (enl 1 k y) (fun x => G x ^ θ) :=
      div_nonneg (Finset.sum_nonneg fun z _ => Real.rpow_nonneg (hG z) _) (Nat.cast_nonneg _)
    have h3d : (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (2 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc avg (cube k y) (fun x => f x ^ (1 / θ)) ≤ avg (cube k y) G := hJ
      _ ≤ A₀ * avg (enl 1 k y) (fun x => G x ^ θ) ^ (1 / θ) := hR
      _ ≤ A₀ * ((3 : ℝ) ^ (2 * d) * avg (enl 2 k y) f) ^ (1 / θ) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA10 ?_ h1θ) (by linarith)
          exact hA1.trans (mul_le_mul_of_nonneg_right h3d havg0)
      _ = A₀ * ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) * avg (enl 2 k y) f ^ (1 / θ) := by
          rw [Real.mul_rpow (by positivity) havg0]
          ring

end Rigidity.Proofs.Cluster
