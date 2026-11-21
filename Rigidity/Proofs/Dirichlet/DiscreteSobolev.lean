import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# A discrete Sobolev inequality on lattice cubes

For a function `f` on `ℤ^d`, a point `x` and `M ≥ 1`,
`|f(x)| ≤ Σ_{S ⊆ {1,…,d}} M^{|S| − d} Σ_{y ∈ x + {0,…,M−1}^d} |∂^S f(y)|`,
where `∂^S` is the mixed forward difference in the coordinates of `S`. It follows from the
one-dimensional bound `|g(0)| ≤ M⁻¹ Σ_{t<M} |g(t)| + Σ_{t<M} |∇g(t)|`, applied one coordinate at
a time on the partial cubes that are full in the coordinates already treated.

This is the discrete form of the embedding `W^{d,1} ⊂ L^∞` used, with the Caccioppoli inequality
for the mixed differences of a constant-coefficient harmonic function, to bound such functions
pointwise by their averages, which gives the large-scale regularity of the discrete homogenized
solutions.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The mixed difference `∂^S f(y) = Σ_{R ⊆ S} (−1)^{|S| − |R|} f(y + Σ_{j ∈ R} e_j)`. -/
def mixedDiff (S : Finset (Fin d)) (f : Vertex d → ℝ) (y : Vertex d) : ℝ :=
  ∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) * f (y + ∑ j ∈ R, unit j)

theorem mixedDiff_empty (f : Vertex d → ℝ) (y : Vertex d) : mixedDiff ∅ f y = f y := by
  simp [mixedDiff]

/-- `∂^{S ∪ {k}} f = ∇_k ∂^S f` for `k ∉ S`. -/
theorem mixedDiff_insert {S : Finset (Fin d)} {k : Fin d} (hk : k ∉ S) (f : Vertex d → ℝ)
    (y : Vertex d) :
    mixedDiff (insert k S) f y = mixedDiff S f (y + unit k) - mixedDiff S f y := by
  classical
  unfold mixedDiff
  rw [Finset.sum_powerset_insert hk, Finset.card_insert_of_notMem hk]
  have h1 : ∀ R ∈ S.powerset, (-1 : ℝ) ^ (S.card + 1 - R.card) * f (y + ∑ j ∈ R, unit j) =
      -((-1 : ℝ) ^ (S.card - R.card) * f (y + ∑ j ∈ R, unit j)) := by
    intro R hR
    have hRS : R.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.mp hR)
    rw [show S.card + 1 - R.card = (S.card - R.card) + 1 by omega, pow_succ]
    ring
  have h2 : ∀ R ∈ S.powerset, (-1 : ℝ) ^ (S.card + 1 - (insert k R).card) *
      f (y + ∑ j ∈ insert k R, unit j) =
        (-1 : ℝ) ^ (S.card - R.card) * f (y + unit k + ∑ j ∈ R, unit j) := by
    intro R hR
    have hkR : k ∉ R := fun h => hk (Finset.mem_powerset.mp hR h)
    rw [Finset.card_insert_of_notMem hkR, Finset.sum_insert hkR,
      show S.card + 1 - (R.card + 1) = S.card - R.card by omega, add_assoc]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  ring

/-- **One-dimensional bound**:
`|g(y)| ≤ M⁻¹ Σ_{t<M} |g(y + t e_k)| + Σ_{t<M} |∇_k g(y + t e_k)|`. -/
theorem abs_le_line_avg_add (g : Vertex d → ℝ) (y : Vertex d) (k : Fin d) {M : ℕ}
    (hM : 0 < M) :
    |g y| ≤ 1 / M * ∑ t ∈ Finset.range M, |g (y + (t : ℤ) • unit k)| +
      ∑ t ∈ Finset.range M, |g (y + (t : ℤ) • unit k + unit k) - g (y + (t : ℤ) • unit k)| := by
  set D := ∑ t ∈ Finset.range M, |g (y + (t : ℤ) • unit k + unit k) - g (y + (t : ℤ) • unit k)|
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hpt : ∀ t ∈ Finset.range M, |g y| ≤ |g (y + (t : ℤ) • unit k)| + D := by
    intro t ht
    have htel : g (y + (t : ℤ) • unit k) - g y = ∑ s ∈ Finset.range t,
        (g (y + (s : ℤ) • unit k + unit k) - g (y + (s : ℤ) • unit k)) := by
      have h := Finset.sum_range_sub (fun s : ℕ => g (y + (s : ℤ) • unit k)) t
      simp only [Nat.cast_zero, zero_smul, add_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc]
    have hsub : Finset.range t ⊆ Finset.range M :=
      Finset.range_subset_range.mpr (Finset.mem_range.mp ht).le
    have h1 : |g (y + (t : ℤ) • unit k) - g y| ≤ D := by
      rw [htel]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (g y) (g (y + (t : ℤ) • unit k))
    rw [abs_sub_comm] at this
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [one_div, ← div_eq_inv_mul, ← sub_le_iff_le_add, le_div_iff₀ hM']
  nlinarith

/-- The partial cube: the coordinates in `T` range over `[x_j, x_j + M)`, the others equal
`x_j`. -/
noncomputable def partialCube (x : Vertex d) (M : ℕ) (T : Finset (Fin d)) : Finset (Vertex d) :=
  Fintype.piFinset fun j => if j ∈ T then Finset.Ico (x j) (x j + M) else {x j}

theorem partialCube_empty (x : Vertex d) (M : ℕ) : partialCube x M ∅ = {x} := by
  have : (fun j => if j ∈ (∅ : Finset (Fin d)) then Finset.Ico (x j) (x j + M) else {x j}) =
      fun j => {x j} := by
    funext j
    simp
  rw [partialCube, this, Fintype.piFinset_singleton]

theorem partialCube_univ (x : Vertex d) (M : ℕ) :
    partialCube x M Finset.univ = (cornerCube x M).vertices := by
  ext y
  simp [partialCube, IntegerCube.vertices, cornerCube]

theorem add_smul_unit_apply_self (y : Vertex d) (t : ℤ) (k : Fin d) :
    (y + t • unit k) k = y k + t := by
  simp [unit]

theorem add_smul_unit_apply_of_ne (y : Vertex d) (t : ℤ) {j k : Fin d} (h : j ≠ k) :
    (y + t • unit k) j = y j := by
  simp [unit, h]

/-- **Sweeping a new coordinate**: summing over the lines in the direction `k ∉ T` through the
partial cube for `T` is summing over the partial cube for `T ∪ {k}`. -/
theorem sum_partialCube_insert (x : Vertex d) (M : ℕ) {T : Finset (Fin d)} {k : Fin d}
    (hk : k ∉ T) (F : Vertex d → ℝ) :
    ∑ y ∈ partialCube x M T, ∑ t ∈ Finset.range M, F (y + (t : ℤ) • unit k) =
      ∑ y ∈ partialCube x M (insert k T), F y := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => p.1 + (p.2 : ℤ) • unit k)
    (fun y => (Function.update y k (x k), (y k - x k).toNat)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨y, t⟩ hp
    obtain ⟨hy, ht⟩ := Finset.mem_product.mp hp
    rw [partialCube, Fintype.mem_piFinset] at hy ⊢
    rw [Finset.mem_range] at ht
    intro j
    have hyj := hy j
    rcases eq_or_ne j k with rfl | hjk
    · simp only [hk, if_false, Finset.mem_singleton] at hyj
      dsimp only
      rw [add_smul_unit_apply_self]
      simp only [Finset.mem_insert_self, if_true, Finset.mem_Ico]
      omega
    · dsimp only
      rw [add_smul_unit_apply_of_ne _ _ hjk]
      simp only [Finset.mem_insert, hjk, false_or]
      exact hyj
  · intro y hy
    rw [partialCube, Fintype.mem_piFinset] at hy
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [partialCube, Fintype.mem_piFinset]
      intro j
      rcases eq_or_ne j k with rfl | hjk
      · simp [hk]
      · dsimp only
        rw [Function.update_of_ne hjk]
        have := hy j
        simpa [Finset.mem_insert, hjk] using this
    · have := hy k
      simp only [Finset.mem_insert_self, if_true, Finset.mem_Ico] at this
      rw [Finset.mem_range]
      omega
  · rintro ⟨y, t⟩ hp
    obtain ⟨hy, ht⟩ := Finset.mem_product.mp hp
    rw [partialCube, Fintype.mem_piFinset] at hy
    have hyk := hy k
    simp only [hk, if_false, Finset.mem_singleton] at hyk
    refine Prod.ext ?_ ?_
    · funext j
      dsimp only
      rcases eq_or_ne j k with rfl | hjk
      · rw [Function.update_self, hyk]
      · rw [Function.update_of_ne hjk, add_smul_unit_apply_of_ne _ _ hjk]
    · dsimp only
      rw [add_smul_unit_apply_self]
      omega
  · intro y hy
    rw [partialCube, Fintype.mem_piFinset] at hy
    have hyk := hy k
    simp only [Finset.mem_insert_self, if_true, Finset.mem_Ico] at hyk
    funext j
    dsimp only
    rcases eq_or_ne j k with rfl | hjk
    · rw [add_smul_unit_apply_self, Function.update_self]
      omega
    · rw [add_smul_unit_apply_of_ne _ _ hjk, Function.update_of_ne hjk]
  · intro p _
    rfl

/-- **Discrete Sobolev inequality on partial cubes**: for `M ≥ 1` and every `T`,
`|f(x)| ≤ Σ_{S ⊆ T} M^{|S| − |T|} Σ_{y ∈ partialCube x M T} |∂^S f(y)|`. -/
theorem abs_le_sum_mixedDiff_partialCube (f : Vertex d → ℝ) (x : Vertex d) {M : ℕ}
    (hM : 0 < M) (T : Finset (Fin d)) :
    |f x| ≤ ∑ S ∈ T.powerset, (1 / (M : ℝ)) ^ (T.card - S.card) *
      ∑ y ∈ partialCube x M T, |mixedDiff S f y| := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [partialCube_empty, mixedDiff_empty]
  | insert k T hk ih =>
    have hc : 0 ≤ 1 / (M : ℝ) := by positivity
    refine ih.trans ?_
    rw [Finset.sum_powerset_insert hk, Finset.card_insert_of_notMem hk]
    have hstep : ∀ S ∈ T.powerset, (1 / (M : ℝ)) ^ (T.card - S.card) *
        ∑ y ∈ partialCube x M T, |mixedDiff S f y| ≤
        (1 / (M : ℝ)) ^ (T.card + 1 - S.card) *
            ∑ y ∈ partialCube x M (insert k T), |mixedDiff S f y| +
          (1 / (M : ℝ)) ^ (T.card + 1 - (insert k S).card) *
            ∑ y ∈ partialCube x M (insert k T), |mixedDiff (insert k S) f y| := by
      intro S hS
      have hST : S ⊆ T := Finset.mem_powerset.mp hS
      have hkS : k ∉ S := fun h => hk (hST h)
      have hcard : S.card ≤ T.card := Finset.card_le_card hST
      rw [Finset.card_insert_of_notMem hkS, show T.card + 1 - (S.card + 1) = T.card - S.card by
        omega, show T.card + 1 - S.card = (T.card - S.card) + 1 by omega, pow_succ,
        ← sum_partialCube_insert x M hk, ← sum_partialCube_insert x M hk]
      have hline : ∀ y, |mixedDiff S f y| ≤
          1 / M * ∑ t ∈ Finset.range M, |mixedDiff S f (y + (t : ℤ) • unit k)| +
            ∑ t ∈ Finset.range M, |mixedDiff (insert k S) f (y + (t : ℤ) • unit k)| := by
        intro y
        have h := abs_le_line_avg_add (mixedDiff S f) y k hM
        simp only [← mixedDiff_insert hkS] at h
        exact h
      have hsum := Finset.sum_le_sum fun y (_ : y ∈ partialCube x M T) => hline y
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
      have hpow : 0 ≤ (1 / (M : ℝ)) ^ (T.card - S.card) := pow_nonneg hc _
      calc (1 / (M : ℝ)) ^ (T.card - S.card) * ∑ y ∈ partialCube x M T, |mixedDiff S f y|
          ≤ (1 / (M : ℝ)) ^ (T.card - S.card) * (1 / M * ∑ y ∈ partialCube x M T,
              ∑ t ∈ Finset.range M, |mixedDiff S f (y + (t : ℤ) • unit k)| +
            ∑ y ∈ partialCube x M T, ∑ t ∈ Finset.range M,
              |mixedDiff (insert k S) f (y + (t : ℤ) • unit k)|) :=
            mul_le_mul_of_nonneg_left hsum hpow
        _ = _ := by ring
    calc ∑ S ∈ T.powerset, (1 / (M : ℝ)) ^ (T.card - S.card) *
          ∑ y ∈ partialCube x M T, |mixedDiff S f y|
        ≤ ∑ S ∈ T.powerset, ((1 / (M : ℝ)) ^ (T.card + 1 - S.card) *
            ∑ y ∈ partialCube x M (insert k T), |mixedDiff S f y| +
          (1 / (M : ℝ)) ^ (T.card + 1 - (insert k S).card) *
            ∑ y ∈ partialCube x M (insert k T), |mixedDiff (insert k S) f y|) :=
          Finset.sum_le_sum hstep
      _ = _ := Finset.sum_add_distrib

/-- **Discrete Sobolev inequality on a cube**: for `M ≥ 1`,
`|f(x)| ≤ Σ_{S ⊆ {1,…,d}} M^{|S| − d} Σ_{y ∈ x + {0,…,M−1}^d} |∂^S f(y)|`. -/
theorem abs_le_sum_mixedDiff_cube (f : Vertex d → ℝ) (x : Vertex d) {M : ℕ} (hM : 0 < M) :
    |f x| ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, (1 / (M : ℝ)) ^ (d - S.card) *
      ∑ y ∈ (cornerCube x M).vertices, |mixedDiff S f y| := by
  have h := abs_le_sum_mixedDiff_partialCube f x hM Finset.univ
  rwa [partialCube_univ, Finset.card_univ, Fintype.card_fin] at h

end Rigidity.Dirichlet
