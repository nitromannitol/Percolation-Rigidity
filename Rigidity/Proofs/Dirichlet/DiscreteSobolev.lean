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

end Rigidity.Dirichlet
