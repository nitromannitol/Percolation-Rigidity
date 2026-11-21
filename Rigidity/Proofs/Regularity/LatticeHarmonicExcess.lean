import Rigidity.Proofs.Regularity.LatticeHarmonicRegularity
import Rigidity.Proofs.Regularity.LatticeBalls

/-!
# Excess decay of order one of lattice harmonic functions on lattice balls

For a function `F` on `ℤ^d` harmonic on the Euclidean ball `B_r(z)` and an affine function `w`,
`f = F - w` is harmonic, its second forward differences are bounded on `Q_m(z)` by
`m^{-d/2 - 2}` times its `ℓ²` norm on `B_r(z)` (`sq_fwd_fwd_le`, for `Q_{Λ m}(z) ⊆ B_r(z)`), and the
first-order Taylor expansion of `f` at the corner `z - n 𝟙`, `n = ⌊s⌋`, approximates `f` on
`B_s(z)` up to `d (d + 1) (2n)²` times this bound (`abs_sub_taylor_le`). This file collects the
lattice facts used to turn these bounds into the excess decay of order one
(`HarmonicRegularity` with `j = 1`) of lattice harmonic functions on the balls of
`latticeComponent d`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

theorem latticeEuclideanEmbedding_add (y v : Fin d → ℤ) :
    latticeEuclideanEmbedding (y + v) = latticeEuclideanEmbedding y + latticeEuclideanEmbedding v := by
  ext i
  change ((y + v) i : ℝ) = (y i : ℝ) + (v i : ℝ)
  push_cast [Pi.add_apply]
  rfl

theorem latticeEuclideanEmbedding_sub (y v : Fin d → ℤ) :
    latticeEuclideanEmbedding (y - v) = latticeEuclideanEmbedding y - latticeEuclideanEmbedding v := by
  ext i
  change ((y - v) i : ℝ) = (y i : ℝ) - (v i : ℝ)
  push_cast [Pi.sub_apply]
  rfl

/-- Affine functions are lattice harmonic. -/
theorem latticeLaplacian_affine (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => a + inner ℝ p (latticeEuclideanEmbedding y)) x = 0 := by
  simp only [latticeLaplacian]
  refine sum_eq_zero fun i _ => ?_
  rw [latticeEuclideanEmbedding_add, latticeEuclideanEmbedding_sub, inner_add_right,
    inner_sub_right]
  ring

theorem dist_le_of_mem_supBox {z y : Fin d → ℤ} {L : ℕ} (hy : y ∈ supBox z L) :
    dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) ≤ Real.sqrt d * L := by
  apply dist_latticeEuclideanEmbedding_le (Nat.cast_nonneg L)
  intro i
  simp only [supBox, Fintype.mem_piFinset, mem_Icc] at hy
  obtain ⟨h1, h2⟩ := hy i
  change |(y i : ℝ) - (z i : ℝ)| ≤ L
  rw [abs_le]
  constructor
  · have : (z i : ℝ) - L ≤ y i := by exact_mod_cast h1
    linarith
  · have : (y i : ℝ) ≤ z i + L := by exact_mod_cast h2
    linarith

/-- A sup-norm box inside a Euclidean ball: square sums over the box are bounded by those over the
ball of the lattice. -/
theorem sum_sq_supBox_le_ball [NeZero d] (z : Fin d → ℤ) {L : ℕ} {r : ℝ}
    (hL : Real.sqrt d * L < r) (F : (Fin d → ℤ) → ℝ) :
    ∑ y ∈ supBox z L, F y ^ 2 ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent d) z r, F x.val ^ 2 := by
  classical
  have hmem : ∀ y : Fin d → ℤ, y ∈ (latticeComponent d).supp := fun y => by
    rw [latticeComponent_supp]; trivial
  have e : ∑ x ∈ componentEuclideanBall (latticeComponent d) z r, F x.val ^ 2 =
      ∑ y ∈ (componentEuclideanBall (latticeComponent d) z r).image Subtype.val, F y ^ 2 :=
    (sum_image (f := fun y => F y ^ 2) fun x _ y _ h => Subtype.val_injective h).symm
  rw [e]
  refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun _ _ _ => sq_nonneg _
  rw [Finset.mem_image]
  refine ⟨⟨y, hmem y⟩, ?_, rfl⟩
  rw [mem_componentEuclideanBall]
  exact (dist_le_of_mem_supBox hy).trans_lt hL

theorem sum_sq_eq_card_mul_componentBallL2_sq {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) (g : C → ℝ) :
    ∑ x ∈ componentEuclideanBall C z r, g x ^ 2 =
      ((componentEuclideanBall C z r).card : ℝ) * componentBallL2 C z r g ^ 2 := by
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C z r).card with h | h
  · rw [Finset.card_eq_zero.1 h]; simp
  · have hc : (0 : ℝ) < (componentEuclideanBall C z r).card := by exact_mod_cast h
    rw [componentBallL2, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) hc.le)]
    field_simp

/-- Lattice points of the ball `B_s(z)` lie in `Q_{⌊s⌋}(z)`. -/
theorem abs_sub_le_floor_of_mem_ball {ω : Configuration d} {C : OpenComponent ω} {z : Vertex d}
    {s : ℝ} {x : C} (hx : x ∈ componentEuclideanBall C z s) (i : Fin d) :
    |x.val i - z i| ≤ (⌊s⌋₊ : ℤ) := by
  rw [mem_componentEuclideanBall] at hx
  have h1 := (abs_sub_le_dist_latticeEuclideanEmbedding x.val z i).trans_lt hx
  have hs0 : 0 ≤ s := (abs_nonneg _).trans h1.le
  have h2 : ((|x.val i - z i| : ℤ) : ℝ) < s := by push_cast; exact h1
  have h3 : (|x.val i - z i|).toNat < s := by
    have : ((|x.val i - z i|).toNat : ℤ) = |x.val i - z i| := Int.toNat_of_nonneg (abs_nonneg _)
    have h4 : (((|x.val i - z i|).toNat : ℕ) : ℝ) = ((|x.val i - z i| : ℤ) : ℝ) := by
      exact_mod_cast this
    rw [h4]; exact h2
  have h5 : (|x.val i - z i|).toNat ≤ ⌊s⌋₊ := Nat.le_floor h3.le
  omega

end Rigidity.Proofs.Regularity
