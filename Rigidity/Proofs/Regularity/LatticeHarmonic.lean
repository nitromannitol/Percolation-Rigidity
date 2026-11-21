import LatticeProb.Graph.Zd
import LatticeProb.Network.LocalCaccioppoli
import Rigidity.Proofs.Regularity.MixedDifferenceSobolev

/-!
# Discrete harmonic functions on the lattice

The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))` (`latticeLaplacian`) is the
network Laplacian of `ℤ^d` with unit conductances (`netLaplacian_lattice`). It commutes with
translations, so the forward differences, and more generally the mixed differences, of a function
harmonic on a region are harmonic on the region shrunk by the directions of the differences
(`latticeLaplacian_mixedDiff`). These are the first ingredients of the interior regularity of
discrete harmonic functions (Caccioppoli inequalities for their differences of all orders).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The lattice Laplacian `Δ f(x) = ∑ᵢ (f(x + eᵢ) + f(x - eᵢ) - 2 f(x))`. -/
noncomputable def latticeLaplacian (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ∑ i, (f (x + unit i) + f (x - unit i) - 2 * f x)

theorem unit_add_ne_sub (x : Fin d → ℤ) (i : Fin d) : x + unit i ≠ x - unit i := by
  intro h
  have := congrFun h i
  simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
  omega

/-- The lattice Laplacian is the network Laplacian of `ℤ^d` with unit conductances. -/
theorem netLaplacian_lattice (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f x = latticeLaplacian f x := by
  classical
  rw [Network.netLaplacian_unitCond, Graph.laplacian, Graph.Zd.neighborFinset_eq, nbrFinset,
    sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair (unit_add_ne_sub x i)]
    ring
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The lattice Laplacian commutes with translations. -/
theorem latticeLaplacian_comp_add (f : (Fin d → ℤ) → ℝ) (v x : Fin d → ℤ) :
    latticeLaplacian (fun y => f (y + v)) x = latticeLaplacian f (x + v) := by
  simp only [latticeLaplacian]
  refine sum_congr rfl fun i _ => ?_
  rw [add_right_comm x (unit i) v, sub_add_eq_add_sub, add_sub_right_comm]

theorem latticeLaplacian_sub (f g : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => f y - g y) x = latticeLaplacian f x - latticeLaplacian g x := by
  simp only [latticeLaplacian, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- The mixed difference `D_S f` is harmonic wherever `f` is harmonic at all the points
`x + ∑_{j ∈ U} e_j`, `U ⊆ S`. -/
theorem latticeLaplacian_mixedDiff (S : Finset (Fin d)) (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ)
    (hf : ∀ U ∈ S.powerset, latticeLaplacian f (x + shiftSum U) = 0) :
    latticeLaplacian (mixedDiff S f) x = 0 := by
  have hi : ∀ i, mixedDiff S f (x + unit i) + mixedDiff S f (x - unit i) - 2 * mixedDiff S f x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) *
        (f (x + shiftSum U + unit i) + f (x + shiftSum U - unit i) - 2 * f (x + shiftSum U)) := by
    intro i
    simp only [mixedDiff, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun U _ => ?_
    rw [add_right_comm x (unit i), sub_add_eq_add_sub]
    ring
  have h : latticeLaplacian (mixedDiff S f) x =
      ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * latticeLaplacian f (x + shiftSum U) := by
    rw [latticeLaplacian, sum_congr rfl fun i _ => hi i, sum_comm]
    refine sum_congr rfl fun U _ => ?_
    rw [latticeLaplacian, mul_sum]
  rw [h]
  exact sum_eq_zero fun U hU => by rw [hf U hU, mul_zero]

/-- The `ℓ^∞` box `{x : |xᵢ - zᵢ| ≤ m for all i}`. -/
noncomputable def supBox (z : Fin d → ℤ) (m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Icc (z i - m) (z i + m)

/-- The `ℓ^∞` distance `maxᵢ |xᵢ - zᵢ|`. -/
def supDist (x z : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i - z i).natAbs

theorem mem_supBox_iff_supDist_le {z x : Fin d → ℤ} {m : ℕ} :
    x ∈ supBox z m ↔ supDist x z ≤ m := by
  simp only [supBox, Fintype.mem_piFinset, mem_Icc, supDist, Finset.sup_le_iff, mem_univ,
    true_implies]
  refine forall_congr' fun i => ?_
  omega

theorem supDist_add_unit_le (x z : Fin d → ℤ) (i : Fin d) (s : ℤ) (hs : |s| ≤ 1) :
    supDist (x + s • unit i) z ≤ supDist x z + 1 := by
  simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
  intro j
  have hj : (x j - z j).natAbs ≤ Finset.univ.sup fun i => (x i - z i).natAbs :=
    Finset.le_sup (f := fun i => (x i - z i).natAbs) (mem_univ j)
  have hu : |(s • unit i) j| ≤ 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
    split_ifs <;> simp [hs]
  have : (x + s • unit i) j - z j = (x j - z j) + (s • unit i) j := by
    simp only [Pi.add_apply]; ring
  rw [this]
  have h1 := Int.natAbs_add_le (x j - z j) ((s • unit i) j)
  have h2 : ((s • unit i) j).natAbs ≤ 1 := by
    have h : (((s • unit i) j).natAbs : ℤ) ≤ 1 := by rw [← Int.abs_eq_natAbs]; exact hu
    exact_mod_cast h
  omega

/-- Neighbours differ by at most one in `ℓ^∞` distance. -/
theorem abs_supDist_sub_le_one {x y : Fin d → ℤ} (hy : y ∈ nbrFinset x) (z : Fin d → ℤ) :
    |(supDist y z : ℝ) - supDist x z| ≤ 1 := by
  obtain ⟨i, rfl | rfl⟩ := Graph.Zd.mem_nbrFinset.1 hy
  · have h1 := supDist_add_unit_le x z i 1 (by norm_num)
    have h2 := supDist_add_unit_le (x + unit i) z i (-1) (by norm_num)
    rw [one_smul] at h1
    rw [neg_one_smul, add_neg_cancel_right] at h2
    have h1' : (supDist (x + unit i) z : ℝ) ≤ supDist x z + 1 := by exact_mod_cast h1
    have h2' : (supDist x z : ℝ) ≤ supDist (x + unit i) z + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith
  · have h1 := supDist_add_unit_le x z i (-1) (by norm_num)
    have h2 := supDist_add_unit_le (x - unit i) z i 1 (by norm_num)
    rw [neg_one_smul, ← sub_eq_add_neg] at h1
    rw [one_smul, sub_add_cancel] at h2
    have h1' : (supDist (x - unit i) z : ℝ) ≤ supDist x z + 1 := by exact_mod_cast h1
    have h2' : (supDist x z : ℝ) ≤ supDist (x - unit i) z + 1 := by exact_mod_cast h2
    rw [abs_le]
    constructor <;> linarith

end Rigidity.Proofs.Regularity
