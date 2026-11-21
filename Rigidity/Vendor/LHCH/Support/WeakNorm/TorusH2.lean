/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusH2.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusCalculus

/-!
# The discrete H² identity on the torus

Sums over the period box of a `2N`-periodic function are invariant under translations, and for a
`2N`-periodic `f`, `Σ_x (∇*∇ f(x))² = Σ_x Σ_{i,j} (∇_i∇_j f(x))²` exactly: both sides are the
same combination of the autocorrelations `Σ_x f(x) f(x + a)`.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- A function of period `2N` in every coordinate is invariant under every translation by a vector
whose coordinates are multiples of `2N`. -/
theorem isTorusPeriodic_add_smul (N : ℕ) (g : Site d → ℝ) (hg : IsTorusPeriodic N g)
    (k x : Site d) : g (x + (2 * (N : ℤ)) • k) = g x := by
  let H : AddSubgroup (Site d) :=
    { carrier := {w | ∀ x, g (x + w) = g x}
      zero_mem' := by intro x; simp
      add_mem' := by
        intro a b ha hb x
        rw [← add_assoc, hb (x + a), ha x]
      neg_mem' := by
        intro a ha x
        have := ha (x + -a)
        simpa using this.symm }
  have hk : (2 * (N : ℤ)) • k = ∑ i : Fin d, k i • ((2 * (N : ℤ)) • unit i) := by
    ext j
    simp [Finset.sum_apply, unit, Pi.single_apply]
    ring
  have hmem : (2 * (N : ℤ)) • k ∈ H := by
    rw [hk]
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (show (2 * (N : ℤ)) • unit i ∈ H from fun x => hg x i) _
  exact hmem x

/-- The reduction of a site modulo `2N` in every coordinate. -/
def torusReduce (N : ℕ) (x : Site d) : Site d := fun i => x i % (2 * (N : ℤ))

/-- A function of period `2N` takes the same value at a site and at its reduction. -/
theorem isTorusPeriodic_apply_torusReduce (N : ℕ) (g : Site d → ℝ) (hg : IsTorusPeriodic N g)
    (x : Site d) : g (torusReduce N x) = g x := by
  have h := isTorusPeriodic_add_smul N g hg (fun i => x i / (2 * (N : ℤ))) (torusReduce N x)
  have hx : torusReduce N x + (2 * (N : ℤ)) • (fun i => x i / (2 * (N : ℤ))) = x := by
    ext i
    simp only [torusReduce, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Int.emod_add_mul_ediv (x i) _
  rw [hx] at h
  exact h.symm

/-- The reduction modulo `2N` lies in the period box. -/
theorem torusReduce_mem_torusBox (N : ℕ) (hN : 0 < N) (x : Site d) :
    torusReduce N x ∈ torusBox d N := by
  simp only [torusBox, torusReduce, Fintype.mem_piFinset, Finset.mem_Ico]
  intro i
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

/-- The reduction modulo `2N` fixes every site of the period box. -/
theorem torusReduce_of_mem_torusBox (N : ℕ) {x : Site d} (hx : x ∈ torusBox d N) :
    torusReduce N x = x := by
  simp only [torusBox, Fintype.mem_piFinset, Finset.mem_Ico] at hx
  ext i
  exact Int.emod_eq_of_lt (hx i).1 (hx i).2

/-- The reduction of a translate by `v` of the reduction of `x` is the reduction of `x + v`. -/
theorem torusReduce_add_torusReduce (N : ℕ) (x v : Site d) :
    torusReduce N (torusReduce N x + v) = torusReduce N (x + v) := by
  ext i
  simp only [torusReduce, Pi.add_apply]
  rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.add_emod]

/-- **Sums over the period box are translation invariant** for functions of period `2N`. -/
theorem sum_torusBox_add (N : ℕ) (hN : 0 < N) (g : Site d → ℝ) (hg : IsTorusPeriodic N g)
    (v : Site d) : ∑ x ∈ torusBox d N, g (x + v) = ∑ x ∈ torusBox d N, g x := by
  refine Finset.sum_nbij' (fun x => torusReduce N (x + v)) (fun x => torusReduce N (x - v))
    (fun x _ => torusReduce_mem_torusBox N hN _) (fun x _ => torusReduce_mem_torusBox N hN _)
    ?_ ?_ ?_
  · intro x hx
    simp only [sub_eq_add_neg]
    rw [torusReduce_add_torusReduce]
    simp [torusReduce_of_mem_torusBox N hx]
  · intro x hx
    simp only [sub_eq_add_neg]
    rw [torusReduce_add_torusReduce]
    simp [torusReduce_of_mem_torusBox N hx]
  · intro x _
    exact (isTorusPeriodic_apply_torusReduce N g hg (x + v)).symm

/-- The product of a function of period `2N` with a translate of itself has period `2N`. -/
theorem isTorusPeriodic_mul_shift (N : ℕ) (f : Site d → ℝ) (hf : IsTorusPeriodic N f)
    (c : Site d) : IsTorusPeriodic N (fun y => f y * f (y + c)) := by
  intro x i
  have h : x + (2 * (N : ℤ)) • unit i + c = (x + c) + (2 * (N : ℤ)) • unit i := by abel
  simp only [h, hf x i, hf (x + c) i]

/-- One summand of the expansion of the discrete `H²` identity: for a function of period `2N` and
two vectors `u`, `w`, `Σ_x (∇*_u ∇_u f)(∇*_w ∇_w f) = Σ_x (∇_u ∇_w f)²`. -/
theorem sum_second_difference_mul_eq (N : ℕ) (hN : 0 < N) (f : Site d → ℝ)
    (hf : IsTorusPeriodic N f) (u w : Site d) :
    ∑ x ∈ torusBox d N, (2 * f x - f (x + u) - f (x - u)) * (2 * f x - f (x + w) - f (x - w)) =
      ∑ x ∈ torusBox d N, (f (x + u + w) - f (x + u) - f (x + w) + f x) ^ 2 := by
  set C : Site d → ℝ := fun a => ∑ x ∈ torusBox d N, f x * f (x + a) with hC
  have hshift : ∀ a b, ∑ x ∈ torusBox d N, f (x + a) * f (x + b) = C (b - a) := by
    intro a b
    have h := sum_torusBox_add N hN _ (isTorusPeriodic_mul_shift N f hf (b - a)) a
    rw [hC]
    simp only
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, add_sub_cancel]
  have hneg : ∀ a, C (-a) = C a := by
    intro a
    have h := hshift a 0
    simp only [add_zero, zero_sub] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have eL : ∀ x, (2 * f x - f (x + u) - f (x - u)) * (2 * f x - f (x + w) - f (x - w)) =
      4 * (f (x + 0) * f (x + 0)) - 2 * (f (x + 0) * f (x + w)) - 2 * (f (x + 0) * f (x + -w))
        - 2 * (f (x + u) * f (x + 0)) + f (x + u) * f (x + w) + f (x + u) * f (x + -w)
        - 2 * (f (x + -u) * f (x + 0)) + f (x + -u) * f (x + w) + f (x + -u) * f (x + -w) := by
    intro x
    simp only [add_zero, sub_eq_add_neg]
    ring
  have eR : ∀ x, (f (x + u + w) - f (x + u) - f (x + w) + f x) ^ 2 =
      f (x + (u + w)) * f (x + (u + w)) + f (x + u) * f (x + u) + f (x + w) * f (x + w)
        + f (x + 0) * f (x + 0) - 2 * (f (x + (u + w)) * f (x + u))
        - 2 * (f (x + (u + w)) * f (x + w)) + 2 * (f (x + (u + w)) * f (x + 0))
        + 2 * (f (x + u) * f (x + w)) - 2 * (f (x + u) * f (x + 0))
        - 2 * (f (x + w) * f (x + 0)) := by
    intro x
    simp only [add_zero, add_assoc]
    ring
  rw [Finset.sum_congr rfl fun x _ => eL x, Finset.sum_congr rfl fun x _ => eR x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hshift]
  have hsub : C (u - w) = C (w - u) := by rw [← hneg (w - u), neg_sub]
  have hcomm : C (w + u) = C (u + w) := by rw [add_comm]
  simp only [sub_self, sub_zero, zero_sub, neg_sub_left, sub_neg_eq_add,
    neg_add_eq_sub, sub_add_cancel_left, sub_add_cancel_right, hneg, zero_add, hsub, hcomm]
  ring

/-- **The discrete `H²` identity on the torus**: for `f` of period `2N`,
`Σ_x (∇*∇ f(x))² = Σ_x Σ_{i,j} (∇_i∇_j f(x))²`, because the differences commute and sums over
the period box are translation invariant. -/
theorem sum_latticeLaplacian_sq_eq (N : ℕ) (hN : 0 < N) (f : Site d → ℝ)
    (hf : IsTorusPeriodic N f) :
    ∑ x ∈ torusBox d N, latticeLaplacian f x ^ 2 =
      ∑ x ∈ torusBox d N, ∑ i : Fin d, ∑ j : Fin d, secondDiff f i j x ^ 2 := by
  have hL : ∀ x, latticeLaplacian f x ^ 2 = ∑ i : Fin d, ∑ j : Fin d,
      (2 * f x - f (x + unit i) - f (x - unit i)) *
        (2 * f x - f (x + unit j) - f (x - unit j)) := by
    intro x
    rw [sq, latticeLaplacian, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun x _ => hL x, Finset.sum_comm,
    Finset.sum_comm (s := torusBox d N)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (s := torusBox d N)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_second_difference_mul_eq N hN f hf (unit i) (unit j)

end LatticeHC

end
