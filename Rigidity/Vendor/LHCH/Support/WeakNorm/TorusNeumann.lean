/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusNeumann.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusH2
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusParts

/-!
# The Neumann problem on the torus

For `u` of period `2N` with mean zero over the period box, `∇*∇ w = u` has a periodic solution:
on the functions on the period box the discrete Laplacian is symmetric by summation by parts, its
kernel is the constants because a function with zero energy is invariant under every unit
translation, and its range is the orthogonal complement of its kernel.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- A translate of a function of period `2N` has period `2N`. -/
theorem isTorusPeriodic_comp_add (N : ℕ) (g : Site d → ℝ) (hg : IsTorusPeriodic N g)
    (v : Site d) : IsTorusPeriodic N (fun x => g (x + v)) := by
  intro x i
  have h : x + (2 * (N : ℤ)) • unit i + v = (x + v) + (2 * (N : ℤ)) • unit i := by abel
  simp only [h, hg (x + v) i]

/-- The product of two functions of period `2N` has period `2N`. -/
theorem isTorusPeriodic_mul (N : ℕ) (g f : Site d → ℝ) (hg : IsTorusPeriodic N g)
    (hf : IsTorusPeriodic N f) : IsTorusPeriodic N (fun x => g x * f x) := by
  intro x i
  simp only [hg x i, hf x i]

/-- The discrete Laplacian of a function of period `2N` has period `2N`. -/
theorem isTorusPeriodic_latticeLaplacian (N : ℕ) (f : Site d → ℝ) (hf : IsTorusPeriodic N f) :
    IsTorusPeriodic N (latticeLaplacian f) := by
  intro x j
  have h1 : ∀ i : Fin d, x + (2 * (N : ℤ)) • unit j + unit i
      = (x + unit i) + (2 * (N : ℤ)) • unit j := fun i => by abel
  have h2 : ∀ i : Fin d, x + (2 * (N : ℤ)) • unit j - unit i
      = (x - unit i) + (2 * (N : ℤ)) • unit j := fun i => by abel
  simp only [latticeLaplacian, h1, h2, hf x j, hf (x + unit _) j, hf (x - unit _) j]

/-- A function of period `2N` whose discrete Laplacian vanishes on the period box is constant: the
energy `Σ_x Σ_i (∇_i f(x))²` vanishes, so `f` is invariant under every unit translation. -/
theorem eq_apply_zero_of_isTorusPeriodic_latticeLaplacian_eq_zero (N : ℕ) (hN : 0 < N)
    (f : Site d → ℝ) (hf : IsTorusPeriodic N f)
    (h0 : ∀ x ∈ torusBox d N, latticeLaplacian f x = 0) (x : Site d) : f x = f 0 := by
  have hsum : ∑ x ∈ torusBox d N, ∑ i : Fin d,
      (f (x + unit i) - f x) * (f (x + unit i) - f x) = 0 := by
    rw [← sum_mul_latticeLaplacian_eq N hN f f hf hf]
    exact Finset.sum_eq_zero fun x hx => by rw [h0 x hx, mul_zero]
  have hbox : ∀ x ∈ torusBox d N, ∀ i, f (x + unit i) = f x := by
    intro x hx i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _)).1 hsum x hx
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg _)).1 h1 i (Finset.mem_univ _)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)
  have hall : ∀ x i, f (x + unit i) = f x := by
    intro x i
    have hp : IsTorusPeriodic N (fun y => f (y + unit i)) := isTorusPeriodic_comp_add N f hf _
    have e1 : f (torusReduce N x + unit i) = f (x + unit i) :=
      isTorusPeriodic_apply_torusReduce N _ hp x
    have e2 : f (torusReduce N x) = f x := isTorusPeriodic_apply_torusReduce N f hf x
    rw [← e1, ← e2]
    exact hbox _ (torusReduce_mem_torusBox N hN x) i
  let H : AddSubgroup (Site d) :=
    { carrier := {w | ∀ y, f (y + w) = f y}
      zero_mem' := by intro y; simp
      add_mem' := by
        intro a b ha hb y
        rw [← add_assoc, hb (y + a), ha y]
      neg_mem' := by
        intro a ha y
        have := ha (y + -a)
        simpa using this.symm }
  have hx : x = ∑ i : Fin d, x i • unit i := by
    ext j
    simp [Finset.sum_apply, unit, Pi.single_apply]
  have hmem : x ∈ H := by
    rw [hx]
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (show unit i ∈ H from fun y => hall y i) _
  simpa using hmem 0

/-- The `2N`-periodic extension of a function on the period box. -/
def torusExtend (N : ℕ) (hN : 0 < N) (f : ↥(torusBox d N) → ℝ) : Site d → ℝ :=
  fun x => f ⟨torusReduce N x, torusReduce_mem_torusBox N hN x⟩

/-- The periodic extension has period `2N`. -/
theorem isTorusPeriodic_torusExtend (N : ℕ) (hN : 0 < N) (f : ↥(torusBox d N) → ℝ) :
    IsTorusPeriodic N (torusExtend N hN f) := by
  intro x i
  have h : torusReduce N (x + (2 * (N : ℤ)) • unit i) = torusReduce N x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [torusReduce, unit]
    · simp [torusReduce, unit, hj]
  exact congrArg f (Subtype.ext h)

/-- The periodic extension agrees with the function on the period box. -/
theorem torusExtend_apply_of_mem (N : ℕ) (hN : 0 < N) (f : ↥(torusBox d N) → ℝ)
    (b : ↥(torusBox d N)) : torusExtend N hN f b = f b :=
  congrArg f (Subtype.ext (torusReduce_of_mem_torusBox N b.2))

/-- The discrete Laplacian of the periodic extension, as a linear map on the real functions on the
period box. -/
def torusLaplacian (N : ℕ) (hN : 0 < N) :
    EuclideanSpace ℝ ↥(torusBox d N) →ₗ[ℝ] EuclideanSpace ℝ ↥(torusBox d N) where
  toFun f := WithLp.toLp 2 fun b => latticeLaplacian (torusExtend N hN f.ofLp) b
  map_add' f g := by
    ext b
    simp [latticeLaplacian, torusExtend, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    ext b
    simp [latticeLaplacian, torusExtend, ← Finset.mul_sum]
    ring

/-- The value of `torusLaplacian` at a point of the box. -/
theorem torusLaplacian_apply (N : ℕ) (hN : 0 < N) (f : EuclideanSpace ℝ ↥(torusBox d N))
    (b : ↥(torusBox d N)) :
    torusLaplacian N hN f b = latticeLaplacian (torusExtend N hN f.ofLp) b := rfl

/-- The inner product on the box is the sum over the box of the periodic extensions. -/
theorem inner_eq_sum_torusBox (N : ℕ) (hN : 0 < N) (f g : EuclideanSpace ℝ ↥(torusBox d N)) :
    inner ℝ g f =
      ∑ x ∈ torusBox d N, torusExtend N hN g.ofLp x * torusExtend N hN f.ofLp x := by
  rw [← Finset.sum_attach]
  simp [PiLp.inner_apply, torusExtend_apply_of_mem]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The pairing of `g` with the discrete Laplacian of `f` on the box is the energy pairing. -/
theorem inner_torusLaplacian_eq (N : ℕ) (hN : 0 < N)
    (f g : EuclideanSpace ℝ ↥(torusBox d N)) :
    inner ℝ g (torusLaplacian N hN f) =
      ∑ x ∈ torusBox d N, ∑ i : Fin d,
        (torusExtend N hN g.ofLp (x + unit i) - torusExtend N hN g.ofLp x) *
          (torusExtend N hN f.ofLp (x + unit i) - torusExtend N hN f.ofLp x) := by
  rw [← sum_mul_latticeLaplacian_eq N hN _ _ (isTorusPeriodic_torusExtend N hN _)
    (isTorusPeriodic_torusExtend N hN _), inner_eq_sum_torusBox N hN]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  exact (torusExtend_apply_of_mem N hN (torusLaplacian N hN f).ofLp ⟨x, hx⟩).trans
    (torusLaplacian_apply N hN f ⟨x, hx⟩)

/-- The discrete Laplacian on the torus is symmetric for the dot product on the period box. -/
theorem isSymmetric_torusLaplacian (N : ℕ) (hN : 0 < N) :
    (torusLaplacian (d := d) N hN).IsSymmetric := by
  intro f g
  rw [real_inner_comm g (torusLaplacian N hN f), inner_torusLaplacian_eq N hN f g,
    inner_torusLaplacian_eq N hN g f]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The kernel of the discrete Laplacian on the torus consists of the constants. -/
theorem exists_forall_eq_of_torusLaplacian_eq_zero (N : ℕ) (hN : 0 < N)
    (f : EuclideanSpace ℝ ↥(torusBox d N)) (hf : torusLaplacian N hN f = 0) :
    ∃ c : ℝ, ∀ b : ↥(torusBox d N), f b = c := by
  refine ⟨torusExtend N hN f.ofLp 0, fun b => ?_⟩
  rw [← torusExtend_apply_of_mem N hN f.ofLp b]
  refine eq_apply_zero_of_isTorusPeriodic_latticeLaplacian_eq_zero N hN _
    (isTorusPeriodic_torusExtend N hN _) (fun x hx => ?_) _
  have := torusLaplacian_apply N hN f ⟨x, hx⟩
  rw [hf] at this
  exact this.symm

/-- **The Neumann problem on the torus**: for `N ≥ 1` and `u` of period `2N` with mean zero over
the period box, there is `w` of period `2N` with `∇*∇ w = u` (the discrete Laplacian on the
torus is symmetric, its kernel is the constants, and its range is their orthogonal complement). -/
theorem exists_isTorusPeriodic_latticeLaplacian_eq (N : ℕ) (hN : 0 < N) (u : Site d → ℝ)
    (hu : IsTorusPeriodic N u) (hmean : ∑ x ∈ torusBox d N, u x = 0) :
    ∃ w : Site d → ℝ, IsTorusPeriodic N w ∧ ∀ x, latticeLaplacian w x = u x := by
  let uE : EuclideanSpace ℝ ↥(torusBox d N) := WithLp.toLp 2 fun b => u b
  have hmean' : ∑ b ∈ (torusBox d N).attach, u b = 0 := by
    rw [Finset.sum_attach (torusBox d N) u]
    exact hmean
  have hmem : uE ∈ (LinearMap.ker (torusLaplacian (d := d) N hN))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    obtain ⟨c, hc⟩ := exists_forall_eq_of_torusLaplacian_eq_zero N hN k hk
    simp [PiLp.inner_apply, uE, hc, ← Finset.sum_mul, hmean']
  rw [LinearMap.orthogonal_ker, (isSymmetric_torusLaplacian N hN).adjoint_eq] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hw := isTorusPeriodic_torusExtend N hN f.ofLp
  refine ⟨torusExtend N hN f.ofLp, hw, fun x => ?_⟩
  rw [← isTorusPeriodic_apply_torusReduce N _ (isTorusPeriodic_latticeLaplacian N _ hw) x,
    ← isTorusPeriodic_apply_torusReduce N u hu x]
  have := torusLaplacian_apply N hN f ⟨torusReduce N x, torusReduce_mem_torusBox N hN x⟩
  rw [hf] at this
  exact this.symm

end LatticeHC

end
