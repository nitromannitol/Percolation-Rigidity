/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/UnitTerm.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Analysis.CauchySchwarz
import Rigidity.Vendor.LHCH.Support.WeakNorm.BlockOscGrad
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusCalculus
import Rigidity.Vendor.LHCH.Support.WeakNorm.UnitScale

/-!
# The unit-scale term of the multiscale duality for a gradient

On each unit cell the term `cubeAvg(∇w·G) − (∇w)·(G)` is a sum over directions of face-weighted
covariances, bounded by Cauchy–Schwarz and the discrete Poincaré inequality on the cell; averaging
over the cells with an overlap count gives `C(d)` times the root mean squares of the second
differences of `w` and of `G`.
-/

open LatticeProb Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- **The covariance of two functions for a weighted average**: for weights `a ≥ 0` with sum one,
the weighted average of `f h` minus the product of the weighted averages of `f` and of `h` is at
most twice the root of the weighted average of `(f − g)²` (for any constant `g`) times the root of
the weighted average of `h²`. -/
theorem abs_sum_mul_mul_sub_mul_le {α : Type*} (s : Finset α) (a f h : α → ℝ) (g : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (h1 : ∑ i ∈ s, a i = 1) :
    |∑ i ∈ s, a i * (f i * h i) - (∑ i ∈ s, a i * f i) * ∑ i ∈ s, a i * h i| ≤
      2 * (Real.sqrt (∑ i ∈ s, a i * (f i - g) ^ 2) * Real.sqrt (∑ i ∈ s, a i * h i ^ 2)) := by
  set V := ∑ i ∈ s, a i * (f i - g) ^ 2 with hV
  set H := ∑ i ∈ s, a i * h i ^ 2 with hH
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)
  have e1 : ∑ i ∈ s, a i * (f i * h i) - (∑ i ∈ s, a i * f i) * ∑ i ∈ s, a i * h i =
      ∑ i ∈ s, a i * ((f i - g) * h i) - (∑ i ∈ s, a i * (f i - g)) * ∑ i ∈ s, a i * h i := by
    have e2 : ∑ i ∈ s, a i * ((f i - g) * h i) =
        ∑ i ∈ s, a i * (f i * h i) - g * ∑ i ∈ s, a i * h i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∑ i ∈ s, a i * (f i - g) = ∑ i ∈ s, a i * f i - g := by
      have : ∑ i ∈ s, a i * (f i - g) = ∑ i ∈ s, a i * f i - g * ∑ i ∈ s, a i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, h1, mul_one]
    rw [e2, e3]
    ring
  rw [e1]
  have c1 : |∑ i ∈ s, a i * ((f i - g) * h i)| ≤ Real.sqrt V * Real.sqrt H := by
    rw [← Real.sqrt_mul hV0]
    exact Real.abs_le_sqrt (sq_sum_mul_mul_le s a (fun i => f i - g) h ha)
  have c2 : |∑ i ∈ s, a i * (f i - g)| ≤ Real.sqrt V := by
    refine Real.abs_le_sqrt ?_
    exact sq_sum_mul_le_sum_mul_sq s a (fun i => f i - g) ha h1
  have c3 : |∑ i ∈ s, a i * h i| ≤ Real.sqrt H := by
    refine Real.abs_le_sqrt ?_
    exact sq_sum_mul_le_sum_mul_sq s a h ha h1
  calc _ ≤ |∑ i ∈ s, a i * ((f i - g) * h i)| +
        |(∑ i ∈ s, a i * (f i - g)) * ∑ i ∈ s, a i * h i| := abs_sub _ _
    _ ≤ Real.sqrt V * Real.sqrt H + Real.sqrt V * Real.sqrt H := by
        rw [abs_mul]
        exact add_le_add c1 (mul_le_mul c2 c3 (abs_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- The face-weighted sum over the edges of a cube in direction `j` of the squared deviations of
`∇w` from a constant `g` is at most the sum over the vertices of the cube of the squared deviations
of `w(x + e_j) − w(x)` from `g`. -/
theorem sum_faceWeight_mul_sq_grad_sub_le (z : Site d) (L : ℕ) (w : Site d → ℝ) (j : Fin d)
    (g : ℝ) :
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        faceWeight z L e * (w e.tgt - w e.src - g) ^ 2 ≤
      ∑ x ∈ latticeCube z L, (w (x + unit j) - w x - g) ^ 2 := by
  have hw : ∀ e : Edge d, 0 ≤ faceWeight z L e := fun e => by unfold faceWeight; positivity
  calc ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        faceWeight z L e * (w e.tgt - w e.src - g) ^ 2
      ≤ ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), (w e.tgt - w e.src - g) ^ 2 := by
        refine Finset.sum_le_sum fun e _ => ?_
        exact mul_le_of_le_one_left (sq_nonneg _) (faceWeight_le_one z L e)
    _ = ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          (w (e.1 + unit j) - w e.1 - g) ^ 2 := by
        refine Finset.sum_congr rfl fun e he => ?_
        have h2 : e.2 = j := (Finset.mem_filter.1 he).2
        simp only [Edge.tgt, Edge.src, h2]
    _ ≤ _ := by
        have hinj : Set.InjOn Prod.fst (((edgesOf z L).filter (fun e => e.2 = j) : Finset _) :
            Set (Edge d)) := by
          intro e he e' he' h
          have h1 : e.2 = j := (Finset.mem_filter.1 he).2
          have h2 : e'.2 = j := (Finset.mem_filter.1 he').2
          exact Prod.ext h (h1.trans h2.symm)
        rw [← Finset.sum_image (f := fun x => (w (x + unit j) - w x - g) ^ 2) hinj]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        intro x hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
        have := (Finset.mem_filter.1 he).1
        simp only [edgesOf, Finset.mem_filter, Finset.mem_product] at this
        exact this.1.1

/-- **The covariance on a unit cell in one direction**: there is `C(d)` such that for every unit
cube, every direction `j`, the face-weighted average over the edges in direction `j` of `∇w · G`
minus the product of the face-weighted averages of `∇w` and of `G` is at most twice the root of
`C` times the sum over the vertices of the squared second differences `∇_i∇_j w`, times the root of
the face-weighted average of `G²`. -/
theorem exists_abs_unit_cell_cov_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Site d) (w : Site d → ℝ) (G : Edge d → ℝ) (j : Fin d),
      |∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j),
          faceWeight z 1 e * ((w e.tgt - w e.src) * G e) -
        (∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j), faceWeight z 1 e * (w e.tgt - w e.src)) *
          ∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j), faceWeight z 1 e * G e| ≤
        2 * (Real.sqrt (C * ∑ x ∈ latticeCube z 1, ∑ i : Fin d, secondDiff w i j x ^ 2) *
          Real.sqrt (∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j),
            faceWeight z 1 e * G e ^ 2)) := by
  obtain ⟨C, hC, hP⟩ := exists_sum_sq_grad_sub_avg_le (d := d)
  refine ⟨C, hC, fun z w G j => ?_⟩
  have hw : ∀ e : Edge d, 0 ≤ faceWeight z 1 e := fun e => by unfold faceWeight; positivity
  have h1 : ∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j), faceWeight z 1 e = 1 := by
    simpa using sum_faceWeight_eq z (le_refl 1) j
  refine (abs_sum_mul_mul_sub_mul_le ((edgesOf z 1).filter (fun e => e.2 = j)) (faceWeight z 1)
    (fun e => w e.tgt - w e.src) G (((latticeCube z 1).card : ℝ)⁻¹ *
      ∑ y ∈ latticeCube z 1, (w (y + unit j) - w y)) (fun e _ => hw e) h1).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_)
    (Real.sqrt_nonneg _)) (by norm_num)
  refine (sum_faceWeight_mul_sq_grad_sub_le z 1 w j _).trans ?_
  have := hP z 1 w j
  simpa using this

/-- A site lies in the unit cube with corner `y ∈ ℕ^d` exactly when each coordinate lies between
that of `y` and that of `y` plus one. -/
theorem mem_latticeCube_triadicCorner_zero_iff (x : Site d) (y : Fin d → ℕ) :
    x ∈ latticeCube (triadicCorner 0 0 y) 1 ↔ ∀ i, (y i : ℤ) ≤ x i ∧ x i ≤ (y i : ℤ) + 1 := by
  have := mem_latticeCube_triadicCorner_iff 0 x 0 y
  simpa using this

/-- The unit cubes with corner in `{0, …, 3^n − 1}^d` lie in `{0, …, 3^n}^d`. -/
theorem latticeCube_triadicCorner_zero_subset_triadicCube {n : ℕ} {y : Fin d → ℕ}
    (hy : y ∈ triadicIndex d n) :
    latticeCube (triadicCorner 0 0 y) 1 ⊆ latticeCube 0 (3 ^ n) := by
  intro x hx
  rw [mem_latticeCube_triadicCorner_zero_iff] at hx
  rw [mem_latticeCube_iff_coord]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hyi : (y i : ℤ) + 1 ≤ ((3 ^ n : ℕ) : ℤ) := by
    have := mem_triadicIndex.1 hy i
    omega
  have hy0 : (0 : ℤ) ≤ y i := Nat.cast_nonneg _
  simp only [Pi.zero_apply, zero_add]
  constructor <;> omega

/-- Every site lies in at most `2^d` of the unit cubes with corner in `{0, …, 3^n − 1}^d`: in each
coordinate at most two values of `y_i` are possible. -/
theorem card_filter_mem_latticeCube_triadicCorner_zero_le (n : ℕ) (x : Site d) :
    ((triadicIndex d n).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 0 y) 1)).card ≤ 2 ^ d := by
  classical
  have hsub : (triadicIndex d n).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 0 y) 1) ⊆
      Fintype.piFinset (fun i : Fin d => (Finset.range (3 ^ n)).filter
        (fun t : ℕ => ((1 : ℕ) : ℤ) * t ≤ x i ∧ x i ≤ ((1 : ℕ) : ℤ) * t + ((1 : ℕ) : ℤ))) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    rw [mem_latticeCube_triadicCorner_zero_iff] at hy2
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨h1, h2⟩ := hy2 i
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (mem_triadicIndex.1 hy1 i), ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_pow_card _ _ 2 fun i _ => ?_).trans ?_
  · exact card_filter_mul_le_le_two 1 one_pos _ _
  · simp

/-- **Overlap of the unit cubes**: summing a nonnegative function over each unit cube with corner
in `{0, …, 3^n − 1}^d` and then over the cubes costs at most a factor `2^d` over the sum over
`{0, …, 3^n}^d`. -/
theorem sum_sum_latticeCube_triadicCorner_zero_le (n : ℕ) (T : Site d → ℝ)
    (hT : ∀ x, 0 ≤ T x) :
    ∑ y ∈ triadicIndex d n, ∑ x ∈ latticeCube (triadicCorner 0 0 y) 1, T x ≤
      2 ^ d * ∑ x ∈ latticeCube 0 (3 ^ n), T x := by
  classical
  have h1 : ∀ y ∈ triadicIndex d n,
      ∑ x ∈ latticeCube (triadicCorner 0 0 y) 1, T x =
        ∑ x ∈ latticeCube 0 (3 ^ n),
          if x ∈ latticeCube (triadicCorner 0 0 y) 1 then T x else 0 := by
    intro y hy
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2
      (latticeCube_triadicCorner_zero_subset_triadicCube hy)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h2 : ∑ y ∈ triadicIndex d n,
      (if x ∈ latticeCube (triadicCorner 0 0 y) 1 then T x else 0) =
      (((triadicIndex d n).filter
        (fun y => x ∈ latticeCube (triadicCorner 0 0 y) 1)).card : ℝ) * T x := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  have hc : ((((triadicIndex d n).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 0 y) 1)).card : ℕ) : ℝ) ≤ 2 ^ d := by
    exact_mod_cast card_filter_mem_latticeCube_triadicCorner_zero_le n x
  exact mul_le_mul_of_nonneg_right hc (hT x)

/-- **The unit-cell term is the sum of the covariances in each direction**: on a unit cube,
`cubeAvg(∇w·G) − (∇w)·(G)` is the sum over the directions `j` of the face-weighted covariance of
`∇w` and `G` over the edges in direction `j`. -/
theorem unit_cell_term_eq_sum_cov (z : Site d) (w : Site d → ℝ) (G : Edge d → ℝ) :
    cubeAvg z 1 (fun e => (w e.tgt - w e.src) * G e) -
        blockMean z 1 (fun e => w e.tgt - w e.src) ⬝ᵥ blockMean z 1 G =
      ∑ j : Fin d, (∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j),
          faceWeight z 1 e * ((w e.tgt - w e.src) * G e) -
        (∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j), faceWeight z 1 e * (w e.tgt - w e.src)) *
          ∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j), faceWeight z 1 e * G e) := by
  rw [Finset.sum_sub_distrib]
  simp only [cubeAvg, blockMean, dotProduct, Nat.cast_one, one_pow, inv_one, one_mul]
  rw [Finset.sum_fiberwise (edgesOf z 1) (fun e => e.2)
    (fun e => faceWeight z 1 e * ((w e.tgt - w e.src) * G e))]

/-- The face-weighted average of a function on a unit cube is the sum over the directions of the
face-weighted sums over the edges in each direction. -/
theorem cubeAvg_one_eq_sum_dir (z : Site d) (f : Edge d → ℝ) :
    cubeAvg z 1 f = ∑ j : Fin d, ∑ e ∈ (edgesOf z 1).filter (fun e => e.2 = j),
      faceWeight z 1 e * f e := by
  simp only [cubeAvg, Nat.cast_one, one_pow, inv_one, one_mul]
  rw [Finset.sum_fiberwise (edgesOf z 1) (fun e => e.2) (fun e => faceWeight z 1 e * f e)]

/-- **The unit-scale term of the multiscale duality for a gradient**: there is
`C(d)` such that for every `w` and every edge field `G`, the average over the unit cells of `□_n` of
`cubeAvg(∇w·G) − (∇w)·(G)` is at most `C` times the root mean square of the second differences of
`w` over `□_n` times the root mean square of `G` (on a unit cell each direction's edges carry equal
face weights, the covariance of `∇w` and `G` is bounded by Cauchy–Schwarz, and the spread of
`∇_j w` over parallel edges of a cell is a sum of second differences). -/
theorem exists_abs_unit_term_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : Site d → ℝ) (G : Edge d → ℝ),
      |((triadicIndex d n).card : ℝ)⁻¹ * ∑ y ∈ triadicIndex d n,
          (cubeAvg (triadicCorner 0 0 y) 1 (fun e => (w e.tgt - w e.src) * G e) -
            blockMean (triadicCorner 0 0 y) 1 (fun e => w e.tgt - w e.src) ⬝ᵥ
              blockMean (triadicCorner 0 0 y) 1 G)| ≤
        C * Real.sqrt ((((3 : ℝ) ^ n) ^ d)⁻¹ *
            ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2) *
          Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => G e ^ 2)) := by
  obtain ⟨C0, hC0, hcell⟩ := exists_abs_unit_cell_cov_le (d := d)
  refine ⟨2 * Real.sqrt (C0 * 2 ^ d), by positivity, fun n w G => ?_⟩
  have hcard : ((triadicIndex d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := by
    rw [card_triadicIndex_eq_pow]
    push_cast
    rfl
  have hNpos : (0 : ℝ) < ((triadicIndex d n).card : ℝ) := by
    rw [hcard]
    positivity
  set N : ℝ := ((triadicIndex d n).card : ℝ) with hN
  set T : Site d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 with hT
  have hT0 : ∀ x, 0 ≤ T x := fun x =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set P : (Fin d → ℕ) × Fin d → ℝ := fun p => C0 *
    ∑ x ∈ latticeCube (triadicCorner 0 0 p.1) 1, ∑ i : Fin d, secondDiff w i p.2 x ^ 2 with hP
  set Q : (Fin d → ℕ) × Fin d → ℝ := fun p =>
    ∑ e ∈ (edgesOf (triadicCorner 0 0 p.1) 1).filter (fun e => e.2 = p.2),
      faceWeight (triadicCorner 0 0 p.1) 1 e * G e ^ 2 with hQ
  have hP0 : ∀ p, 0 ≤ P p := fun p =>
    mul_nonneg hC0 (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hQ0 : ∀ p, 0 ≤ Q p := fun p => Finset.sum_nonneg fun e _ =>
    mul_nonneg (by unfold faceWeight; positivity) (sq_nonneg _)
  -- the bound for one cell
  have hone : ∀ y : Fin d → ℕ,
      |cubeAvg (triadicCorner 0 0 y) 1 (fun e => (w e.tgt - w e.src) * G e) -
          blockMean (triadicCorner 0 0 y) 1 (fun e => w e.tgt - w e.src) ⬝ᵥ
            blockMean (triadicCorner 0 0 y) 1 G| ≤
        ∑ j : Fin d, 2 * (Real.sqrt (P (y, j)) * Real.sqrt (Q (y, j))) := by
    intro y
    rw [unit_cell_term_eq_sum_cov]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => hcell (triadicCorner 0 0 y) w G j)
  -- the sums of `P` and `Q`
  have hPsum : ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), P p ≤
      C0 * 2 ^ d * ∑ x ∈ latticeCube 0 (3 ^ n), T x := by
    rw [Finset.sum_product]
    have e1 : ∀ y : Fin d → ℕ, ∑ j : Fin d, P (y, j) =
        C0 * ∑ x ∈ latticeCube (triadicCorner 0 0 y) 1, T x := by
      intro y
      simp only [hP, hT]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl fun y _ => e1 y, ← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left (sum_sum_latticeCube_triadicCorner_zero_le n T hT0) hC0
  have hQsum : ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), Q p =
      N * cubeAvg 0 (3 ^ n) (fun e => G e ^ 2) := by
    rw [Finset.sum_product, cubeAvg_eq_avg_unit, ← hN, mul_inv_cancel_left₀ hNpos.ne']
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [cubeAvg_one_eq_sum_dir]
  have hQavg : 0 ≤ cubeAvg 0 (3 ^ n) (fun e => G e ^ 2) := by
    rw [cubeAvg_eq_avg_unit]
    refine mul_nonneg (inv_nonneg.2 hNpos.le) (Finset.sum_nonneg fun y _ => ?_)
    rw [cubeAvg_one_eq_sum_dir]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun e _ =>
      mul_nonneg (by unfold faceWeight; positivity) (sq_nonneg _)
  have hN0 : 0 ≤ N⁻¹ := inv_nonneg.2 hNpos.le
  have hsqN : Real.sqrt N⁻¹ * Real.sqrt N⁻¹ = N⁻¹ := Real.mul_self_sqrt hN0
  have step1 : |N⁻¹ * ∑ y ∈ triadicIndex d n,
        (cubeAvg (triadicCorner 0 0 y) 1 (fun e => (w e.tgt - w e.src) * G e) -
          blockMean (triadicCorner 0 0 y) 1 (fun e => w e.tgt - w e.src) ⬝ᵥ
            blockMean (triadicCorner 0 0 y) 1 G)| ≤
      2 * (Real.sqrt (N⁻¹ * ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), P p) *
        Real.sqrt (N⁻¹ * ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), Q p)) := by
    calc _ = N⁻¹ * |∑ y ∈ triadicIndex d n,
          (cubeAvg (triadicCorner 0 0 y) 1 (fun e => (w e.tgt - w e.src) * G e) -
            blockMean (triadicCorner 0 0 y) 1 (fun e => w e.tgt - w e.src) ⬝ᵥ
              blockMean (triadicCorner 0 0 y) 1 G)| := by
          rw [abs_mul, abs_of_nonneg hN0]
      _ ≤ N⁻¹ * ∑ y ∈ triadicIndex d n, ∑ j : Fin d,
            2 * (Real.sqrt (P (y, j)) * Real.sqrt (Q (y, j))) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun y _ => hone y)) hN0
      _ = N⁻¹ * (2 * ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)),
            Real.sqrt (P p) * Real.sqrt (Q p)) := by
          rw [Finset.sum_product]
          simp only [← Finset.mul_sum]
      _ ≤ N⁻¹ * (2 * (Real.sqrt (∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), P p) *
            Real.sqrt (∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), Q p))) := by
          refine mul_le_mul_of_nonneg_left ?_ hN0
          exact mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _ hP0 hQ0) (by norm_num)
      _ = _ := by
          rw [Real.sqrt_mul hN0, Real.sqrt_mul hN0]
          linear_combination (-2 * Real.sqrt (∑ p ∈ triadicIndex d n ×ˢ
            (Finset.univ : Finset (Fin d)), P p) * Real.sqrt (∑ p ∈ triadicIndex d n ×ˢ
            (Finset.univ : Finset (Fin d)), Q p)) * hsqN
  refine step1.trans ?_
  have hA : N⁻¹ * ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), P p ≤
      C0 * 2 ^ d * (N⁻¹ * ∑ x ∈ latticeCube 0 (3 ^ n), T x) := by
    calc _ ≤ N⁻¹ * (C0 * 2 ^ d * ∑ x ∈ latticeCube 0 (3 ^ n), T x) :=
          mul_le_mul_of_nonneg_left hPsum hN0
      _ = _ := by ring
  have hB : N⁻¹ * ∑ p ∈ triadicIndex d n ×ˢ (Finset.univ : Finset (Fin d)), Q p =
      cubeAvg 0 (3 ^ n) (fun e => G e ^ 2) := by
    rw [hQsum, inv_mul_cancel_left₀ hNpos.ne']
  rw [hB, ← hcard]
  have hA' := Real.sqrt_le_sqrt hA
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ C0 * 2 ^ d by positivity)] at hA'
  calc _ ≤ 2 * (Real.sqrt (C0 * 2 ^ d) * Real.sqrt (N⁻¹ * ∑ x ∈ latticeCube 0 (3 ^ n), T x) *
        Real.sqrt (cubeAvg 0 (3 ^ n) (fun e => G e ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg _))
          (by norm_num)
    _ = _ := by ring

end LatticeHC

end
