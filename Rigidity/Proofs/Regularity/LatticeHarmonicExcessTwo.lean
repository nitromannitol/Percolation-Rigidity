import Rigidity.Proofs.Regularity.LatticeHarmonicExcess

/-!
# Second-order approximation of lattice harmonic functions

Ingredients of the excess decay of order two (`HarmonicRegularity` with `j = 2`) of lattice
harmonic functions on the balls of the lattice: forward differences commute
(`fwd_comm`), the second forward differences of the quadratic form
`Q₀(y) = ½ q_H(y - c)` are the constants `(H_{ab} + H_{ba}) / 2` (`fwd_fwd_halfQuad`), and the
third forward differences of a harmonic function are bounded on a box by its square sum on a
larger box (`sq_fwd_fwd_fwd_le`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

theorem fwd_comm (a b : Fin d) (f : (Fin d → ℤ) → ℝ) : fwd a (fwd b f) = fwd b (fwd a f) := by
  funext y
  simp only [fwd]
  rw [add_right_comm y (unit a) (unit b)]
  ring

theorem latticeEuclideanEmbedding_unit (i : Fin d) :
    latticeEuclideanEmbedding (unit i) = EuclideanSpace.single i 1 := by
  ext j
  change ((Pi.single i 1 : Fin d → ℤ) j : ℝ) = (EuclideanSpace.single i (1 : ℝ)) j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem quadPolar_add_left (M : Matrix (Fin d) (Fin d) ℝ) (u u' v : EuclideanSpace ℝ (Fin d)) :
    quadPolar M (u + u') v = quadPolar M u v + quadPolar M u' v := by
  rw [quadPolar_eq_inner, quadPolar_eq_inner, quadPolar_eq_inner, inner_add_left]

/-- Second forward differences of `½ q_H(y - c)`. -/
theorem fwd_fwd_halfQuad (H : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℤ) (a b : Fin d)
    (y : Fin d → ℤ) :
    fwd a (fwd b (fun x => quadForm H (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c)
      / 2)) y = symEntry H a b := by
  simp only [fwd]
  have hshift : ∀ (x : Fin d → ℤ) (i : Fin d), latticeEuclideanEmbedding (x + unit i) -
      latticeEuclideanEmbedding c = (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) +
        EuclideanSpace.single i 1 := by
    intro x i
    rw [latticeEuclideanEmbedding_add, latticeEuclideanEmbedding_unit]; abel
  simp only [hshift, quadForm_add, quadPolar_add_left]
  rw [quadPolar_single]
  ring

/-- **Third differences of lattice harmonic functions.** -/
theorem sq_fwd_fwd_fwd_le (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {m : ℕ} (hm : 0 < m)
    (hf : ∀ x ∈ supBox z (4 * (4 * (4 ^ d * (2 * m)) + 4) + 5), latticeLaplacian f x = 0)
    (a b e : Fin d) {x₀ : Fin d → ℤ} (hx₀ : x₀ ∈ supBox z m) :
    fwd e (fwd a (fwd b f)) x₀ ^ 2 ≤
      secondDiffCoeff d m * (16 * d / ((4 * (4 ^ d * (2 * m)) + 6 : ℕ) : ℝ) ^ 2 *
        ∑ x ∈ supBox z (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2), f x ^ 2) := by
  set ρ := 4 ^ d * (2 * m) with hρ
  set L := 4 * ρ + 6 with hL
  have hL0 : 0 < L := by omega
  have hfe : ∀ x ∈ supBox z (4 * ρ + 4), latticeLaplacian (fwd e f) x = 0 :=
    latticeLaplacian_fwd_eq_zero (fun x hx => hf x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) e
  have h1 := sq_fwd_fwd_le (fwd e f) z hm (by rw [← hρ]; exact hfe) a b hx₀
  have hcomm : fwd e (fwd a (fwd b f)) = fwd a (fwd b (fwd e f)) := by
    rw [fwd_comm e a, fwd_comm e b]
  rw [hcomm]
  refine h1.trans ?_
  rw [secondDiffCoeff]
  have e2 : 2 * (2 * ρ + 2) + 2 = L := by rw [hL]; ring
  rw [← hρ, e2]
  have h2 := sum_sq_fwd_le f z hL0 (fun x hx => hf x (by
    rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) e
  have hc : 0 ≤ 4 ^ d * (64 * (d : ℝ)) ^ d / ((m : ℝ) + 1) ^ d *
      (16 * d / ((ρ : ℕ) : ℝ) ^ 2 * (16 * d / ((2 * ρ + 2 : ℕ) : ℝ) ^ 2)) := by positivity
  calc 4 ^ d * (64 * (d : ℝ)) ^ d / ((m : ℝ) + 1) ^ d *
        (16 * d / ((ρ : ℕ) : ℝ) ^ 2 * (16 * d / ((2 * ρ + 2 : ℕ) : ℝ) ^ 2 *
          ∑ x ∈ supBox z L, fwd e f x ^ 2))
      = 4 ^ d * (64 * (d : ℝ)) ^ d / ((m : ℝ) + 1) ^ d *
          (16 * d / ((ρ : ℕ) : ℝ) ^ 2 * (16 * d / ((2 * ρ + 2 : ℕ) : ℝ) ^ 2)) *
          ∑ x ∈ supBox z L, fwd e f x ^ 2 := by ring
    _ ≤ 4 ^ d * (64 * (d : ℝ)) ^ d / ((m : ℝ) + 1) ^ d *
          (16 * d / ((ρ : ℕ) : ℝ) ^ 2 * (16 * d / ((2 * ρ + 2 : ℕ) : ℝ) ^ 2)) *
          (16 * d / (L : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * L + 2), f x ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by push_cast; ring

theorem fwd_sub (i : Fin d) (f g : (Fin d → ℤ) → ℝ) :
    fwd i (fun y => f y - g y) = fun y => fwd i f y - fwd i g y := by
  funext y; simp only [fwd]; ring

/-- The Hessian `H_{ij} = D_i D_j f(c)` of second forward differences at `c`. -/
def hessAt (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fwd i (fwd j f) c

/-- The quadratic part `Q₀(y) = ½ q_H(y - c)` of the second-order expansion at `c`. -/
noncomputable def halfQuad (H : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℤ) (y : Fin d → ℤ) : ℝ :=
  quadForm H (latticeEuclideanEmbedding y - latticeEuclideanEmbedding c) / 2

theorem symEntry_hessAt (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (a b : Fin d) :
    symEntry (hessAt f c) a b = fwd a (fwd b f) c := by
  simp only [symEntry, hessAt]
  rw [fwd_comm b a]; ring

/-- **Second-order Taylor expansion on the lattice**: with `g = f - Q₀`,
`|f(x) - (Q₀(x) + g(c) + ∑ᵢ (xᵢ - cᵢ) D_i g(c))| ≤ d (d + 1) s² · d s M₃` when the third forward
differences are bounded by `M₃` on the box `[c, x]`. -/
theorem abs_sub_taylor_two_le (f : (Fin d → ℤ) → ℝ) {c x : Fin d → ℤ} (hcx : ∀ i, c i ≤ x i)
    {s : ℕ} (hs : ∀ i, x i - c i ≤ s) {M₃ : ℝ} (hM₀ : 0 ≤ M₃)
    (hM : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) →
      ∀ a b e, |fwd e (fwd a (fwd b f)) y| ≤ M₃) :
    |f x - (halfQuad (hessAt f c) c x + (f c - halfQuad (hessAt f c) c c) +
        ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i (fun y => f y - halfQuad (hessAt f c) c y) c)| ≤
      d * (d + 1) * s ^ 2 * (d * s * M₃) := by
  set Q₀ := halfQuad (hessAt f c) c with hQ₀
  set g : (Fin d → ℤ) → ℝ := fun y => f y - Q₀ y with hg
  have hMg : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) → ∀ a b,
      |fwd a (fwd b g) y| ≤ d * s * M₃ := by
    intro y hy a b
    have e1 : fwd a (fwd b g) y = fwd a (fwd b f) y - fwd a (fwd b Q₀) y := by
      rw [hg, fwd_sub, fwd_sub]
    have e2 : fwd a (fwd b Q₀) y = fwd a (fwd b f) c := by
      rw [hQ₀]
      exact (fwd_fwd_halfQuad (hessAt f c) c a b y).trans (symEntry_hessAt f c a b)
    rw [e1, e2]
    have hcy : ∀ i, c i ≤ y i := fun i => (hy i).1
    have hsy : ∀ i, y i - c i ≤ s := fun i => by have := (hy i).2; have := hs i; omega
    have h := abs_cornerPoint_sub_le (fwd a (fwd b f)) hcy hsy hM₀
      (fun y' hy' i => hM y' (fun j => ⟨(hy' j).1, (hy' j).2.trans (hy j).2⟩) a b i) univ
    rw [cornerPoint_univ, card_univ, Fintype.card_fin] at h
    exact h
  have hdM : 0 ≤ (d : ℝ) * s * M₃ := by positivity
  have := abs_sub_taylor_le g hcx hs hdM hMg
  have e3 : f x - (Q₀ x + (f c - Q₀ c) + ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i g c) =
      g x - g c - ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i g c := by
    simp only [hg]; ring
  rw [e3]
  exact this

theorem latticeEuclideanEmbedding_sub_unit (x : Fin d → ℤ) (i : Fin d) :
    latticeEuclideanEmbedding (x - unit i) =
      latticeEuclideanEmbedding x - EuclideanSpace.single i 1 := by
  rw [latticeEuclideanEmbedding_sub, latticeEuclideanEmbedding_unit]

/-- The lattice Laplacian of `½ q_H(y - c)` is the trace of `H`. -/
theorem latticeLaplacian_halfQuad (H : Matrix (Fin d) (Fin d) ℝ) (c x : Fin d → ℤ) :
    latticeLaplacian (halfQuad H c) x = ∑ a, H a a := by
  simp only [latticeLaplacian, halfQuad]
  refine sum_congr rfl fun a _ => ?_
  have h1 : latticeEuclideanEmbedding (x + unit a) - latticeEuclideanEmbedding c =
      (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) + EuclideanSpace.single a 1 := by
    rw [latticeEuclideanEmbedding_add, latticeEuclideanEmbedding_unit]; abel
  have h2 : latticeEuclideanEmbedding (x - unit a) - latticeEuclideanEmbedding c =
      (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) - EuclideanSpace.single a 1 := by
    rw [latticeEuclideanEmbedding_sub_unit]; abel
  rw [h1, h2]
  have := quadForm_add_add_sub H (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c)
    (EuclideanSpace.single a 1)
  rw [quadForm_single] at this
  linarith

theorem quadForm_smul_matrix (t : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm (t • H) v = t * quadForm H v := by
  simp only [quadForm, Matrix.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- `½ q_H(y - c)` is a quadratic function. -/
theorem halfQuad_mem_clusterQuadratic [NeZero d] (H : Matrix (Fin d) (Fin d) ℝ)
    (c : Fin d → ℤ) :
    (fun x : latticeComponent d => halfQuad H c x.val) ∈ clusterQuadratic (latticeComponent d) := by
  set C := latticeEuclideanEmbedding c
  refine ⟨(inner ℝ C (polarVec H C) - quadForm H C) / 2, (-(1 / 2 : ℝ)) • polarVec H C,
    (1 / 2 : ℝ) • H, fun x => ?_⟩
  simp only [halfQuad]
  have h1 := quadForm_eq_sub H (latticeEuclideanEmbedding x.val) C
  rw [inner_sub_left] at h1
  have hcomm : inner ℝ (polarVec H C) (latticeEuclideanEmbedding x.val) =
      inner ℝ (latticeEuclideanEmbedding x.val) (polarVec H C) := real_inner_comm _ _
  rw [quadForm_smul_matrix, real_inner_smul_left, hcomm]
  linarith

theorem latticeLaplacian_add (f g : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => f y + g y) x = latticeLaplacian f x + latticeLaplacian g x := by
  simp only [latticeLaplacian, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem latticeLaplacian_neg (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fun y => -f y) x = -latticeLaplacian f x := by
  simp only [latticeLaplacian, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem mem_latticeComponent_supp [NeZero d] (y : Fin d → ℤ) : y ∈ (latticeComponent d).supp := by
  rw [latticeComponent_supp]; trivial

/-- A function on the lattice component as a function on `ℤ^d`. -/
def latticeExt [NeZero d] (v : latticeComponent d → ℝ) (y : Fin d → ℤ) : ℝ :=
  v ⟨y, mem_latticeComponent_supp y⟩

/-- The lattice harmonic quadratic functions, `Ā_2` on the lattice. -/
def latticeHarmonicQuadratic (d : ℕ) [NeZero d] : AddSubgroup (latticeComponent d → ℝ) where
  carrier := {v | v ∈ clusterQuadratic (latticeComponent d) ∧
    ∀ y : Fin d → ℤ, latticeLaplacian (latticeExt v) y = 0}
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨(clusterQuadratic _).add_mem hv hw, fun y => ?_⟩
    have e : latticeExt (v + w) = fun y => latticeExt v y + latticeExt w y := rfl
    rw [e, latticeLaplacian_add, hv' y, hw' y, add_zero]
  zero_mem' := ⟨(clusterQuadratic _).zero_mem, fun y => by
    simp [latticeExt, latticeLaplacian]⟩
  neg_mem' := by
    rintro v ⟨hv, hv'⟩
    refine ⟨(clusterQuadratic _).neg_mem hv, fun y => ?_⟩
    have e : latticeExt (-v) = fun y => -latticeExt v y := rfl
    rw [e, latticeLaplacian_neg, hv' y, neg_zero]

theorem latticeHarmonicQuadratic_le_clusterQuadratic [NeZero d] :
    latticeHarmonicQuadratic d ≤ clusterQuadratic (latticeComponent d) := fun _ hv => hv.1

theorem clusterAffine_le_latticeHarmonicQuadratic [NeZero d] :
    clusterAffine (latticeComponent d) ≤ latticeHarmonicQuadratic d := by
  rintro v ⟨a, p, hv⟩
  refine ⟨clusterAffine_le_clusterQuadratic _ ⟨a, p, hv⟩, fun y => ?_⟩
  have : latticeExt v = fun y => a + inner ℝ p (latticeEuclideanEmbedding y) := by
    funext y; simp only [latticeExt, hv]
  rw [this, latticeLaplacian_affine]

end Rigidity.Proofs.Regularity
