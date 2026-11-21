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

end Rigidity.Proofs.Regularity
