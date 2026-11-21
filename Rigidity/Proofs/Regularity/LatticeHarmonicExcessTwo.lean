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

theorem HarmonicRegularity.mono_const {F : Type*} [AddCommGroup F] {N : ℝ → AddGroupSeminorm F}
    {Abar : ℝ → Set F} {P : AddSubgroup F} {j : ℕ} {X R CH CH' : ℝ}
    (h : HarmonicRegularity N Abar P j X R CH) (hCH : CH ≤ CH') (hX : 0 < X) :
    HarmonicRegularity N Abar P j X R CH' := by
  intro r hrR v hv s hXs hsr
  have hs : 0 < s := hX.trans_le hXs
  have hr : 0 < r := by linarith
  refine (h r hrR v hv s hXs hsr).trans ?_
  apply mul_le_mul_of_nonneg_right _ (ballExcess_nonneg N P r v)
  exact mul_le_mul_of_nonneg_right hCH (by positivity)

/-- The trace of the second differences at `c` of a function harmonic at `c` is a sum of third
differences. -/
theorem sum_hessAt_eq (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) (hΔ : latticeLaplacian f c = 0) :
    ∑ a, hessAt f c a a = ∑ a, fwd a (fwd a (fwd a f)) (c - unit a) := by
  have e : ∀ a, fwd a (fwd a (fwd a f)) (c - unit a) =
      hessAt f c a a - (f (c + unit a) + f (c - unit a) - 2 * f c) := by
    intro a
    simp only [fwd, hessAt, sub_add_cancel]
    ring
  rw [sum_congr rfl fun a _ => e a, sum_sub_distrib]
  simp only [latticeLaplacian] at hΔ
  rw [hΔ, sub_zero]

/-- The trace-free part `H - (tr H / d) I` of the second differences at `c`. -/
noncomputable def harmHess (f : (Fin d → ℤ) → ℝ) (c : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  hessAt f c - Matrix.diagonal fun _ => (∑ a, hessAt f c a a) / d

theorem latticeLaplacian_halfQuad_harmHess (hd : 0 < d) (f : (Fin d → ℤ) → ℝ)
    (c x : Fin d → ℤ) : latticeLaplacian (halfQuad (harmHess f c) c) x = 0 := by
  rw [latticeLaplacian_halfQuad]
  simp only [harmHess, Matrix.sub_apply, Matrix.diagonal_apply_eq, sum_sub_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

theorem quadForm_sub_matrix (M M' : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm (M - M') v = quadForm M v - quadForm M' v := by
  simp only [quadForm, Matrix.sub_apply, sub_mul, sum_sub_distrib]

theorem quadForm_diagonal (t : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm (Matrix.diagonal fun _ => t) v = t * ∑ i, v i ^ 2 := by
  simp only [quadForm, Matrix.diagonal_apply, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true,
    mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- Removing the trace changes the quadratic part by at most `|t| d S²` on `[c, c + S 𝟙]`. -/
theorem abs_halfQuad_sub_le (H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) {c x : Fin d → ℤ}
    (hcx : ∀ i, c i ≤ x i) {S : ℕ} (hs : ∀ i, x i - c i ≤ S) :
    |halfQuad H c x - halfQuad (H - Matrix.diagonal fun _ => t) c x| ≤ |t| * (d * S ^ 2) := by
  simp only [halfQuad]
  rw [quadForm_sub_matrix, quadForm_diagonal]
  have hcomp : ∀ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i =
      ((x i - c i : ℤ) : ℝ) := fun i => by
    rw [← latticeEuclideanEmbedding_sub]; rfl
  have hsum : ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2 ≤
      d * S ^ 2 := by
    calc _ ≤ ∑ _i : Fin d, ((S : ℝ)) ^ 2 := by
          refine sum_le_sum fun i _ => ?_
          rw [hcomp]
          have h0 : (0 : ℝ) ≤ ((x i - c i : ℤ) : ℝ) := by
            have := hcx i; exact_mod_cast (by omega : (0 : ℤ) ≤ x i - c i)
          have h1 : ((x i - c i : ℤ) : ℝ) ≤ S := by exact_mod_cast hs i
          exact pow_le_pow_left₀ h0 h1 2
      _ = d * S ^ 2 := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum0 : 0 ≤ ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have e : quadForm H (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) / 2 -
      (quadForm H (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) -
        t * ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2) / 2 =
      (t * ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2) / 2 := by ring
  rw [e, abs_div, abs_mul, abs_of_nonneg hsum0, abs_two]
  have : |t| * ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2 ≤
      |t| * (d * S ^ 2) := mul_le_mul_of_nonneg_left hsum (abs_nonneg t)
  have h0 : 0 ≤ |t| * ∑ i, (latticeEuclideanEmbedding x - latticeEuclideanEmbedding c) i ^ 2 :=
    mul_nonneg (abs_nonneg t) hsum0
  linarith

/-- **Second-order harmonic Taylor expansion on the lattice**: the quadratic part is the trace-free
`½ q_{H'}(y - c)`, `H' = harmHess f c`, which is lattice harmonic. -/
theorem abs_sub_harmonicTaylor_two_le (hd : 0 < d) (f : (Fin d → ℤ) → ℝ) {c x : Fin d → ℤ}
    (hcx : ∀ i, c i ≤ x i) {S : ℕ} (hs : ∀ i, x i - c i ≤ S) {M₃ : ℝ} (hM₀ : 0 ≤ M₃)
    (hM : ∀ y : Fin d → ℤ, (∀ i, c i ≤ y i ∧ y i ≤ x i) →
      ∀ a b e, |fwd e (fwd a (fwd b f)) y| ≤ M₃)
    (hMc : ∀ a, |fwd a (fwd a (fwd a f)) (c - unit a)| ≤ M₃) (hΔ : latticeLaplacian f c = 0) :
    |f x - (halfQuad (harmHess f c) c x + (f c - halfQuad (hessAt f c) c c) +
        ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i (fun y => f y - halfQuad (hessAt f c) c y) c)| ≤
      d * (d + 1) * S ^ 2 * (d * S * M₃) + d * S ^ 2 * M₃ := by
  have h1 := abs_sub_taylor_two_le f hcx hs hM₀ hM
  have h2 := abs_halfQuad_sub_le (hessAt f c) ((∑ a, hessAt f c a a) / d) hcx hs (x := x)
  have htr : |(∑ a, hessAt f c a a) / d| ≤ M₃ := by
    rw [sum_hessAt_eq f c hΔ, abs_div, Nat.abs_cast]
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    rw [div_le_iff₀ hd']
    calc |∑ a, fwd a (fwd a (fwd a f)) (c - unit a)|
        ≤ ∑ a, |fwd a (fwd a (fwd a f)) (c - unit a)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin d, M₃ := sum_le_sum fun a _ => hMc a
      _ = M₃ * d := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h3 : |(∑ a, hessAt f c a a) / d| * (d * S ^ 2) ≤ d * S ^ 2 * M₃ := by
    have := mul_le_mul_of_nonneg_right htr (by positivity : (0 : ℝ) ≤ d * S ^ 2)
    linarith
  have e : harmHess f c = hessAt f c - Matrix.diagonal fun _ => (∑ a, hessAt f c a a) / d := rfl
  rw [e]
  set T := halfQuad (hessAt f c) c x + (f c - halfQuad (hessAt f c) c c) +
    ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i (fun y => f y - halfQuad (hessAt f c) c y) c with hT
  set D := halfQuad (hessAt f c) c x -
    halfQuad (hessAt f c - Matrix.diagonal fun _ => (∑ a, hessAt f c a a) / d) c x with hD
  have e2 : f x - (halfQuad (hessAt f c - Matrix.diagonal fun _ => (∑ a, hessAt f c a a) / d) c x +
      (f c - halfQuad (hessAt f c) c c) +
      ∑ i, ((x i - c i : ℤ) : ℝ) * fwd i (fun y => f y - halfQuad (hessAt f c) c y) c) =
      (f x - T) + D := by rw [hT, hD]; ring
  rw [e2]
  calc |(f x - T) + D| ≤ |f x - T| + |D| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (h2.trans h3)

/-- The coefficient of `sq_fwd_fwd_fwd_le` at the scale `m`. -/
noncomputable def thirdDiffCoeff (d m : ℕ) : ℝ :=
  secondDiffCoeff d m * (16 * d / ((4 * (4 ^ d * (2 * m)) + 6 : ℕ) : ℝ) ^ 2)

theorem thirdDiffCoeff_nonneg (d m : ℕ) : 0 ≤ thirdDiffCoeff d m := by
  have := secondDiffCoeff_nonneg d m
  unfold thirdDiffCoeff; positivity

theorem corner_mem_supBox (z : Fin d → ℤ) (n : ℕ) : (fun i => z i - n) ∈ supBox z n := by
  simp only [supBox, Fintype.mem_piFinset, mem_Icc]
  intro i; omega

theorem sub_unit_mem_supBox {z c : Fin d → ℤ} {n : ℕ} (hc : c ∈ supBox z n) (a : Fin d) :
    c - unit a ∈ supBox z (n + 1) := by
  rw [mem_supBox_iff_supDist_le] at hc ⊢
  have e : c - unit a = c + (-1 : ℤ) • unit a := by rw [neg_smul, one_smul, sub_eq_add_neg]
  rw [e]
  exact (supDist_add_unit_le c z a (-1) (by norm_num)).trans (by omega)

/-- **Excess decay of order two below the interior scale.** -/
theorem ballExcess_two_le_of_latticeHarmonic [NeZero d] (z : Vertex d) {r s : ℝ} {m : ℕ}
    (hm : 0 < m) (hbox : Real.sqrt d * ((4 * (4 * (4 ^ d * (2 * m)) + 4) + 5 : ℕ) : ℝ) < r)
    (hsm : s + 1 ≤ m) (hs1 : 1 ≤ s) {v : latticeComponent d → ℝ}
    (hv : v ∈ latticeHarmonicClass z r) {w : latticeComponent d → ℝ}
    (hw : w ∈ latticeHarmonicQuadratic d) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicQuadratic d) s v ≤
      d * ((d + 1) * d + 1) * (2 * s) ^ 3 * Real.sqrt (thirdDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨F, hvF, hF⟩ := hv
  have hW := hw.2
  set f : (Fin d → ℤ) → ℝ := fun y => F y - latticeExt w y with hfdef
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hf : ∀ x ∈ supBox z (4 * (4 * (4 ^ d * (2 * m)) + 4) + 5), latticeLaplacian f x = 0 := by
    intro x hx
    rw [hfdef, latticeLaplacian_sub, hW x, sub_zero]
    exact hF x ((dist_le_of_mem_supBox hx).trans_lt hbox)
  have hs0 : 0 ≤ s := by linarith
  set n := ⌊s⌋₊ with hn
  have hns : (n : ℝ) ≤ s := Nat.floor_le hs0
  have hnm : n + 1 ≤ m := by
    have : ((n + 1 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  set M := Real.sqrt (thirdDiffCoeff d m *
    ∑ y ∈ supBox z (2 * (4 * (4 ^ d * (2 * m)) + 6) + 2), f y ^ 2) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hM : ∀ y ∈ supBox z m, ∀ a b e, |fwd e (fwd a (fwd b f)) y| ≤ M := by
    intro y hy a b e
    apply Real.abs_le_sqrt
    have := sq_fwd_fwd_fwd_le f z hm hf a b e hy
    rw [thirdDiffCoeff, mul_assoc]
    exact this
  set c : Fin d → ℤ := fun i => z i - n with hc
  have hcn : c ∈ supBox z n := corner_mem_supBox z n
  have hρm : m ≤ 4 ^ d * (2 * m) := by
    have := Nat.one_le_pow d 4 (by norm_num); nlinarith
  have hΔc : latticeLaplacian f c = 0 := hf c (by
    rw [mem_supBox_iff_supDist_le] at hcn ⊢; omega)
  have hMc : ∀ a, |fwd a (fwd a (fwd a f)) (c - unit a)| ≤ M := fun a =>
    hM _ (by
      have := sub_unit_mem_supBox hcn a
      rw [mem_supBox_iff_supDist_le] at this ⊢; omega) a a a
  -- the harmonic quadratic and affine parts of the expansion at `c`
  set g : (Fin d → ℤ) → ℝ := fun y => f y - halfQuad (hessAt f c) c y with hg
  set q : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => fwd i g c with hq
  set α := (f c - halfQuad (hessAt f c) c c) - ∑ i, (c i : ℝ) * fwd i g c with hα
  have hQ : (fun x : latticeComponent d => halfQuad (harmHess f c) c x.val) ∈
      latticeHarmonicQuadratic d :=
    ⟨halfQuad_mem_clusterQuadratic (harmHess f c) c,
      fun y => latticeLaplacian_halfQuad_harmHess hd f c y⟩
  have hA : (fun x : latticeComponent d => α + inner ℝ q (latticeEuclideanEmbedding x.val)) ∈
      latticeHarmonicQuadratic d :=
    clusterAffine_le_latticeHarmonicQuadratic ⟨α, q, fun _ => rfl⟩
  have hsum := (latticeHarmonicQuadratic d).add_mem ((latticeHarmonicQuadratic d).add_mem hw hQ) hA
  refine (ballExcess_le _ _ hsum).trans ?_
  rw [componentBallSeminorm_apply]
  have hbound : 0 ≤ d * (d + 1) * ((2 * n : ℕ) : ℝ) ^ 2 * (d * ((2 * n : ℕ) : ℝ) * M) +
      d * ((2 * n : ℕ) : ℝ) ^ 2 * M := by positivity
  refine (componentBallL2_le_of_abs_le (latticeComponent d) z s hbound ?_).trans ?_
  · intro x hx
    have hxz := abs_sub_le_floor_of_mem_ball hx
    have hcx : ∀ i, c i ≤ x.val i := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; omega
    have hs2 : ∀ i, x.val i - c i ≤ (2 * n : ℕ) := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; push_cast; omega
    have htay := abs_sub_harmonicTaylor_two_le hd f hcx hs2 hM0 (fun y hy a b e => hM y (by
      rw [mem_supBox_iff_supDist_le]
      simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
      intro i
      have h1 := hy i
      have h2 := abs_le.1 (hxz i)
      simp only [hc] at h1
      rw [← hn] at h2
      omega) a b e) hMc hΔc
    have hinner : inner ℝ q (latticeEuclideanEmbedding x.val) =
        ∑ i, (x.val i : ℝ) * fwd i g c := by
      rw [inner_eq_sum]
      exact sum_congr rfl fun i _ => mul_comm _ _
    have hsplit : ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i g c =
        ∑ i, (x.val i : ℝ) * fwd i g c - ∑ i, (c i : ℝ) * fwd i g c := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by push_cast; ring
    have hfx : f x.val = F x.val - w x := rfl
    have hval : (v - (w + (fun x : latticeComponent d => halfQuad (harmHess f c) c x.val) +
        fun x : latticeComponent d => α + inner ℝ q (latticeEuclideanEmbedding x.val))) x =
        f x.val - (halfQuad (harmHess f c) c x.val + (f c - halfQuad (hessAt f c) c c) +
          ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i g c) := by
      show v x - (w x + halfQuad (harmHess f c) c x.val +
        (α + inner ℝ q (latticeEuclideanEmbedding x.val))) = _
      rw [hvF, hinner, hsplit, hfx, hα]
      ring
    rw [hval]
    exact htay
  · have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have ht : ((2 * n : ℕ) : ℝ) ≤ 2 * s := by push_cast; linarith
    have ht0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : ((2 * n : ℕ) : ℝ) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ ht0 ht 3
    have h2 : ((2 * n : ℕ) : ℝ) ^ 2 ≤ (2 * s) ^ 3 :=
      (pow_le_pow_left₀ ht0 ht 2).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
    have hle : d * (d + 1) * ((2 * n : ℕ) : ℝ) ^ 2 * (d * ((2 * n : ℕ) : ℝ) * M) +
        d * ((2 * n : ℕ) : ℝ) ^ 2 * M ≤ d * ((d + 1) * d + 1) * (2 * s) ^ 3 * M := by
      have e1 : d * (d + 1) * ((2 * n : ℕ) : ℝ) ^ 2 * (d * ((2 * n : ℕ) : ℝ) * M) +
          d * ((2 * n : ℕ) : ℝ) ^ 2 * M = (d * (d + 1) * d * M) * ((2 * n : ℕ) : ℝ) ^ 3 +
            (d * M) * ((2 * n : ℕ) : ℝ) ^ 2 := by ring
      have e2 : d * ((d + 1) * d + 1) * (2 * s) ^ 3 * M =
          (d * (d + 1) * d * M) * (2 * s) ^ 3 + (d * M) * (2 * s) ^ 3 := by ring
      rw [e1, e2]
      exact add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    have hMle : M ≤ Real.sqrt (thirdDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (thirdDiffCoeff_nonneg d m)
      rw [← sum_sq_eq_card_mul_componentBallL2_sq]
      have hL : Real.sqrt d * ((2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 : ℕ) : ℝ) < r := by
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hsd) hbox
        exact_mod_cast (by omega : 2 * (4 * (4 ^ d * (2 * m)) + 6) + 2 ≤
          4 * (4 * (4 ^ d * (2 * m)) + 4) + 5)
      have hball := sum_sq_supBox_le_ball z hL f
      refine hball.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
      rw [Pi.sub_apply, hvF]
      rfl
    calc _ ≤ d * ((d + 1) * d + 1) * (2 * s) ^ 3 * M := hle
      _ ≤ _ := mul_le_mul_of_nonneg_left hMle (by positivity)

end Rigidity.Proofs.Regularity
