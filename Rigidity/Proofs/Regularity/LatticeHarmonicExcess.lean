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
    latticeEuclideanEmbedding (y + v) =
      latticeEuclideanEmbedding y + latticeEuclideanEmbedding v := by
  ext i
  change ((y + v) i : ℝ) = (y i : ℝ) + (v i : ℝ)
  push_cast [Pi.add_apply]
  rfl

theorem latticeEuclideanEmbedding_sub (y v : Fin d → ℤ) :
    latticeEuclideanEmbedding (y - v) =
      latticeEuclideanEmbedding y - latticeEuclideanEmbedding v := by
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

/-- The coefficient of `sq_fwd_fwd_le` at the scale `m`. -/
noncomputable def secondDiffCoeff (d m : ℕ) : ℝ :=
  4 ^ d * (64 * d) ^ d / ((m : ℝ) + 1) ^ d *
    (16 * d / ((4 ^ d * (2 * m) : ℕ) : ℝ) ^ 2 * (16 * d / ((2 * (4 ^ d * (2 * m)) + 2 : ℕ) : ℝ) ^ 2))

theorem secondDiffCoeff_nonneg (d m : ℕ) : 0 ≤ secondDiffCoeff d m := by
  unfold secondDiffCoeff; positivity

/-- The lattice harmonic functions on `B_r(z)`, restricted to the lattice. -/
def latticeHarmonicClass [NeZero d] (z : Vertex d) (r : ℝ) : Set (latticeComponent d → ℝ) :=
  {v | ∃ F : (Fin d → ℤ) → ℝ, (∀ x, v x = F x.val) ∧
    ∀ y : Fin d → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < r →
      latticeLaplacian F y = 0}

/-- **Excess decay below the interior scale.** -/
theorem ballExcess_le_of_latticeHarmonic [NeZero d] (z : Vertex d) {r s : ℝ} {m : ℕ}
    (hm : 0 < m) (hbox : Real.sqrt d * ((4 * (4 ^ d * (2 * m)) + 6 : ℕ) : ℝ) < r)
    (hsm : s ≤ m) (hs0 : 0 ≤ s) {v : latticeComponent d → ℝ}
    (hv : v ∈ latticeHarmonicClass z r) {w : latticeComponent d → ℝ}
    (hw : w ∈ clusterAffine (latticeComponent d)) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (clusterAffine (latticeComponent d))
        s v ≤
      d * (d + 1) * (2 * s) ^ 2 * Real.sqrt (secondDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
  classical
  obtain ⟨F, hvF, hF⟩ := hv
  obtain ⟨a, p, hwap⟩ := hw
  set W : (Fin d → ℤ) → ℝ := fun y => a + inner ℝ p (latticeEuclideanEmbedding y) with hW
  set f : (Fin d → ℤ) → ℝ := fun y => F y - W y with hfdef
  set ρ := 4 ^ d * (2 * m) with hρ
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  -- `f` is harmonic on `Q_{4ρ+4}(z)`
  have hf : ∀ x ∈ supBox z (4 * ρ + 4), latticeLaplacian f x = 0 := by
    intro x hx
    rw [hfdef, latticeLaplacian_sub, latticeLaplacian_affine, sub_zero]
    apply hF
    refine (dist_le_of_mem_supBox hx).trans_lt (lt_of_le_of_lt ?_ hbox)
    apply mul_le_mul_of_nonneg_left _ hsd
    exact_mod_cast (by omega : 4 * ρ + 4 ≤ 4 * ρ + 6)
  set n := ⌊s⌋₊ with hn
  have hnm : n ≤ m := Nat.floor_le_of_le hsm
  have hns : (n : ℝ) ≤ s := Nat.floor_le hs0
  set M := Real.sqrt (secondDiffCoeff d m * ∑ y ∈ supBox z (4 * ρ + 6), f y ^ 2) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set c : Fin d → ℤ := fun i => z i - n with hc
  -- the second differences on `Q_n(z)`
  have hM : ∀ y : Fin d → ℤ, y ∈ supBox z n → ∀ a b, |fwd a (fwd b f) y| ≤ M := by
    intro y hy a b
    apply Real.abs_le_sqrt
    have hy' : y ∈ supBox z m := by
      rw [mem_supBox_iff_supDist_le] at hy ⊢; omega
    have := sq_fwd_fwd_le f z hm (by rw [← hρ]; exact hf) a b hy'
    rw [secondDiffCoeff]
    have e : 2 * (2 * ρ + 2) + 2 = 4 * ρ + 6 := by ring
    rw [← hρ, e] at this
    calc fwd a (fwd b f) y ^ 2 ≤ _ := this
      _ = _ := by ring
  -- the affine Taylor polynomial at the corner `c`
  set q : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => fwd i f c with hq
  set α := f c - ∑ i, (c i : ℝ) * fwd i f c with hα
  have hTaff : (fun x : latticeComponent d => α + inner ℝ q (latticeEuclideanEmbedding x.val)) ∈
      clusterAffine (latticeComponent d) := ⟨α, q, fun _ => rfl⟩
  have hsum_aff := (clusterAffine (latticeComponent d)).add_mem ⟨a, p, hwap⟩ hTaff
  refine (ballExcess_le _ _ hsum_aff).trans ?_
  rw [componentBallSeminorm_apply]
  have hbound : 0 ≤ d * (d + 1) * (2 * (n : ℝ)) ^ 2 * M := by positivity
  refine (componentBallL2_le_of_abs_le (latticeComponent d) z s hbound ?_).trans ?_
  · intro x hx
    have hxz := abs_sub_le_floor_of_mem_ball hx
    have hcx : ∀ i, c i ≤ x.val i := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; omega
    have hs2 : ∀ i, x.val i - c i ≤ (2 * n : ℕ) := fun i => by
      have := abs_le.1 (hxz i); simp only [hc]; rw [← hn] at this; push_cast; omega
    have htay := abs_sub_taylor_le f hcx hs2 hM0 (fun y hy a b => hM y (by
      rw [mem_supBox_iff_supDist_le]
      simp only [supDist, Finset.sup_le_iff, mem_univ, true_implies]
      intro i
      have h1 := hy i
      have h2 := abs_le.1 (hxz i)
      simp only [hc] at h1
      rw [← hn] at h2
      omega) a b)
    have hinner : inner ℝ q (latticeEuclideanEmbedding x.val) =
        ∑ i, (x.val i : ℝ) * fwd i f c := by
      rw [inner_eq_sum]
      exact sum_congr rfl fun i _ => mul_comm _ _
    have hsplit : ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i f c =
        ∑ i, (x.val i : ℝ) * fwd i f c - ∑ i, (c i : ℝ) * fwd i f c := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by push_cast; ring
    have hval : (v - (w + fun x : latticeComponent d =>
        α + inner ℝ q (latticeEuclideanEmbedding x.val))) x =
        f x.val - f c - ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i f c := by
      rw [Pi.sub_apply, Pi.add_apply, hvF, hwap, hinner, hsplit, hα]
      simp only [hfdef, hW]
      ring
    have e4 : (2 * n : ℕ) = 2 * n := rfl
    rw [hval]
    calc |f x.val - f c - ∑ i, ((x.val i - c i : ℤ) : ℝ) * fwd i f c|
        ≤ d * (d + 1) * ((2 * n : ℕ) : ℝ) ^ 2 * M := htay
      _ = d * (d + 1) * (2 * (n : ℝ)) ^ 2 * M := by push_cast; ring
  · -- compare with the norm on `B_r`
    have h1 : (2 * (n : ℝ)) ^ 2 ≤ (2 * s) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 : M ≤ Real.sqrt (secondDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) *
          componentBallL2 (latticeComponent d) z r (v - w) ^ 2)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (secondDiffCoeff_nonneg d m)
      rw [← sum_sq_eq_card_mul_componentBallL2_sq]
      have hball := sum_sq_supBox_le_ball z (L := 4 * ρ + 6) hbox f
      refine hball.trans (le_of_eq (sum_congr rfl fun x _ => ?_))
      simp only [Pi.sub_apply, hvF, hwap, hfdef, hW]
    have hd0 : (0 : ℝ) ≤ d * (d + 1) := by positivity
    calc d * (d + 1) * (2 * (n : ℝ)) ^ 2 * M ≤ d * (d + 1) * (2 * s) ^ 2 * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hd0) hM0
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem secondDiffCoeff_le (d : ℕ) {m : ℕ} (hm : 0 < m) :
    secondDiffCoeff d m ≤ 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 / (m : ℝ) ^ (d + 4) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set ρ : ℝ := ((4 ^ d * (2 * m) : ℕ) : ℝ) with hρ
  set ρ' : ℝ := ((2 * (4 ^ d * (2 * m)) + 2 : ℕ) : ℝ) with hρ'
  have hρm : (m : ℝ) ≤ ρ := by
    rw [hρ]; push_cast
    have : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  have hρ'm : (m : ℝ) ≤ ρ' := by
    rw [hρ']; push_cast
    have : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  have e : secondDiffCoeff d m = 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 *
      (1 / ((m : ℝ) + 1) ^ d * (1 / ρ ^ 2) * (1 / ρ' ^ 2)) := by
    rw [secondDiffCoeff, ← hρ, ← hρ']; ring
  rw [e]
  have h1 : 1 / ((m : ℝ) + 1) ^ d ≤ 1 / (m : ℝ) ^ d :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hm'.le (by linarith) d)
  have h2 : 1 / ρ ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hm'.le hρm 2)
  have h3 : 1 / ρ' ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hm'.le hρ'm 2)
  have h123 : 1 / ((m : ℝ) + 1) ^ d * (1 / ρ ^ 2) * (1 / ρ' ^ 2) ≤
      1 / (m : ℝ) ^ d * (1 / (m : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) :=
    mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
      (by positivity)
  have e2 : 1 / (m : ℝ) ^ d * (1 / (m : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) = 1 / (m : ℝ) ^ (d + 4) := by
    rw [pow_add]; field_simp
  rw [e2] at h123
  calc 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 *
        (1 / ((m : ℝ) + 1) ^ d * (1 / ρ ^ 2) * (1 / ρ' ^ 2))
      ≤ 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 * (1 / (m : ℝ) ^ (d + 4)) :=
        mul_le_mul_of_nonneg_left h123 (by positivity)
    _ = _ := by ring

/-- The lower radius `X₀ = 2 √d (8 · 4^d + 6)` of the excess decay of lattice harmonic functions. -/
noncomputable def latticeHRScale (d : ℕ) : ℝ := 2 * Real.sqrt d * (8 * 4 ^ d + 6)

/-- The constant of the excess decay of order one of lattice harmonic functions. -/
noncomputable def latticeHRConst (d : ℕ) : ℝ :=
  4 * d * (d + 1) * Real.sqrt (4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 * 5 ^ d *
      (2 * latticeHRScale d) ^ (d + 4)) +
    Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (2 * latticeHRScale d) ^ ((d : ℝ) / 2) *
      (2 * latticeHRScale d) ^ 2

/-- **Excess decay of order one, against one affine function.** -/
theorem ballExcess_le_latticeHRConst_mul [NeZero d] (z : Vertex d) {R r s : ℝ} (hrR : r ≤ R)
    {v : latticeComponent d → ℝ} (hv : v ∈ latticeHarmonicClass z r) (hXs : latticeHRScale d ≤ s)
    (hsr : s ≤ r / 2) {w : latticeComponent d → ℝ} (hw : w ∈ clusterAffine (latticeComponent d)) :
    ballExcess (componentBallSeminorm (latticeComponent d) z) (clusterAffine (latticeComponent d))
        s v ≤ latticeHRConst d * (s / r) ^ 2 * componentBallL2 (latticeComponent d) z r (v - w) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  set X₀ := latticeHRScale d with hX₀
  set Λ : ℝ := 8 * 4 ^ d + 6 with hΛ
  have hΛ1 : 14 ≤ Λ := by
    rw [hΛ]; have : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num); linarith
  have hX₀def : X₀ = 2 * Real.sqrt d * Λ := rfl
  have hX₀pos : 0 < X₀ := by rw [hX₀def]; positivity
  set B := 2 * X₀ with hB
  have hBpos : 0 < B := by positivity
  have hs0 : 0 < s := hX₀pos.trans_le hXs
  have hr2 : 2 * X₀ ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by
    have : (28 : ℝ) ≤ X₀ := by rw [hX₀def]; nlinarith
    linarith
  set N := componentBallL2 (latticeComponent d) z r (v - w) with hN
  have hN0 : 0 ≤ N := componentBallL2_nonneg _ _ _ _
  set m := ⌊r / X₀⌋₊ with hmdef
  have hrX : 2 ≤ r / X₀ := by rw [le_div_iff₀ hX₀pos]; linarith
  have hm2 : 2 ≤ m := Nat.le_floor (by exact_mod_cast hrX)
  have hm0 : 0 < m := by omega
  have hmle : (m : ℝ) ≤ r / X₀ := Nat.floor_le (by positivity)
  have hmge : r / B ≤ m := by
    have h1 := Nat.lt_floor_add_one (r / X₀)
    rw [← hmdef] at h1
    have : r / B = r / X₀ / 2 := by rw [hB]; field_simp
    rw [this]; linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  -- the box of the interior estimates lies in `B_r(z)`
  have hbox : Real.sqrt d * ((4 * (4 ^ d * (2 * m)) + 6 : ℕ) : ℝ) < r := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have h1 : ((4 * (4 ^ d * (2 * m)) + 6 : ℕ) : ℝ) ≤ Λ * m := by
      push_cast; rw [hΛ]; nlinarith
    have h2 : Λ * m ≤ Λ * (r / X₀) := mul_le_mul_of_nonneg_left hmle (by linarith)
    have h3 : Real.sqrt d * (Λ * (r / X₀)) = r / 2 := by
      rw [hX₀def]; field_simp
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : 0 ≤ Real.sqrt d)
    linarith
  have hCH1 : 0 ≤ 4 * d * (d + 1) * Real.sqrt (4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 * 5 ^ d *
      (2 * latticeHRScale d) ^ (d + 4)) := by positivity
  have hCH2 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) *
      (2 * latticeHRScale d) ^ ((d : ℝ) / 2) * (2 * latticeHRScale d) ^ 2 := by positivity
  have hsr2 : 0 ≤ (s / r) ^ 2 := sq_nonneg _
  by_cases hsm : s ≤ m
  · have h := ballExcess_le_of_latticeHarmonic z hm0 hbox hsm hs0.le hv hw
    refine h.trans ?_
    set K₀ : ℝ := 4 ^ d * (64 * d) ^ d * (16 * d) ^ 2 with hK₀
    have hK₀0 : 0 ≤ K₀ := by positivity
    have hcoef := secondDiffCoeff_le d hm0
    have hcard : ((componentEuclideanBall (latticeComponent d) z r).card : ℝ) ≤ (5 * r) ^ d :=
      (card_componentEuclideanBall_le _ z hr0.le).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) d)
    have hinv : 1 / (m : ℝ) ^ (d + 4) ≤ (B / r) ^ (d + 4) := by
      rw [one_div, ← inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_comm₀ hmpos (by positivity), inv_div]
      exact hmge
    have hin : secondDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2) ≤
        (K₀ * 5 ^ d * B ^ (d + 4)) * (N / r ^ 2) ^ 2 := by
      calc secondDiffCoeff d m *
            (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2)
          ≤ K₀ / (m : ℝ) ^ (d + 4) * ((5 * r) ^ d * N ^ 2) :=
            mul_le_mul hcoef (mul_le_mul_of_nonneg_right hcard (sq_nonneg _)) (by positivity)
              (by positivity)
        _ ≤ K₀ * (B / r) ^ (d + 4) * ((5 * r) ^ d * N ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left hinv hK₀0
        _ = (K₀ * 5 ^ d * B ^ (d + 4)) * (N / r ^ 2) ^ 2 := by
            rw [div_pow, div_pow, mul_pow]
            field_simp
            ring
    have hsq : Real.sqrt (secondDiffCoeff d m *
        (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2)) ≤
        Real.sqrt (K₀ * 5 ^ d * B ^ (d + 4)) * (N / r ^ 2) := by
      calc _ ≤ Real.sqrt ((K₀ * 5 ^ d * B ^ (d + 4)) * (N / r ^ 2) ^ 2) := Real.sqrt_le_sqrt hin
        _ = _ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc d * (d + 1) * (2 * s) ^ 2 * Real.sqrt (secondDiffCoeff d m *
          (((componentEuclideanBall (latticeComponent d) z r).card : ℝ) * N ^ 2))
        ≤ d * (d + 1) * (2 * s) ^ 2 * (Real.sqrt (K₀ * 5 ^ d * B ^ (d + 4)) * (N / r ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * d * (d + 1) * Real.sqrt (K₀ * 5 ^ d * B ^ (d + 4)) * (s / r) ^ 2 * N := by
          field_simp
          ring
      _ ≤ latticeHRConst d * (s / r) ^ 2 * N := by
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr2
          rw [latticeHRConst, ← hX₀, ← hB, ← hK₀]
          linarith
  · push Not at hsm
    have hsm' : r / B < s := lt_of_le_of_lt hmge hsm
    have hvol := clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent d) z R hd
      one_pos (clusterCubeDensity_latticeComponent z (24 * Real.sqrt d) 1)
    have h6 : 6 * Real.sqrt d * max 1 1 ≤ s := by
      rw [max_self, mul_one]
      have : 6 * Real.sqrt d ≤ X₀ := by rw [hX₀def]; nlinarith
      linarith
    have hmono := radiusMonotone_componentBallSeminorm (latticeComponent d) z
      (by positivity : (0 : ℝ) < 6 * Real.sqrt d * max 1 1) (by positivity) hvol
    have h1 := ballExcess_le (componentBallSeminorm (latticeComponent d) z)
      (clusterAffine (latticeComponent d)) (s := s) (u := v) hw
    have h2 := hmono (v - w) s r h6 (by linarith) hrR
    rw [componentBallSeminorm_apply, componentBallSeminorm_apply] at h2
    rw [componentBallSeminorm_apply] at h1
    have hrs : r / s ≤ B := by
      rw [div_le_iff₀ hs0]; rw [div_lt_iff₀ hBpos] at hsm'; linarith
    have hrs0 : 0 ≤ r / s := by positivity
    have h3 : (r / s) ^ ((d : ℝ) / 2) ≤ B ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow hrs0 hrs (by positivity)
    have h4 : 1 ≤ B ^ 2 * (s / r) ^ 2 := by
      rw [← mul_pow]
      have : 1 ≤ B * (s / r) := by
        rw [div_lt_iff₀ hBpos] at hsm'
        rw [mul_div_assoc', le_div_iff₀ hr0]; linarith
      exact one_le_pow₀ this
    have hK : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) := Real.sqrt_nonneg _
    calc ballExcess (componentBallSeminorm (latticeComponent d) z)
          (clusterAffine (latticeComponent d)) s v
        ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * (r / s) ^ ((d : ℝ) / 2) * N :=
          h1.trans h2
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * B ^ ((d : ℝ) / 2) * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hK) hN0
      _ ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * B ^ ((d : ℝ) / 2) *
            (B ^ 2 * (s / r) ^ 2) * N := by
          have h5 : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * B ^ ((d : ℝ) / 2) * N := by
            positivity
          nlinarith
      _ ≤ latticeHRConst d * (s / r) ^ 2 * N := by
          have e : Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) * B ^ ((d : ℝ) / 2) *
              (B ^ 2 * (s / r) ^ 2) * N = (Real.sqrt ((5 * (6 * Real.sqrt d)) ^ d / 1) *
                B ^ ((d : ℝ) / 2) * B ^ 2) * (s / r) ^ 2 * N := by ring
          rw [e]
          apply mul_le_mul_of_nonneg_right _ hN0
          apply mul_le_mul_of_nonneg_right _ hsr2
          rw [latticeHRConst, ← hX₀, ← hB]
          linarith

/-- **Excess decay of order one of lattice harmonic functions on the lattice balls**:
`HarmonicRegularity` with `j = 1` for the class `latticeHarmonicClass z` above the radius
`latticeHRScale d`, with the constant `latticeHRConst d`. -/
theorem harmonicRegularity_latticeHarmonicClass [NeZero d] (z : Vertex d) (R : ℝ) :
    HarmonicRegularity (componentBallSeminorm (latticeComponent d) z) (latticeHarmonicClass z)
      (clusterAffine (latticeComponent d)) 1 (latticeHRScale d) R (latticeHRConst d) := by
  intro r hrR v hv s hXs hsr
  have hK : 0 ≤ latticeHRConst d * (s / r) ^ (1 + 1) := by
    have hX : 0 ≤ latticeHRScale d := by unfold latticeHRScale; positivity
    have : 0 ≤ latticeHRConst d := by rw [latticeHRConst]; positivity
    exact mul_nonneg this (pow_two_nonneg _)
  have e : latticeHRConst d * (s / r) ^ (1 + 1) *
      ballExcess (componentBallSeminorm (latticeComponent d) z)
        (clusterAffine (latticeComponent d)) r v =
      ⨅ w : clusterAffine (latticeComponent d), latticeHRConst d * (s / r) ^ (1 + 1) *
        componentBallSeminorm (latticeComponent d) z r (v - w) :=
    Real.mul_iInf_of_nonneg hK _
  rw [e]
  refine le_ciInf fun w => ?_
  rw [componentBallSeminorm_apply]
  exact ballExcess_le_latticeHRConst_mul z hrR hv hXs hsr w.2

theorem latticeHRConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ latticeHRConst d := by
  have hX : 0 ≤ latticeHRScale d := by unfold latticeHRScale; positivity
  rw [latticeHRConst]; positivity

theorem zero_mem_latticeHarmonicClass [NeZero d] (z : Vertex d) (r : ℝ) :
    (0 : latticeComponent d → ℝ) ∈ latticeHarmonicClass z r :=
  ⟨fun _ => 0, fun _ => rfl, fun y _ => by simp [latticeLaplacian]⟩

/-- **Armstrong–Dario, Lemma 7.2 (`k = 0`), for lattice harmonic functions on the balls of the
lattice**: with `Ā(B_r)` the lattice harmonic functions on `B_r(z)`, whose excess decay is
`harmonicRegularity_latticeHarmonicClass`, only the harmonic approximation hypothesis remains. -/
theorem armstrongDario_lemma_7_2_zero_latticeHarmonic (d : ℕ) [NeZero d] {A α : ℝ} (hA : 2 ≤ A)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vertex d) (R X E : ℝ) (u : latticeComponent d → ℝ),
      1 ≤ X → max (latticeHRScale d) (24 * Real.sqrt d) ≤ X → X ≤ R / A → 0 ≤ E →
      HarmonicApproximation (componentBallSeminorm (latticeComponent d) z)
        (latticeHarmonicClass z) (clusterConstants (latticeComponent d)) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) r u ≤
          C * (r / R) * ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u +
          C * r ^ (1 - α) * (ballExcess (componentBallSeminorm (latticeComponent d) z)
            (clusterConstants (latticeComponent d)) R u / R + E / r) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_zero_lattice d hd hA hα (latticeHRConst_nonneg d)
  refine ⟨C, hC, fun z R X E u hX hXs hXR hE happ => ?_⟩
  exact h z (latticeHarmonicClass z) R X E u hX hXR hE ((le_max_right _ _).trans hXs)
    ((harmonicRegularity_latticeHarmonicClass z R).of_le _ ((le_max_left _ _).trans hXs))
    (fun r _ _ => ⟨0, zero_mem_latticeHarmonicClass z r⟩) happ

end Rigidity.Proofs.Regularity
