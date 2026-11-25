import Rigidity.Proofs.Green.OpenHeatSemigroup

/-!
# The energy identity of the planar heat kernel

For the heat kernel `openHeat ω t x y` of the variable speed random walk on the open graph of a
planar bond configuration, this file proves the discrete Gauss–Green formula for summable bounded
functions,
`Σ_x f(x) Δf(x) = -½ Σ_x Σ_{z ∼ x} (f(z) - f(x))²`,
and the energy identity used in the proof of Proposition 3.1 of Barlow (*Random walks on
supercritical percolation clusters*, Ann. Probab. 32 (2004)):
`d/dt p_{2t}(x, x) = -Σ_y Σ_{z ∼ y} (p_t(x, z) - p_t(x, y))²`.
It also records `p_{2t}(x, x) = Σ_y p_t(x, y)²` and
`p_{2t}(x, y) ≤ (p_{2t}(x, x) + p_{2t}(y, y)) / 2`.

The double sums over neighbours are sums over the directed open edges `OpenDart ω`, on which the
reversal `(x, z) ↦ (z, x)` is an involution.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Barlow

section Darts

variable (ω : Configuration 2)

/-- The directed open edges `(x, z)`, `z ∼ x`, of a planar configuration. -/
abbrev OpenDart : Type := Σ x : Vertex 2, (openGraph ω).neighborFinset x

/-- The reversal `(x, z) ↦ (z, x)` of directed open edges. -/
def OpenDart.rev : OpenDart ω ≃ OpenDart ω where
  toFun e := ⟨e.2.1, ⟨e.1, ((openGraph ω).mem_neighborFinset _ _).2
    (((openGraph ω).mem_neighborFinset _ _).1 e.2.2).symm⟩⟩
  invFun e := ⟨e.2.1, ⟨e.1, ((openGraph ω).mem_neighborFinset _ _).2
    (((openGraph ω).mem_neighborFinset _ _).1 e.2.2).symm⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {ω}

/-- A family on directed edges dominated by a summable function of the tail is summable. -/
theorem summable_openDart_of_abs_le {h : OpenDart ω → ℝ} {g : Vertex 2 → ℝ} (hg : Summable g)
    (hg0 : ∀ x, 0 ≤ g x) (hhg : ∀ e, |h e| ≤ g e.1) : Summable h := by
  have hfib : Summable fun e : OpenDart ω => g e.1 := by
    refine (summable_sigma_of_nonneg fun e => hg0 e.1).2 ⟨fun x => Summable.of_finite, ?_⟩
    refine (hg.mul_left 4).of_nonneg_of_le (fun x => tsum_nonneg fun _ => hg0 x) fun x => ?_
    rw [tsum_fintype]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul]
    have hdeg : ((openGraph ω).degree x : ℝ) ≤ 4 := by exact_mod_cast openGraph_degree_le_four ω x
    exact mul_le_mul_of_nonneg_right hdeg (hg0 x)
  exact Summable.of_norm_bounded hfib fun e => by rw [Real.norm_eq_abs]; exact hhg e

/-- A summable sum over directed edges is the sum over vertices of the sums over neighbours. -/
theorem tsum_openDart {F : Vertex 2 → Vertex 2 → ℝ}
    (hF : Summable fun e : OpenDart ω => F e.1 e.2.1) :
    ∑' e : OpenDart ω, F e.1 e.2.1 = ∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, F x z := by
  rw [hF.tsum_sigma]
  exact tsum_congr fun x => Finset.tsum_subtype ((openGraph ω).neighborFinset x) (F x)

theorem summable_neighbor_sum_of_openDart {F : Vertex 2 → Vertex 2 → ℝ}
    (hF : Summable fun e : OpenDart ω => F e.1 e.2.1) :
    Summable fun x => ∑ z ∈ (openGraph ω).neighborFinset x, F x z := by
  have h := hF.sigma
  refine h.congr fun x => ?_
  exact Finset.tsum_subtype ((openGraph ω).neighborFinset x) (F x)

/-- Reversal of the directed edges leaves sums unchanged. -/
theorem tsum_openDart_swap (F : Vertex 2 → Vertex 2 → ℝ) :
    ∑' e : OpenDart ω, F e.1 e.2.1 = ∑' e : OpenDart ω, F e.2.1 e.1 :=
  ((OpenDart.rev ω).tsum_eq (fun e => F e.1 e.2.1)).symm

theorem summable_openDart_swap {F : Vertex 2 → Vertex 2 → ℝ}
    (hF : Summable fun e : OpenDart ω => F e.1 e.2.1) :
    Summable fun e : OpenDart ω => F e.2.1 e.1 :=
  (OpenDart.rev ω).summable_iff.2 hF

end Darts

variable {ω : Configuration 2}

/-- **The discrete Gauss–Green formula** (Barlow 2004, Lemma 1.6) for a summable bounded function on
the open graph: the energy is summable and `Σ_x f(x) Δf(x) = -½ Σ_x Σ_{z ∼ x} (f(z) - f(x))²`. -/
theorem tsum_mul_openLaplacian {f : Vertex 2 → ℝ} {B : ℝ} (hf : Summable f)
    (hB : ∀ x, |f x| ≤ B) :
    Summable (fun x => ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) ∧
      ∑' x, f x * openLaplacian ω f x =
        -(1 / 2) * ∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hP : Summable fun e : OpenDart ω => f e.1 * (f e.2.1 - f e.1) := by
    refine summable_openDart_of_abs_le (g := fun x => 2 * B * |f x|) (hf.abs.mul_left _)
      (fun x => by positivity) fun e => ?_
    rw [abs_mul, mul_comm]
    have h1 : |f e.2.1 - f e.1| ≤ 2 * B := by
      calc |f e.2.1 - f e.1| ≤ |f e.2.1| + |f e.1| := abs_sub _ _
        _ ≤ B + B := add_le_add (hB _) (hB _)
        _ = 2 * B := by ring
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hQ : Summable fun e : OpenDart ω => f e.2.1 * (f e.1 - f e.2.1) :=
    summable_openDart_swap (F := fun a b => f a * (f b - f a)) hP
  have hS : Summable fun e : OpenDart ω => (f e.2.1 - f e.1) ^ 2 := by
    refine ((hP.add hQ).neg).congr fun e => ?_
    ring
  have hswap : ∑' e : OpenDart ω, f e.2.1 * (f e.1 - f e.2.1) =
      ∑' e : OpenDart ω, f e.1 * (f e.2.1 - f e.1) :=
    (tsum_openDart_swap (fun a b => f a * (f b - f a))).symm
  have hSsum : ∑' e : OpenDart ω, (f e.2.1 - f e.1) ^ 2 =
      -(2 * ∑' e : OpenDart ω, f e.1 * (f e.2.1 - f e.1)) := by
    have : (fun e : OpenDart ω => (f e.2.1 - f e.1) ^ 2) =
        fun e => -(f e.1 * (f e.2.1 - f e.1) + f e.2.1 * (f e.1 - f e.2.1)) := by
      funext e
      ring
    rw [this, tsum_neg, hP.tsum_add hQ, hswap]
    ring
  refine ⟨summable_neighbor_sum_of_openDart (F := fun a b => (f b - f a) ^ 2) hS, ?_⟩
  have hL : ∑' x, f x * openLaplacian ω f x =
      ∑' e : OpenDart ω, f e.1 * (f e.2.1 - f e.1) := by
    rw [tsum_openDart (F := fun a b => f a * (f b - f a)) hP]
    refine tsum_congr fun x => ?_
    rw [openLaplacian, Finset.mul_sum]
  rw [hL, ← tsum_openDart (F := fun a b => (f b - f a) ^ 2) hS, hSsum]
  ring

/-- `p_{2t}(x, x) = Σ_y p_t(x, y)²`. -/
theorem hasSum_openHeat_sq {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    HasSum (fun y => openHeat ω t x y ^ 2) (openHeat ω (2 * t) x x) := by
  have h := hasSum_openHeat_mul ω ht ht x x
  rw [← two_mul] at h
  have he : (fun y => openHeat ω t x y ^ 2) = fun y => openHeat ω t x y * openHeat ω t y x :=
    funext fun y => by rw [sq, openHeat_symm ω t y x]
  rw [he]
  exact h

/-- The Laplacian of the heat kernel in its first variable may be taken in either variable. -/
theorem openLaplacian_openHeat_comm (t : ℝ) (x w : Vertex 2) :
    openLaplacian ω (fun z => openHeat ω t z w) x =
      openLaplacian ω (fun z => openHeat ω t z x) w := by
  have h1 := hasDerivAt_openHeat ω t x w
  have h2 := hasDerivAt_openHeat ω t w x
  have h3 : (fun s => openHeat ω s x w) = fun s => openHeat ω s w x :=
    funext fun s => openHeat_symm ω s x w
  rw [h3] at h1
  exact h1.unique h2

/-- `0 ≤ p_t ≤ 1`, as an absolute bound. -/
theorem abs_openHeat_le_one {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) : |openHeat ω t x y| ≤ 1 := by
  rw [abs_of_nonneg (openHeat_nonneg ω ht x y)]
  exact openHeat_le_one ω ht x y

/-- The Dirichlet energy `Σ_y Σ_{z ∼ y} (p_t(x, z) - p_t(x, y))²` of the heat kernel is summable. -/
theorem summable_openHeat_energy {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Summable fun y => ∑ z ∈ (openGraph ω).neighborFinset y,
      (openHeat ω t x z - openHeat ω t x y) ^ 2 :=
  (tsum_mul_openLaplacian (ω := ω) (hasSum_openHeat ω ht x).summable
    (abs_openHeat_le_one ht x)).1

/-- **The energy identity** (Barlow 2004, proof of Proposition 3.1):
`d/dt p_{2t}(x, x) = -Σ_y Σ_{z ∼ y} (p_t(x, z) - p_t(x, y))²` for `t ≥ 0`. -/
theorem hasDerivAt_openHeat_two_mul {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    HasDerivAt (fun s => openHeat ω (2 * s) x x)
      (-∑' y, ∑ z ∈ (openGraph ω).neighborFinset y,
        (openHeat ω t x z - openHeat ω t x y) ^ 2) t := by
  set f : Vertex 2 → ℝ := fun y => openHeat ω t x y with hf
  have hd := hasDerivAt_openHeat ω (2 * t) x x
  have hc : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hcomp := hd.comp t hc
  have hterm : ∀ z, HasSum (fun w => (openHeat ω t z w - openHeat ω t x w) * openHeat ω t w x)
      (openHeat ω (2 * t) z x - openHeat ω (2 * t) x x) := by
    intro z
    have h1 := hasSum_openHeat_mul ω ht ht z x
    have h2 := hasSum_openHeat_mul ω ht ht x x
    rw [← two_mul] at h1 h2
    have he : (fun w => (openHeat ω t z w - openHeat ω t x w) * openHeat ω t w x) =
        fun w => openHeat ω t z w * openHeat ω t w x - openHeat ω t x w * openHeat ω t w x :=
      funext fun w => by ring
    rw [he]
    exact h1.sub h2
  have hL : openLaplacian ω (fun z => openHeat ω (2 * t) z x) x =
      ∑' w, f w * openLaplacian ω f w := by
    have hs := hasSum_sum (s := (openGraph ω).neighborFinset x) fun z _ => hterm z
    rw [openLaplacian, ← hs.tsum_eq]
    refine tsum_congr fun w => ?_
    rw [← Finset.sum_mul]
    have hlap : ∑ z ∈ (openGraph ω).neighborFinset x, (openHeat ω t z w - openHeat ω t x w) =
        openLaplacian ω f w := by
      have := openLaplacian_openHeat_comm (ω := ω) t x w
      rw [openLaplacian] at this
      rw [this]
      have hfz : (fun z => openHeat ω t z x) = f := funext fun z => openHeat_symm ω t z x
      rw [hfz]
    rw [hlap, openHeat_symm ω t w x, mul_comm]
  obtain ⟨-, hGG⟩ := tsum_mul_openLaplacian (ω := ω) (hasSum_openHeat ω ht x).summable
    (abs_openHeat_le_one ht x)
  refine hcomp.congr_deriv ?_
  rw [hL, hGG]
  ring

/-- `p_{2t}(x, y) ≤ (p_{2t}(x, x) + p_{2t}(y, y)) / 2` for `t ≥ 0`. -/
theorem openHeat_two_mul_le_half_add {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) :
    openHeat ω (2 * t) x y ≤ (openHeat ω (2 * t) x x + openHeat ω (2 * t) y y) / 2 := by
  have h := hasSum_openHeat_mul ω ht ht x y
  rw [← two_mul] at h
  have hx := hasSum_openHeat_sq (ω := ω) ht x
  have hy := hasSum_openHeat_sq (ω := ω) ht y
  refine hasSum_le (fun w => ?_) h ((hx.add hy).div_const 2)
  rw [openHeat_symm ω t w y]
  nlinarith [sq_nonneg (openHeat ω t x w - openHeat ω t y w)]

end Rigidity.Barlow
