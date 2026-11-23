import Rigidity.Proofs.Green.DarioGuDensityGaussianBound
import Rigidity.Proofs.Green.DarioGuTail

/-!
# The inputs of Lemma 4.1 of Dario–Gu in dimension two

The proof of Lemma 4.1 of Dario–Gu (lines 1993-2148 of the source) uses, besides Theorem 4
(Barlow), Proposition 2.15 (Carne–Varopoulos) and Proposition A.7, two estimates on balls of the
infinite cluster: the Poincaré inequality (Proposition 2.7) and the gradient bound on the heat
kernel (Theorem 3, through Remark 1.3). This file fixes the discrete objects and states them.

* `clusterBall K y r` is `𝒞 ∩ B_r(y)`, the vertices of the component `K` at distance less than
  `r` from `y`; `finAvg U u` is the average `(u)_U`.
* `gradEnergy ω U u` is `Σ_{x ∈ U} |∇u|_U(x)²` with `|∇u|_U(x) = Σ_{z ∈ U, z ∼ x} |u(z) - u(x)|`,
  the sum over the open edges with both endpoints in `U` (Dario–Gu, (1.28) and (1.31) for a
  function on `𝒞_∞ ∩ U`), so that `‖∇u‖_{L̲²(𝒞_∞ ∩ U)} = (gradEnergy ω U u / |U|)^{1/2}`.

Named statements (printed statements, not formalized here):

* `ClusterPoincareTwo`: Proposition 2.7 for `p = 2` (first part), in dimension two, in the weak
  form with the gradient on a dilated ball (cited by the source: Barlow 2004, Theorem 2.18;
  Armstrong–Dario 2018, Proposition 3.4); the printed form, with the gradient on the same ball,
  fails at large radii (see the docstring).
* `DarioGuGradientBoundTwo`: Theorem 3 in the form of Remark 1.3, in dimension two (proved in §3 of
  the source from Theorem 5 and Proposition 3.9). The gradient is taken over the edges inside the
  ball; the printed statement, with all the edges at the vertices of the ball, implies it.
-/

open Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-! ### Balls of the cluster -/

/-- `𝒞 ∩ B_r(y)`: the vertices of `K` at distance less than `r` from `y`. -/
noncomputable def clusterBall {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2) (r : ℝ) :
    Finset (Vertex 2) := by
  classical
  exact (indexBox y (⌈r⌉₊ : ℤ)).filter (fun x => x ∈ K.supp ∧ latticeDist x y < r)

theorem mem_clusterBall {ω : Configuration 2} {K : OpenComponent ω} {y x : Vertex 2} {r : ℝ} :
    x ∈ clusterBall K y r ↔ x ∈ K.supp ∧ latticeDist x y < r := by
  classical
  unfold clusterBall
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_indexBox.2 fun i => ?_, h⟩
    have h1 := (latticeDist_ge_abs x y i).trans_lt h.2
    have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h3 : |((x i - y i : ℤ) : ℝ)| < ((⌈r⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3.le

theorem clusterBall_mono {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2} {r r' : ℝ}
    (h : r ≤ r') : clusterBall K y r ⊆ clusterBall K y r' := by
  intro x hx
  rw [mem_clusterBall] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le h⟩

theorem card_clusterBall_le {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2) {r : ℝ}
    (hr : 1 ≤ r) : ((clusterBall K y r).card : ℝ) ≤ 25 * r ^ 2 := by
  classical
  have h1 : (clusterBall K y r).card ≤ (indexBox y (⌈r⌉₊ : ℤ)).card := by
    unfold clusterBall
    convert Finset.card_filter_le _ _
  rw [card_indexBox] at h1
  have h2 : ((clusterBall K y r).card : ℝ) ≤ ((2 * ⌈r⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  push_cast at h2
  have h3 : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : (0 : ℝ) ≤ ⌈r⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- The average `(u)_U = |U|^{-1} Σ_{x ∈ U} u(x)`. -/
noncomputable def finAvg (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) : ℝ :=
  (∑ x ∈ U, u x) / U.card

/-- `Σ_{x ∈ U} |∇u|_U(x)²`, with `|∇u|_U(x) = Σ_{z ∈ U, z ∼ x} |u(z) - u(x)|` over the open edges
with both endpoints in `U`. -/
noncomputable def gradEnergy (ω : Configuration 2) (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) :
    ℝ := by
  classical
  exact ∑ x ∈ U, (∑ z ∈ U.filter (fun z => (openGraph ω).Adj x z), |u z - u x|) ^ 2

theorem gradEnergy_nonneg (ω : Configuration 2) (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) :
    0 ≤ gradEnergy ω U u := by
  unfold gradEnergy
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

/-! ### The named statements -/

/-- **Dario–Gu, Proposition 2.7** (Poincaré inequality on `𝒞_∞`), `p = 2`, in dimension two, in
the weak form with the gradient on the dilated ball `𝒞_∞ ∩ B_{CR}(y)`.

Printed statement (lines 979-993 of the source): *There exist a constant `C < ∞` and an exponent
`s > 0` such that, for any `y ∈ ℤ^d`, there exists a non-negative random variable
`M_Poinc(y) ≤ O_s(C)` such that for each radius `R ≥ M_Poinc(y)` and each function
`u : 𝒞_∞ ∩ B_R(y) → ℝ`, `‖u - (u)_{𝒞_∞ ∩ B_R(y)}‖_{L̲²(𝒞_∞ ∩ B_R(y))} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_R(y))}`.*
Citing lines: "it can be found in [Ba, Theorem 2.18] for the L²-version" (983); "The proof relies on
the Sobolev inequality as stated in [AD2, Proposition 3.4]" (1002).

With the gradient over the open edges inside `𝒞_∞ ∩ B_R(y)` (`u` is defined on this set only),
the printed inequality fails whenever `𝒞_∞ ∩ B_R(y)` is not connected by the open edges inside
`B_R(y)` (a function equal to `1` on one piece and `0` elsewhere), which happens for every large
`R` with probability tending to one (a vertex of `𝒞_∞` near the boundary whose only open edge leaves
the ball). The statement here is the weak Poincaré inequality, with the gradient on the larger set
`𝒞_∞ ∩ B_{CR}(y)`, `C ≥ 1`; it is the form used in the proof of Lemma 4.1. -/
def ClusterPoincareTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 1 ≤ C ∧ ∀ y : Vertex 2,
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, M ω ≤ R →
          ∀ u : Vertex 2 → ℝ,
            Real.sqrt ((∑ x ∈ clusterBall (uniqueInfiniteComponent h) y R,
                (u x - finAvg (clusterBall (uniqueInfiniteComponent h) y R) u) ^ 2) /
                (clusterBall (uniqueInfiniteComponent h) y R).card) ≤
              C * R * Real.sqrt (gradEnergy ω (clusterBall (uniqueInfiniteComponent h) y (C * R)) u /
                (clusterBall (uniqueInfiniteComponent h) y (C * R)).card)

/-- **Dario–Gu, Theorem 3, Remark 1.3** (gradient bound on the heat kernel in the second
variable), in dimension two. Printed statement (lines 516-521 of the source, with (1.20)):
*for each point `y ∈ ℤ^d`, there exists a non-negative random variable `M_reg(y)` satisfying
`P(M_reg(y) ≥ R) ≤ C exp(-R^s/C)` such that for every radius `r ≥ M_reg(y)`, every point
`x ∈ 𝒞_∞` and every time `t ≥ max(4r², |x - y|)`,
`‖∇_y p(t, x, ·)‖_{L̲²(B_r(y) ∩ 𝒞_∞)} ≤ C t^{-d/2 - 1/2} exp(-|x - y|²/(C t))`.*
The gradient is over the open edges inside `B_r(y) ∩ 𝒞_∞` (`gradEnergy`); Theorem 3 is proved in §3
of the source (lines 1865-1911) from Proposition 3.9 and Theorem 4. -/
def DarioGuGradientBoundTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ y : Vertex 2,
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ HasTail p M C s ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ r : ℝ, M ω ≤ r →
          ∀ x ∈ (uniqueInfiniteComponent h).supp, ∀ t : ℝ, 4 * r ^ 2 ≤ t → latticeDist x y ≤ t →
            Real.sqrt (gradEnergy ω (clusterBall (uniqueInfiniteComponent h) y r)
                (fun z => openHeat ω t x z) /
                (clusterBall (uniqueInfiniteComponent h) y r).card) ≤
              C * t ^ (-(3 / 2 : ℝ)) * Real.exp (-(latticeDist x y ^ 2 / (C * t)))

/-! ### The oscillation on a ball -/

/-- From the Poincaré inequality and the gradient bound:
`Σ_{x ∈ U} |u(x) - (u)_U| ≤ C_P R |U| G` when `‖u - (u)_U‖_{L̲²(U)} ≤ C_P R ‖∇u‖_{L̲²(U')}` and
`‖∇u‖_{L̲²(U')} ≤ G`. -/
theorem sum_abs_sub_finAvg_le {ω : Configuration 2} {U U' : Finset (Vertex 2)}
    {u : Vertex 2 → ℝ} {CP R G : ℝ} (hCP : 0 ≤ CP) (hR : 0 ≤ R)
    (hP : Real.sqrt ((∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card) ≤
      CP * R * Real.sqrt (gradEnergy ω U' u / U'.card))
    (hG : Real.sqrt (gradEnergy ω U' u / U'.card) ≤ G) :
    ∑ x ∈ U, |u x - finAvg U u| ≤ CP * R * U.card * G := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < U.card := by exact_mod_cast hne.card_pos
  have hG0 : 0 ≤ G := (Real.sqrt_nonneg _).trans hG
  have hCS : (∑ x ∈ U, |u x - finAvg U u|) ^ 2 ≤ U.card * ∑ x ∈ U, (u x - finAvg U u) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := U) (f := fun x => |u x - finAvg U u|)
    simpa only [sq_abs] using this
  have hL2 : Real.sqrt ((∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card) ≤ CP * R * G :=
    hP.trans (mul_le_mul_of_nonneg_left hG (by positivity))
  have hsq : (∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card ≤ (CP * R * G) ^ 2 := by
    have h0 : 0 ≤ (∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card :=
      div_nonneg (Finset.sum_nonneg fun x _ => sq_nonneg _) hc.le
    calc (∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card
        = Real.sqrt ((∑ x ∈ U, (u x - finAvg U u) ^ 2) / U.card) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (CP * R * G) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL2 2
  have hsum : ∑ x ∈ U, (u x - finAvg U u) ^ 2 ≤ U.card * (CP * R * G) ^ 2 := by
    rw [div_le_iff₀ hc] at hsq
    linarith
  have hfin : (∑ x ∈ U, |u x - finAvg U u|) ^ 2 ≤ (CP * R * U.card * G) ^ 2 := by
    calc (∑ x ∈ U, |u x - finAvg U u|) ^ 2 ≤ U.card * (U.card * (CP * R * G) ^ 2) :=
          hCS.trans (mul_le_mul_of_nonneg_left hsum hc.le)
      _ = (CP * R * U.card * G) ^ 2 := by ring
  exact abs_le_of_sq_le_sq' hfin (by positivity) |>.2

end Rigidity.Green
