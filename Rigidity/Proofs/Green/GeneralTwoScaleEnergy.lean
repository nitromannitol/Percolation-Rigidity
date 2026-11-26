import Rigidity.Proofs.Green.GeneralTwoScaleStepOne
import Rigidity.Proofs.Green.DarioGuTwoScaleGronwall

/-!
# Steps 2 and 5 of Proposition 4.3 of Dario–Gu on `ℤ^d` with the weight one

Step 2 of the proof of Proposition 4.3 of Dario–Gu (lines 2276-2331 of the source) tests the
equation of `w` against `w` and integrates by parts on the cluster; Step 5 (lines 2448-2490)
integrates the resulting differential inequality in time, first with the weight `ψ = 1`, which
gives (4.40). Only this first pass is used for the whole-cluster estimate. On `ℤ^d`:

* `tsum_openLaplacian_mulD`: the discrete integration by parts (1.35),
  `Σ_x (Δ u)(x) φ(x) = -Σ_x Σ_i a_i(x) (u(x + e_i) - u(x)) (φ(x + e_i) - φ(x))` for square
  summable `u`, `φ`; with `φ = u` it is `-E(u)` (`openEnergyD`);
* `hasDerivAt_tsum_sqD`: `∂_s Σ_x u(s, x)² = Σ_x 2 u ∂_s u` when `u` and `∂_s u` are dominated by
  square summable functions;
* `energy_first_passD`: (4.40) in the form of the planar `energy_first_pass`: if
  `Σ_x u G ≤ E(u) + (2s)^{-1} Σ_x u² + Q s^{α - 3}` (Steps 3-4) on `(τ, t)`, `u(τ) = 0` and
  `∂_s u = Δ u + G`, then `Σ_x u(t)² ≤ 2Q/(3 - α) (t/τ) τ^{α - 2}`; on `ℤ^d` it is applied with
  `α - 3 = α_0 - d/2 - 2`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-- The energy `E(v) = Σ_x Σ_i a_i(x) (v(x + e_i) - v(x))²` of the open graph. -/
noncomputable def openEnergyD (ω : Configuration d) (v : Vertex d → ℝ) : ℝ :=
  ∑' x, ∑ i, openCondD ω i x * (v (x + Pi.single i 1) - v x) ^ 2

theorem summable_mul_of_sqD {f g : Vertex d → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => f x * g x := by
  refine Summable.of_norm_bounded ((hf.add hg).div_const 2) fun x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]

theorem summable_sq_subD {f g : Vertex d → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => (f x - g x) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) ((hf.add hg).mul_left 2)
  nlinarith [sq_nonneg (f x + g x)]

theorem summable_sq_addD {f g : Vertex d → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : Summable fun x => (f x + g x) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) ((hf.add hg).mul_left 2)
  nlinarith [sq_nonneg (f x - g x)]

theorem summable_sq_add_shiftD {f : Vertex d → ℝ} (hf : Summable fun x => f x ^ 2)
    (a : Vertex d) : Summable fun x => f (x + a) ^ 2 :=
  hf.comp_injective (add_left_injective a)

theorem summable_sq_sub_shiftD {f : Vertex d → ℝ} (hf : Summable fun x => f x ^ 2)
    (a : Vertex d) : Summable fun x => f (x - a) ^ 2 :=
  hf.comp_injective (sub_left_injective (b := a))

theorem summable_mul_mul_of_abs_leD {c A B : Vertex d → ℝ} (hc : ∀ x, |c x| ≤ 1)
    (h : Summable fun x => A x * B x) : Summable fun x => c x * A x * B x := by
  refine Summable.of_norm_bounded h.abs fun x => ?_
  rw [Real.norm_eq_abs, mul_assoc, abs_mul]
  calc |c x| * |A x * B x| ≤ 1 * |A x * B x| := mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)
    _ = |A x * B x| := one_mul _

theorem sq_le_sq_of_abs_leD {v w : ℝ} (h : |v| ≤ w) : v ^ 2 ≤ w ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **Discrete integration by parts on `ℤ^d`** for the Laplacian of the open graph and square
summable functions. -/
theorem tsum_openLaplacian_mulD (ω : Configuration d) {u φ : Vertex d → ℝ}
    (hu : Summable fun x => u x ^ 2) (hφ : Summable fun x => φ x ^ 2) :
    ∑' x, openLaplacian ω u x * φ x =
      -∑' x, ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) *
        (φ (x + Pi.single i 1) - φ x) := by
  have hP : ∀ i : Fin d,
      Summable fun x => openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ x :=
    fun i => summable_mul_mul_of_abs_leD (abs_openCondD_le ω i)
      (summable_mul_of_sqD (summable_sq_subD (summable_sq_add_shiftD hu (Pi.single i 1)) hu) hφ)
  have hM : ∀ i : Fin d, Summable fun x =>
      openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) * φ x :=
    fun i => summable_mul_mul_of_abs_leD (fun x => abs_openCondD_le ω i _)
      (summable_mul_of_sqD (summable_sq_subD (summable_sq_sub_shiftD hu (Pi.single i 1)) hu) hφ)
  have hP' : ∀ i : Fin d, Summable fun x =>
      openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ (x + Pi.single i 1) :=
    fun i => summable_mul_mul_of_abs_leD (abs_openCondD_le ω i)
      (summable_mul_of_sqD (summable_sq_subD (summable_sq_add_shiftD hu (Pi.single i 1)) hu)
        (summable_sq_add_shiftD hφ (Pi.single i 1)))
  have hshift : ∀ i : Fin d,
      ∑' x, openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) * φ x =
        ∑' x, -(openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ (x + Pi.single i 1)) := by
    intro i
    rw [← (Equiv.addRight (Pi.single i 1 : Vertex d)).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  have hterm : ∀ i : Fin d,
      ∑' x, openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ x +
        ∑' x, openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) * φ x =
      -∑' x, openCondD ω i x * (u (x + Pi.single i 1) - u x) *
        (φ (x + Pi.single i 1) - φ x) := by
    intro i
    rw [hshift i, ← (hP i).tsum_add (hP' i).neg, ← tsum_neg]
    refine tsum_congr fun x => ?_
    ring
  have hsum : ∀ i ∈ (Finset.univ : Finset (Fin d)), Summable fun x =>
      openCondD ω i x * (u (x + Pi.single i 1) - u x) * (φ (x + Pi.single i 1) - φ x) :=
    fun i _ => summable_mul_mul_of_abs_leD (abs_openCondD_le ω i)
      (summable_mul_of_sqD (summable_sq_subD (summable_sq_add_shiftD hu (Pi.single i 1)) hu)
        (summable_sq_subD (summable_sq_add_shiftD hφ (Pi.single i 1)) hφ))
  calc ∑' x, openLaplacian ω u x * φ x
      = ∑' x, ∑ i, (openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ x +
          openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) * φ x) := by
        refine tsum_congr fun x => ?_
        rw [openLaplacian_eq_sumD, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i, (∑' x, openCondD ω i x * (u (x + Pi.single i 1) - u x) * φ x +
          ∑' x, openCondD ω i (x - Pi.single i 1) * (u (x - Pi.single i 1) - u x) * φ x) := by
        rw [Summable.tsum_finsetSum fun i _ => (hP i).add (hM i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hP i).tsum_add (hM i)
    _ = ∑ i, -∑' x, openCondD ω i x * (u (x + Pi.single i 1) - u x) *
          (φ (x + Pi.single i 1) - φ x) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = -∑' x, ∑ i, openCondD ω i x * (u (x + Pi.single i 1) - u x) *
          (φ (x + Pi.single i 1) - φ x) := by
        rw [Finset.sum_neg_distrib, Summable.tsum_finsetSum hsum]

/-- `Σ_x (Δ u)(x) u(x) = -E(u)`. -/
theorem tsum_openLaplacian_mul_selfD (ω : Configuration d) {u : Vertex d → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    ∑' x, openLaplacian ω u x * u x = -openEnergyD ω u := by
  rw [tsum_openLaplacian_mulD ω hu hu, openEnergyD]
  congr 1
  exact tsum_congr fun x => Finset.sum_congr rfl fun i _ => by ring

theorem summable_sq_openLaplacianD (ω : Configuration d) {w : Vertex d → ℝ}
    (hw : Summable fun x => w x ^ 2) : Summable fun x => openLaplacian ω w x ^ 2 := by
  have hs : ∀ i : Fin d, Summable fun x => (openCondD ω i x * (w (x + Pi.single i 1) - w x) +
      openCondD ω i (x - Pi.single i 1) * (w (x - Pi.single i 1) - w x)) ^ 2 := by
    intro i
    refine summable_sq_addD ?_ ?_
    · refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
        (summable_sq_subD (summable_sq_add_shiftD hw (Pi.single i 1)) hw)
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by
        rw [openCondD_sq]; exact (le_abs_self _).trans (abs_openCondD_le ω i x))
    · refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
        (summable_sq_subD (summable_sq_sub_shiftD hw (Pi.single i 1)) hw)
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by
        rw [openCondD_sq]; exact (le_abs_self _).trans (abs_openCondD_le ω i _))
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    ((summable_sum fun i (_ : i ∈ Finset.univ) => hs i).mul_left (d : ℝ))
  rw [openLaplacian_eq_sumD]
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i => openCondD ω i x * (w (x + Pi.single i 1) - w x) +
      openCondD ω i (x - Pi.single i 1) * (w (x - Pi.single i 1) - w x))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem openEnergyD_nonneg (ω : Configuration d) (v : Vertex d → ℝ) : 0 ≤ openEnergyD ω v :=
  tsum_nonneg fun x => Finset.sum_nonneg fun i _ =>
    mul_nonneg (openCondD_nonneg ω i x) (sq_nonneg _)

/-- **Differentiation of the energy under the sum**: if `|u| ≤ D` and `|∂_s u| ≤ D'` on
`(a, b) × ℤ^d` with `D, D'` square summable, then `∂_s Σ_x u² = Σ_x 2 u ∂_s u` on `(a, b)`. -/
theorem hasDerivAt_tsum_sqD {u u' : ℝ → Vertex d → ℝ} {a b s : ℝ} {D D' : Vertex d → ℝ}
    (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ r ∈ Set.Ioo a b, ∀ x, |u r x| ≤ D x)
    (hu' : ∀ r ∈ Set.Ioo a b, ∀ x, |u' r x| ≤ D' x)
    (hdu : ∀ r ∈ Set.Ioo a b, ∀ x, HasDerivAt (fun r => u r x) (u' r x) r)
    (hs : s ∈ Set.Ioo a b) :
    HasDerivAt (fun r => ∑' x, u r x ^ 2) (∑' x, 2 * u s x * u' s x) s := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun x => D x ^ 2 + D' x ^ 2) (hD.add hD')
    isOpen_Ioo isPreconnected_Ioo (g := fun x r => u r x ^ 2)
    (g' := fun x r => 2 * u r x * u' r x) (fun x r hr => ?_) (fun x r hr => ?_) hs ?_ hs
  · exact ((hdu r hr x).pow 2).congr_deriv (by norm_num)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
    have h2 := hu r hr x
    have h4 := hu' r hr x
    have hDx : 0 ≤ D x := (abs_nonneg _).trans h2
    have hD'x : 0 ≤ D' x := (abs_nonneg _).trans h4
    have k := mul_le_mul h2 h4 (abs_nonneg _) hDx
    nlinarith [sq_nonneg (D x - D' x)]
  · exact Summable.of_nonneg_of_le (fun x => sq_nonneg _)
      (fun x => sq_le_sq_of_abs_leD (hu s hs x)) hD

/-- **The first pass of Step 5** (`ψ = 1`, (4.40) of Dario–Gu) on `ℤ^d`. -/
theorem energy_first_passD (ω : Configuration d) {u G : ℝ → Vertex d → ℝ} {τ t Q α : ℝ}
    {D D' : Vertex d → ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) (hQ : 0 ≤ Q) (hα : α < 3)
    (hD : Summable fun x => D x ^ 2) (hD' : Summable fun x => D' x ^ 2)
    (hu : ∀ s ∈ Set.Ioo τ t, ∀ x, |u s x| ≤ D x)
    (hu' : ∀ s ∈ Set.Ioo τ t, ∀ x, |openLaplacian ω (u s) x + G s x| ≤ D' x)
    (hdu : ∀ s ∈ Set.Ioo τ t, ∀ x,
      HasDerivAt (fun s => u s x) (openLaplacian ω (u s) x + G s x) s)
    (hcont : ContinuousOn (fun s => ∑' x, u s x ^ 2) (Set.Icc τ t)) (h0 : ∀ x, u τ x = 0)
    (hsrc : ∀ s ∈ Set.Ioo τ t, ∑' x, u s x * G s x ≤ openEnergyD ω (u s) +
      1 / (2 * s) * ∑' x, u s x ^ 2 + Q * s ^ (α - 3)) :
    ∑' x, u t x ^ 2 ≤ 2 * Q / (3 - α) * (t / τ) * τ ^ (α - 2) := by
  have hstep : ∀ r ∈ Set.Ioo τ t, ∃ E' : ℝ,
      HasDerivAt (fun s => ∑' x, u s x ^ 2) E' r ∧
        E' ≤ (∑' x, u r x ^ 2) / r + 2 * Q * r ^ (α - 3) := by
    intro r hr
    have hr0 : 0 < r := hτ.trans hr.1
    refine ⟨_, hasDerivAt_tsum_sqD hD hD' hu hu' hdu hr, ?_⟩
    have hw : Summable fun x => u r x ^ 2 :=
      Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => sq_le_sq_of_abs_leD (hu r hr x))
        hD
    have hLG : Summable fun x => (openLaplacian ω (u r) x + G r x) ^ 2 :=
      Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => sq_le_sq_of_abs_leD (hu' r hr x))
        hD'
    have hG : Summable fun x => G r x ^ 2 :=
      (summable_sq_subD hLG (summable_sq_openLaplacianD ω hw)).congr fun x => by ring
    have hL := summable_sq_openLaplacianD ω hw
    have s1 : Summable fun x => openLaplacian ω (u r) x * u r x := summable_mul_of_sqD hL hw
    have s2 : Summable fun x => u r x * G r x := summable_mul_of_sqD hw hG
    have e : ∑' x, 2 * u r x * (openLaplacian ω (u r) x + G r x) =
        2 * ∑' x, openLaplacian ω (u r) x * u r x + 2 * ∑' x, u r x * G r x := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← (s1.mul_left 2).tsum_add (s2.mul_left 2)]
      exact tsum_congr fun x => by ring
    rw [e, tsum_openLaplacian_mul_selfD ω hw]
    have h1 := hsrc r hr
    have e2 : 1 / (2 * r) * ∑' x, u r x ^ 2 = (∑' x, u r x ^ 2) / r / 2 := by
      field_simp
    linarith
  choose E' hE' using hstep
  classical
  let E'' : ℝ → ℝ := fun s => if hs : s ∈ Set.Ioo τ t then E' s hs else 0
  exact le_of_hasDerivAt_le_div_add (E := fun s => ∑' x, u s x ^ 2) (E' := E'') hτ hτt
    (by positivity : 0 ≤ 2 * Q) hα hcont
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).1)
    (fun s hs => by simpa only [E'', dif_pos hs] using (hE' s hs).2)
    (by simp [h0])

end Rigidity.Green.GeneralDim
