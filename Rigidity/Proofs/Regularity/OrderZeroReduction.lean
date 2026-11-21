import Rigidity.Proofs.Regularity.OrderZeroLiouville
import Rigidity.Proofs.Regularity.InfiniteClusterBalls
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# The order-zero regularity of Armstrong–Dario from harmonic approximation

Armstrong and Dario (arXiv:1609.09431v2) derive the order-zero regularity (Theorem 2 (iii), `k = 0`)
from the harmonic approximation of Lemma 7.1 and the iteration of Lemma 7.2. In the cluster-ball
form of `Rigidity.Proofs.Regularity.InfiniteClusterBalls`, the harmonic approximation is the
statement `OrderZeroHarmonicApproximation`: above a minimal scale `X ≤ O_s(θ)`, every function `u`
harmonic in `C_∞ ∩ B_R(0)` is close, on the cluster balls of radii in `[X, R / A]`, to a class
`Abar` of functions with the excess decay of order one, in the form of the hypothesis of Lemma 7.2
with `R E ≤ K ‖u‖_{L̲²(B_R)}`.

`armstrongDarioOrderZero_of_harmonicApproximation` proves the order-zero input
`LatticeProb.External.ArmstrongDarioOrderZero` from `OrderZeroHarmonicApproximation` and the almost
sure uniqueness of the infinite cluster, through the order-zero decay with constants
(`armstrongDario_orderZero_origin_infiniteCluster`, which uses the proved density concentration
of Dario–Gu) and the Liouville argument of `Rigidity.Proofs.Regularity.OrderZeroLiouville`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- The harmonic approximation of order zero on the balls of the infinite cluster centred at `0`,
above a minimal scale with stretched exponential moments. -/
def OrderZeroHarmonicApproximation : Prop :=
  ∀ (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ A α CH K : ℝ), 0 < s ∧ 0 < θ ∧ 2 ≤ A ∧ 0 < α ∧ 0 ≤ CH ∧ 0 ≤ K ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, A * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∃ (Abar : ℝ → Set (uniqueInfiniteComponent h → ℝ)) (E : ℝ), 0 ≤ E ∧
            R * E ≤ K * componentBallL2 (uniqueInfiniteComponent h) 0 R u ∧
            HarmonicRegularity (componentBallSeminorm (uniqueInfiniteComponent h) 0) Abar
              (clusterAffine (uniqueInfiniteComponent h)) 1 (X ω) R CH ∧
            (∀ r : ℝ, X ω ≤ r → r ≤ R / A → (Abar r).Nonempty) ∧
            HarmonicApproximation (componentBallSeminorm (uniqueInfiniteComponent h) 0) Abar
              (clusterConstants (uniqueInfiniteComponent h)) A α (X ω) R E u

variable {F : Type*} [AddCommGroup F]

theorem HarmonicApproximation.of_le (N : ℝ → AddGroupSeminorm F) {Abar : ℝ → Set F}
    {P₀ : AddSubgroup F} {A α X X' R E : ℝ} {u : F}
    (h : HarmonicApproximation N Abar P₀ A α X R E u) (hX : X ≤ X') :
    HarmonicApproximation N Abar P₀ A α X' R E u :=
  fun r hr hrR => h r (hX.trans hr) hrR

/-- **The order-zero regularity input of Armstrong–Dario** (`ArmstrongDarioOrderZero`) from the
harmonic approximation of order zero and the almost sure uniqueness of the infinite cluster. -/
theorem armstrongDarioOrderZero_of_harmonicApproximation
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hHA : OrderZeroHarmonicApproximation) : LatticeProb.External.ArmstrongDarioOrderZero := by
  apply armstrongDarioOrderZero_of_decay
  intro d _ hd p hpc hp1
  obtain ⟨s₁, θ₁, A, α, CH, K, hs₁, hθ₁, hA, hα, hCH, hK, X₁, hX₁m, hX₁0, hX₁os, hX₁ae⟩ :=
    hHA d hd p hpc hp1
  obtain ⟨s₂, C₀, C₂, hs₂, hC₀, hC₂, hgeo⟩ :=
    armstrongDario_orderZero_origin_infiniteCluster hd p hpc hp1 hA hα hCH
  obtain ⟨M, hMm, hM0, hMos, hMae⟩ := hgeo 0
  have hA0 : 0 < A := by linarith
  set s := min s₁ s₂ with hsdef
  have hs : 0 < s := lt_min hs₁ hs₂
  have h1 := IsOsBond.mono_exponent hs (min_le_left _ _) hX₁m hX₁os
  have h2 := IsOsBond.mono_exponent hs (min_le_right _ _) hMm hMos
  have h12 := IsOsBond.max hs (by positivity) (by positivity) hX₁m hMm h1 h2
  set c₁ := max C₂ 1 with hc₁
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h3 := isOsBond_const (p := p) (d := d) hc₁0 hs
  have h123 := IsOsBond.max hs (by positivity) (by positivity) (hX₁m.max hMm) measurable_const
    h12 h3
  have hY := IsOsBond.const_mul hA0 h123
  set Z : Configuration d → ℝ := fun ω => max (max (X₁ ω) (M ω)) c₁ with hZ
  set θY := A * (max (max (θ₁ * 6 ^ (1 / s)) (C₀ * 6 ^ (1 / s)) * 4 ^ (1 / s))
    (c₁ * 3 ^ (1 / s)) * 4 ^ (1 / s)) with hθY
  have hθY0 : 0 < θY := by positivity
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => hc₁0.le.trans (le_max_right _ _)
  obtain ⟨hint, hle⟩ := hY
  have e : (fun ω => Real.exp (Real.rpow (max (A * Z ω / θY) 0) s)) =
      fun ω => Real.exp (Real.rpow (A * Z ω / θY) s) := by
    funext ω
    rw [max_eq_left (div_nonneg (mul_nonneg hA0.le (hZ0 ω)) hθY0.le)]
  have hK1 : 0 < 1 + K := by linarith
  refine ⟨s, θY, C₂ * (1 + K), hs, hθY0, by positivity, fun ω => A * Z ω,
    ((hX₁m.max hMm).max measurable_const).const_mul A, fun ω => mul_nonneg hA0.le (hZ0 ω),
    by rw [← e]; exact hint, by rw [← e]; exact hle, ?_⟩
  have hUae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ uniqueInfiniteComponentEvent d :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent d).nullMeasurableSet).2
      (by rw [measure_univ]; exact hUq.2 d hd p hpc hp1)
  filter_upwards [hUae, hX₁ae, hMae] with ω hU hω₁ hω₂
  refine ⟨hU, fun h' R hR u hu => ?_⟩
  have hZ1 : 1 ≤ Z ω := (le_max_right _ _).trans (le_max_right _ _)
  have hXZ : X₁ ω ≤ Z ω := (le_max_left _ _).trans (le_max_left _ _)
  have hMZ : M ω ≤ Z ω := (le_max_right _ _).trans (le_max_left _ _)
  have hCZ : C₂ ≤ Z ω := (le_max_left _ _).trans (le_max_right _ _)
  have hR' : 2 * (A * Z ω) ≤ R := hR
  have hAZ : A * Z ω ≤ R := by nlinarith [hZ0 ω]
  have hAX : A * X₁ ω ≤ R := (mul_le_mul_of_nonneg_left hXZ hA0.le).trans hAZ
  have hZR : Z ω ≤ R / A := by rw [le_div_iff₀ hA0]; linarith
  have hR0 : 0 ≤ R := le_trans (mul_nonneg hA0.le (hZ0 ω)) hAZ
  obtain ⟨Abar, E, hE, hRE, hreg, hne, happ⟩ := hω₁ h' R hAX u hu
  have hN0 := componentBallL2_nonneg (uniqueInfiniteComponent h') 0 R u
  by_cases hN : componentBallL2 (uniqueInfiniteComponent h') 0 R u = 0
  · refine ⟨0, fun r hr hrR => ?_⟩
    have hz := (componentBallL2_eq_zero_iff (uniqueInfiniteComponent h') 0 R u).1 hN
    have hr0 : componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => (0 : ℝ)) = 0 := by
      rw [componentBallL2_eq_zero_iff]
      intro x hx
      have hxR : x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R :=
        componentEuclideanBall_mono (uniqueInfiniteComponent h') 0 (by linarith) hx
      simp [hz x hxR]
    rw [hr0, hN, mul_zero]
  · have hNpos : 0 < componentBallL2 (uniqueInfiniteComponent h') 0 R u :=
      lt_of_le_of_ne hN0 (Ne.symm hN)
    have hB : 0 < (1 + K) * componentBallL2 (uniqueInfiniteComponent h') 0 R u :=
      mul_pos hK1 hNpos
    have hBu : ballExcess (componentBallSeminorm (uniqueInfiniteComponent h') 0)
        (clusterConstants (uniqueInfiniteComponent h')) R u + R * E ≤
        (1 + K) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by
      have := ballExcess_le_self (componentBallSeminorm (uniqueInfiniteComponent h') 0)
        (clusterConstants (uniqueInfiniteComponent h')) R u
      rw [componentBallSeminorm_apply] at this
      linarith
    obtain ⟨φ, ⟨c, hc⟩, hφ⟩ := hω₂ h' Abar R (Z ω) E u hZ1 hMZ hZR hE
      (hreg.of_le _ hXZ) (fun r hr hrR => hne r (hXZ.trans hr) hrR) (happ.of_le _ hXZ)
      _ hB hBu
    have hφc : φ = fun _ => c := funext hc
    refine ⟨c, fun r hr hrR => ?_⟩
    have hr' : A * Z ω ≤ r := hr
    have hZr : Z ω ≤ r := by nlinarith [hZ0 ω]
    have := hφ r (max_le hZr (hCZ.trans hZr)) hrR
    rw [hφc] at this
    calc componentBallL2 (uniqueInfiniteComponent h') 0 r (u - fun _ => c)
        ≤ C₂ * (r / R) * ((1 + K) * componentBallL2 (uniqueInfiniteComponent h') 0 R u) := this
      _ = C₂ * (1 + K) * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u := by ring

end Rigidity.Proofs.Regularity
