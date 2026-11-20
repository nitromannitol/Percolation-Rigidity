import Rigidity.Percolation.SlabTriadicRadius
import Rigidity.Percolation.TriadicOverlapDecay

/-!
# Slab estimates at triadic overlap scales

The slab crossing and coalescence bounds apply uniformly to the ambient cube,
its test cubes, and their overlap cubes once the ambient scale is large enough.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External Filter
open scoped ENNReal

/-- A cube whose side lies between one tenth and all of the ambient side fits
the common slab scale used for crossing and path coalescence. -/
theorem triadic_overlap_slab_scale (d S A : ℕ) (hd : 0 < d) (hS : 160 ≤ S)
    (hlower : S ≤ 10 * A) (hupper : A ≤ S) :
    let t := S / 40 - 1
    0 < t ∧ 8 * t < 10 * d * A ∧ A ≤ 10 * (8 * t) ∧
      2 * (t : ℤ) ≤ ((S / 20 : ℕ) : ℤ) - 1 ∧ S ≤ 80 * t := by
  let q := S / 40
  let t := q - 1
  have hq : 4 ≤ q := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 40)).2
    omega
  have ht : t + 1 = q := Nat.sub_add_cancel (by omega)
  have hdiv := Nat.mod_add_div S 40
  have hmod := Nat.mod_lt S (by omega : 0 < 40)
  have hSbound : S ≤ 80 * t := by dsimp only [t, q] at *; omega
  have h8 : 8 * t < S := by dsimp only [t, q] at *; omega
  have hq20 : 2 * t + 1 ≤ S / 20 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 20)).2
    dsimp only [t, q] at *
    omega
  have hq20' : ((2 * t + 1 : ℕ) : ℤ) ≤ ((S / 20 : ℕ) : ℤ) := by exact_mod_cast hq20
  have hdiam : 2 * (t : ℤ) ≤ ((S / 20 : ℕ) : ℤ) - 1 := by push_cast at hq20'; omega
  refine ⟨by omega, ?_, ?_, hdiam, hSbound⟩
  · nlinarith
  · omega

/-- Uniform full-slab two-point bounds imply the three crossing and coalescence
estimates used in the triadic overlap argument at every sufficiently large scale. -/
theorem TriadicCube.eventually_overlap_estimates_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hslab : ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) :
    ∃ M : ℕ, ∀ Q : TriadicCube d, M ≤ 3 ^ Q.scale →
      let S : ℕ := 3 ^ Q.scale
      let rate := (c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2
      let err := ENNReal.ofReal (Real.exp (-(rate / 40) * (S : ℝ)))
      (latticeBondLaw d p) {ω | ¬ HasCrossingComponent ω Q.vertices
          (fun a => ↑(Q.toIntegerCube.lowerFace a)) (fun a => ↑(Q.toIntegerCube.upperFace a)) ∨
        ¬ LargePathsCoalesce ω Q.vertices (pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1))} ≤ err ∧
      (∀ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
        (latticeBondLaw d p) {ω | ¬ CrossableRegion ω (↑R.vertices)
            (fun a => ↑(R.lowerFace a)) (fun a => ↑(R.upperFace a)) ∨
          ¬ LargePathsCoalesce ω (↑R.vertices) (pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1))} ≤ err) ∧
      ∀ T : IntegerCube d, T.size = S / 20 →
        (latticeBondLaw d p) {ω | ¬ HasCrossingComponent ω (↑T.vertices)
          (fun a => ↑(T.lowerFace a)) (fun a => ↑(T.upperFace a))} ≤ err := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_crossing_and_diameter_coalescence_le_of_twoPoint_slabs hd j i hij width 10
      hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo)
  obtain ⟨L, hL⟩ := eventually_measure_no_crossingComponent_le_exp_of_twoPoint_slabs
    hd j i hij width hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo
  refine ⟨max 160 (max (40 * (N + 1)) (40 * L)), ?_⟩
  intro Q hlarge
  let S := 3 ^ Q.scale
  let t := S / 40 - 1
  let rate : ℝ := (c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hS : 160 ≤ S := le_trans (le_max_left _ _) hlarge
  have hSN : 40 * (N + 1) ≤ S :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlarge
  have hSL : 40 * L ≤ S :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlarge
  have ht : N ≤ t := by
    have hdiv : N + 1 ≤ S / 40 := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    dsimp only [t]
    omega
  have hLsize : L ≤ S / 20 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 20)).2
    omega
  have hdiv20 := Nat.mod_add_div S 20
  have hmod20 := Nat.mod_lt S (by omega : 0 < 20)
  have hq20 : 1 ≤ S / 20 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 20)).2
    omega
  have hS20 : S ≤ 40 * (S / 20) := by omega
  have hgeom := triadic_overlap_slab_scale d S S hd hS (by omega) le_rfl
  have hS80 : S ≤ 80 * t := hgeom.2.2.2.2
  have hS80' : (S : ℝ) ≤ 80 * (t : ℝ) := by exact_mod_cast hS80
  have hexp : ENNReal.ofReal (Real.exp (-(rate * ((8 * t : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-(rate / 40) * (S : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hverts : (↑Q.toIntegerCube.vertices : Set (Vertex d)) = Q.vertices := by
    ext x
    exact Q.mem_toIntegerCube_vertices x
  have hQpos : 1 ≤ Q.toIntegerCube.size := by change 1 ≤ S; omega
  have hQfit : 8 * t < 10 * d * Q.toIntegerCube.size := by
    change 8 * t < 10 * d * S
    exact hgeom.2.1
  have hQcomp : Q.toIntegerCube.size ≤ 10 * (8 * t) := by
    change S ≤ 10 * (8 * t)
    exact hgeom.2.2.1
  have hQmain := hN t ht Q.toIntegerCube (((S / 20 : ℕ) : ℤ) - 1)
    hQpos hQfit hQcomp hgeom.2.2.2.1 (hslab Q.toIntegerCube)
  have hQbound : (latticeBondLaw d p) {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun a => ↑(Q.toIntegerCube.lowerFace a)) (fun a => ↑(Q.toIntegerCube.upperFace a)) ∨
      ¬ LargePathsCoalesce ω Q.vertices (pathDiameterAtLeast (((S / 20 : ℕ) : ℤ) - 1))} ≤
      ENNReal.ofReal (Real.exp (-(rate / 40) * (S : ℝ))) := by
    rw [hverts] at hQmain
    exact hQmain.trans hexp
  refine ⟨hQbound, ?_, ?_⟩
  · intro R hR
    have hside : Q.side = (S : ℤ) := by simp only [TriadicCube.side, S, Nat.cast_pow, Nat.cast_ofNat]
    have hlow' := hR.1
    have hhigh' := hR.2.1
    rw [hside] at hlow' hhigh'
    have hlow : S ≤ 10 * R.size := by exact_mod_cast hlow'
    have hhigh : R.size ≤ S := by
      have h : 2 * R.size ≤ S := by exact_mod_cast hhigh'
      omega
    have hparam := triadic_overlap_slab_scale d S R.size hd hS hlow hhigh
    have hRpos : 1 ≤ R.size := by omega
    have hRmain := hN t ht R (((S / 20 : ℕ) : ℤ) - 1)
      hRpos hparam.2.1 hparam.2.2.1 hparam.2.2.2.1 (hslab R)
    apply (measure_mono ?_).trans (hRmain.trans hexp)
    intro ω hbad
    rcases hbad with hbad | hbad
    · exact Or.inl (fun hcross => hbad hcross.crossableRegion)
    · exact Or.inr hbad
  · intro T hTsize
    have hTbound := hL T (by omega) (hslab T)
    apply hTbound.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hS20' : (S : ℝ) ≤ 40 * ((S / 20 : ℕ) : ℝ) := by exact_mod_cast hS20
    rw [hTsize]
    change -(rate * ((S / 20 : ℕ) : ℝ)) ≤ -(rate / 40) * (S : ℝ)
    nlinarith

/-- Uniform two-point connectivity in all complete cube slabs implies an
eventual exponential bound for failure of triadic well-connectedness in the
three-quarter interior. -/
theorem TriadicCube.eventually_measure_not_wellConnectedIn_threeQuarter_le_of_twoPoint_slabs
    {d : ℕ} (hd : 0 < d) (j i : Fin d) (hij : i ≠ j)
    (width : ℕ) (hwidth : 0 < width) (p : unitInterval) (ρ c : ℝ)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hslab : ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) :
    ∃ M : ℕ, ∀ Q : TriadicCube d, M ≤ 3 ^ Q.scale →
      let rate : ℝ := ((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 40
      (latticeBondLaw d p) {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        ENNReal.ofReal ((1 + 4 * 7 ^ d * ((d + 1).factorial : ℝ) /
          (rate / 2) ^ (d + 1)) * Real.exp (-(rate / 2) * (3 : ℝ) ^ Q.scale)) := by
  obtain ⟨M, hM⟩ := TriadicCube.eventually_overlap_estimates_of_twoPoint_slabs hd j i hij
    width hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo hslab
  refine ⟨max 160 M, ?_⟩
  intro Q hlarge
  have hsize : 160 ≤ 3 ^ Q.scale := le_trans (le_max_left _ _) hlarge
  have hMsize : M ≤ 3 ^ Q.scale := le_trans (le_max_right _ _) hlarge
  have hside : 2 ≤ Q.side := by
    have hsize' : (160 : ℤ) ≤ ((3 ^ Q.scale : ℕ) : ℤ) := by exact_mod_cast hsize
    change 2 ≤ (3 : ℤ) ^ Q.scale
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hsize'
    omega
  have hk : 0 < 3 ^ Q.scale / 20 := by
    apply Nat.div_pos
    · omega
    · omega
  let rate : ℝ := ((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 40
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  obtain ⟨hQ, htest, hoverlap⟩ := hM Q hMsize
  refine (Q.measure_not_wellConnectedIn_threeQuarter_le_exp hd hside hk (latticeBondLaw d p)
    1 rate (by norm_num) hrate ?_ ?_ ?_).trans_eq ?_
  · simpa only [one_mul, rate, Nat.cast_pow, Nat.cast_ofNat] using hQ
  · intro R hR
    simpa only [one_mul, rate, Nat.cast_pow, Nat.cast_ofNat] using htest R hR
  · intro T hTsize _
    simpa only [one_mul, rate, Nat.cast_pow, Nat.cast_ofNat] using hoverlap T hTsize
  · simp only [one_mul, rate]

end Rigidity.Percolation
