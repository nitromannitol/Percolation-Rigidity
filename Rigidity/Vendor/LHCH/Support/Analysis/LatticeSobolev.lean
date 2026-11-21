/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Analysis/LatticeSobolev.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import LatticeProb.Site
import Rigidity.Vendor.LHCH.Support.Lattice.Membership
import Mathlib

/-!
# The lattice ℓ¹ Sobolev inequality

For a finitely supported function `v` on `ℤ^d`, `d ≥ 2`, `(Σ_x |v x|^{d/(d−1)})^{(d−1)/d} ≤ Σ_x Σ_j
|v(x+e_j) − v(x)|`, with constant one. Along every line `|v(x)|` is at most the sum of the absolute
gradients on that line, and Mathlib's grid-lines lemma (`lintegral_prod_lintegral_pow_le`) for the
counting measure on `ℤ` gives the Loomis–Whitney step. It is the first step of the weighted Sobolev
inequality (e:weighted-Sobolev), proved here rather than cited from ADS15 (3.13).
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The product of counting measures on `ℤ^d` is the counting measure on `ℤ^d`. -/
theorem pi_count_eq_count :
    MeasureTheory.Measure.pi
      (fun _ : Fin d => (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) =
      MeasureTheory.Measure.count := by
  refine MeasureTheory.Measure.ext_of_singleton fun x => ?_
  simp [MeasureTheory.Measure.pi_singleton]

/-- Telescoping along a line: a real function on `ℤ` that vanishes for large arguments is
bounded at `a` by the sum of its absolute increments to the right of `a`, each bounded
above by `g`. -/
theorem ofReal_abs_le_tsum_of_telescope (h : ℤ → ℝ) (g : ℤ → ENNReal)
    (hh : ∃ N : ℤ, ∀ t, N ≤ t → h t = 0)
    (hg : ∀ t, ENNReal.ofReal |h (t + 1) - h t| ≤ g t) (a : ℤ) :
    ENNReal.ofReal |h a| ≤ ∑' t, g t := by
  obtain ⟨N, hN⟩ := hh
  have step : ∀ n : ℕ, ENNReal.ofReal |h a| ≤
      ENNReal.ofReal |h (a + n)| + ∑ k ∈ Finset.range n, g (a + k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ih.trans ?_
      have hone : ENNReal.ofReal |h (a + n)| ≤
          ENNReal.ofReal |h (a + (n + 1 : ℕ))| + g (a + n) := by
        calc ENNReal.ofReal |h (a + n)|
            ≤ ENNReal.ofReal (|h (a + (n + 1 : ℕ))| + |h (a + (n + 1 : ℕ)) - h (a + n)|) := by
              apply ENNReal.ofReal_le_ofReal
              have := abs_sub_abs_le_abs_sub (h (a + n)) (h (a + (n + 1 : ℕ)))
              rw [abs_sub_comm] at this
              linarith
          _ ≤ ENNReal.ofReal |h (a + (n + 1 : ℕ))|
                + ENNReal.ofReal |h (a + (n + 1 : ℕ)) - h (a + n)| := ENNReal.ofReal_add_le
          _ ≤ _ := by
              gcongr
              have := hg (a + n)
              simpa [add_assoc] using this
      calc ENNReal.ofReal |h (a + n)| + ∑ k ∈ Finset.range n, g (a + k)
          ≤ (ENNReal.ofReal |h (a + (n + 1 : ℕ))| + g (a + n)) + ∑ k ∈ Finset.range n, g (a + k)
            := by gcongr
        _ = _ := by rw [Finset.sum_range_succ]; ring
  have hzero : h (a + ((N - a).toNat : ℕ)) = 0 := by
    apply hN
    have := Int.self_le_toNat (N - a)
    linarith
  refine (step (N - a).toNat).trans ?_
  rw [hzero]
  simp only [ENNReal.ofReal_zero, abs_zero, zero_add]
  calc ∑ k ∈ Finset.range (N - a).toNat, g (a + k)
      ≤ ∑' k : ℕ, g (a + k) := ENNReal.sum_le_tsum _
    _ ≤ ∑' t, g t := ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun k : ℕ => a + (k : ℤ)) (fun k l hkl => by simpa using hkl) g

/-- A function on `ℤ^d` vanishing off a finite set vanishes along each line far enough
in the positive direction. -/
theorem exists_forall_update_eq_zero (S : Finset (Site d)) (v : Site d → ℝ)
    (hv : ∀ x, x ∉ S → v x = 0) (x : Site d) (i : Fin d) :
    ∃ N : ℤ, ∀ t, N ≤ t → v (Function.update x i t) = 0 := by
  obtain ⟨N, hN⟩ := (S.image fun y => y i).bddAbove
  refine ⟨N + 1, fun t ht => hv _ fun hmem => ?_⟩
  have := hN (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, hmem, rfl⟩))
  simp at this
  omega

/-- **The lattice `ℓ¹` Sobolev inequality** (Gagliardo–Nirenberg on `ℤ^d`, constant one): for `v`
vanishing off a finite set `S`,
`(Σ_x |v x|^{d/(d−1)})^{(d−1)/d} ≤ Σ_{x ∈ S'} Σ_j |v(x+e_j) − v(x)|`,
where `S'` contains every `x` at which some gradient `v(x+e_j) − v(x)` is nonzero. -/
theorem sum_rpow_le_sum_abs_grad (hd : 2 ≤ d) (S S' : Finset (Site d)) (v : Site d → ℝ)
    (hv : ∀ x, x ∉ S → v x = 0) (hS' : ∀ x (j : Fin d), v (x + unit j) ≠ v x → x ∈ S') :
    (∑ x ∈ S, |v x| ^ ((d : ℝ) / (d - 1))) ^ (((d : ℝ) - 1) / d) ≤
      ∑ x ∈ S', ∑ j : Fin d, |v (x + unit j) - v x| := by
  classical
  -- the gradient size `F` and the associated `ENNReal`-valued function `f`
  set F : Site d → ℝ := fun x => ∑ j : Fin d, |v (x + unit j) - v x| with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hFS' : ∀ x, x ∉ S' → F x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun j _ => ?_
    have : v (x + unit j) = v x := by
      by_contra h
      exact hx (hS' x j h)
    simp [this]
  set f : Site d → ENNReal := fun x => ENNReal.ofReal (F x) with hf
  -- the line estimate
  have hline : ∀ (x : Site d) (i : Fin d),
      ENNReal.ofReal |v x| ≤ ∑' t : ℤ, f (Function.update x i t) := by
    intro x i
    have := ofReal_abs_le_tsum_of_telescope (fun t => v (Function.update x i t))
      (fun t => f (Function.update x i t)) (exists_forall_update_eq_zero S v hv x i) ?_ (x i)
    · simpa using this
    · intro t
      simp only [hf]
      apply ENNReal.ofReal_le_ofReal
      rw [← update_add_unit]
      exact Finset.single_le_sum (f := fun j => |v (Function.update x i t + unit j)
        - v (Function.update x i t)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  -- exponents
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  set p : ℝ := (d : ℝ) / (d - 1) with hp
  have hp0 : 0 < p := div_pos (by linarith) hd2
  have hpq : (1 : ℝ) / ((d : ℝ) - 1) * d = p := by rw [hp]; field_simp
  have hconj : Real.HolderConjugate (Fintype.card (Fin d) : ℝ) p := by
    rw [Real.holderConjugate_iff]
    refine ⟨by simpa using hd1, ?_⟩
    rw [Fintype.card_fin, hp]
    field_simp
    ring
  -- pointwise bound by the product of the line sums
  have hpt : ∀ x : Site d, ENNReal.ofReal |v x| ^ p ≤
      ∏ i : Fin d, (∑' t : ℤ, f (Function.update x i t)) ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
    intro x
    calc ENNReal.ofReal |v x| ^ p
        = ∏ _i : Fin d, ENNReal.ofReal |v x| ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_mul, hpq]
      _ ≤ _ := by
          gcongr with i
          exact hline x i
  -- the grid-lines inequality for the counting measure
  have hmeas : Measurable f := measurable_of_countable f
  have key := MeasureTheory.lintegral_prod_lintegral_pow_le
    (fun _ : Fin d => (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) hconj hmeas
  simp only [Fintype.card_fin, MeasureTheory.lintegral_count, pi_count_eq_count] at key
  -- evaluate both sides of the grid-lines inequality
  have hG0 : 0 ≤ ∑ x ∈ S', F x := Finset.sum_nonneg fun x _ => hF0 x
  have hright : ∑' x : Site d, f x = ENNReal.ofReal (∑ x ∈ S', F x) := by
    rw [tsum_eq_sum (s := S'), ENNReal.ofReal_sum_of_nonneg fun x _ => hF0 x]
    intro x hx
    simp [hf, hFS' x hx]
  have hleft : ENNReal.ofReal (∑ x ∈ S, |v x| ^ p) = ∑' x : Site d, ENNReal.ofReal |v x| ^ p := by
    rw [tsum_eq_sum (s := S), ENNReal.ofReal_sum_of_nonneg fun x _ => by positivity]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
    · intro x hx
      simp [hv x hx, hp0]
  have hmain : ∑ x ∈ S, |v x| ^ p ≤ (∑ x ∈ S', F x) ^ p := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), hleft,
      ← ENNReal.ofReal_rpow_of_nonneg hG0 hp0.le, ← hright]
    exact (ENNReal.tsum_le_tsum hpt).trans key
  calc (∑ x ∈ S, |v x| ^ p) ^ (((d : ℝ) - 1) / d)
      ≤ ((∑ x ∈ S', F x) ^ p) ^ (((d : ℝ) - 1) / d) :=
        Real.rpow_le_rpow (by positivity) hmain (by positivity)
    _ = ∑ x ∈ S', F x := by
        rw [show ((d : ℝ) - 1) / d = p⁻¹ by rw [hp, inv_div]]
        exact Real.rpow_rpow_inv hG0 hp0.ne'

end LatticeHC

end
