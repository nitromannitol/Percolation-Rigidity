import Rigidity.Percolation.SlabCrossingLargePaths
import Rigidity.Percolation.PisztoraDiameter

/-!
# Slab connectivity and radius-based path estimates

The cube-crossing bound for paths of large coordinate diameter also bounds the
radius-based event used in the percolation crossing estimates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Full-slab two-point connectivity bounds failure of the cube-crossing
component that connects every path above a prescribed lattice-radius scale. -/
theorem IntegerCube.measureReal_no_crossing_connecting_radius_le_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j)
    (width k₀ N radius : ℕ) (hwidth : 0 < width) (hstart : 0 < k₀ * width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (hradius : 10 * d * ((N + 1) * width - 1) ≤ radius)
    (p : unitInterval) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hprob : ∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
        (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
      ((1 - ρ) ^ (Q.size / width) +
        ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N) +
      ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (Q.measureReal_no_crossing_connecting_paths_le_of_twoPoint_slabs j i hij width k₀ N
      hwidth hstart hsize p ρ hρ hρ₁ hprob)
  intro ω hfail hdiam
  have hpos : 0 < (N + 1) * width := Nat.mul_pos (by omega) hwidth
  have hcast : (((N + 1) * width - 1 : ℕ) : ℤ) + 1 =
      (((N + 1) * width : ℕ) : ℤ) := by
    have h := Nat.sub_add_cancel (show 1 ≤ (N + 1) * width by omega)
    exact_mod_cast h
  apply hfail
  apply HasCrossingComponentConnectingPaths.of_coordinate_diameter hd radius
    ((N + 1) * width - 1) hradius
  simpa only [hcast] using hdiam

/-- A geometric factor with success probability at least `c` is bounded by
an exponential at every earlier integer scale. -/
theorem one_sub_pow_le_exp_neg_mul {α c : ℝ} {m n : ℕ}
    (hc : 0 ≤ c) (hca : c ≤ α) (ha : α ≤ 1) (hnm : n ≤ m) :
    (1 - α) ^ m ≤ Real.exp (-(c * n)) := by
  have hc₁ : c ≤ 1 := hca.trans ha
  have hbase : 1 - α ≤ 1 - c := sub_le_sub_left hca 1
  have hexp : 1 - c ≤ Real.exp (-c) := Real.one_sub_le_exp_neg c
  calc
    (1 - α) ^ m ≤ (1 - c) ^ m := pow_le_pow_left₀ (sub_nonneg.mpr ha) hbase m
    _ ≤ Real.exp (-c) ^ m := pow_le_pow_left₀ (sub_nonneg.mpr hc₁) hexp m
    _ = Real.exp (-((m : ℝ) * c)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(c * n)) := by
      apply Real.exp_le_exp.mpr
      have hmn : (n : ℝ) ≤ m := by exact_mod_cast hnm
      nlinarith

/-- Under uniform full-slab two-point connectivity, a common positive rate
bounds the radius-based crossing failure by an exponential times a polynomial
in the cube size. -/
theorem IntegerCube.measureReal_no_crossing_connecting_radius_le_exp {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j)
    (width k₀ N radius : ℕ) (hwidth : 0 < width) (hstart : 0 < k₀ * width)
    (hsize : ∀ n ≤ N, (k₀ + n) * width < Q.size)
    (hradius : 10 * d * ((N + 1) * width - 1) ≤ radius)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hprob : ∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
        (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
      (1 + ((Q.lowerFace j).card : ℝ) +
        ((d * Q.size : ℕ) : ℝ) * (Q.vertices.card : ℝ) ^ 2) * Real.exp (-(c * N)) := by
  have hdiv : N ≤ Q.size / width := by
    apply (Nat.le_div_iff_mul_le hwidth).2
    have hmul := Nat.mul_le_mul_right width (Nat.le_add_left N k₀)
    exact hmul.trans (Nat.le_of_lt (hsize N le_rfl))
  have hpow : ρ ^ (2 * d) ≤ 1 := pow_le_one₀ hρ hρ₁
  have hroot : (p : ℝ) * ρ ^ (2 * d) ≤ 1 := by
    calc
      (p : ℝ) * ρ ^ (2 * d) ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hpow p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hfirst : (p : ℝ) * ρ ≤ 1 := by
    calc
      (p : ℝ) * ρ ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left hρ₁ p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have htwo : (p : ℝ) * ((p : ℝ) * ρ) ≤ 1 := by
    calc
      (p : ℝ) * ((p : ℝ) * ρ) ≤ (p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hfirst p.property.1
      _ ≤ 1 := by simpa using p.property.2
  have hb₁ := one_sub_pow_le_exp_neg_mul hc.le hcρ hρ₁ hdiv
  have hb₂ := one_sub_pow_le_exp_neg_mul (m := N) (n := N) hc.le hcroot hroot le_rfl
  have hb₃ := one_sub_pow_le_exp_neg_mul (m := N) (n := N) hc.le hctwo htwo le_rfl
  have hb := Q.measureReal_no_crossing_connecting_radius_le_of_twoPoint_slabs hd j i hij
    width k₀ N radius hwidth hstart hsize hradius p ρ hρ hρ₁ hprob
  calc
    _ ≤ ((1 - ρ) ^ (Q.size / width) +
        ((Q.lowerFace j).card : ℝ) * (1 - (p : ℝ) * ρ ^ (2 * d)) ^ N) +
      ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 *
        (1 - (p : ℝ) * ((p : ℝ) * ρ)) ^ N) := hb
    _ ≤ (Real.exp (-(c * N)) + ((Q.lowerFace j).card : ℝ) * Real.exp (-(c * N))) +
        ((d * Q.size : ℕ) : ℝ) * ((Q.vertices.card : ℝ) ^ 2 * Real.exp (-(c * N))) := by
      gcongr
    _ = _ := by ring

/-- Positive bond and slab-connection probabilities admit a common positive
rate for the three geometric factors. -/
theorem exists_slab_decay_rate {d : ℕ} (p : unitInterval) (ρ : ℝ)
    (hp : 0 < (p : ℝ)) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ ρ ∧ c ≤ (p : ℝ) * ρ ^ (2 * d) ∧
      c ≤ (p : ℝ) * ((p : ℝ) * ρ) := by
  let c := min ρ (min ((p : ℝ) * ρ ^ (2 * d)) ((p : ℝ) * ((p : ℝ) * ρ)))
  refine ⟨c, ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min hρ (lt_min (mul_pos hp (pow_pos hρ _)) (mul_pos hp (mul_pos hp hρ)))
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

end Rigidity.Percolation
