import Rigidity.Proofs.Partition.Lambda

/-!
# Counting bad cubes near a triadic cube

The indices of the cubes of scale `j` near the triadic cube of scale `m` centred at the origin
split into `3ᵈ` residue classes modulo three. Two distinct cubes of scale `j` in the same class
have centres at least three side lengths apart in some coordinate, hence disjoint threefold
enlargements, so their bad events are independent. If each cube is bad with probability at most
`a`, at least `k` cubes of a class are bad with probability at most `(e N a / k)^k`, where
`N = (2 · 3^{m-j} + 23)^d` bounds the number of indices.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal Nat

variable {d : ℕ}

/-- The residues modulo three of the coordinates of an index. -/
def residue (ι : Fin d → ℤ) : Fin d → Fin 3 := fun i =>
  ⟨((ι i) % 3).toNat, by
    have h0 : 0 ≤ ι i % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : ι i % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega⟩

theorem emod_three_eq_of_residue_eq {ι ι' : Fin d → ℤ} (h : residue ι = residue ι') (i : Fin d) :
    ι i % 3 = ι' i % 3 := by
  have hi := congrArg (fun r => ((r i : Fin 3) : ℕ)) h
  simp only [residue] at hi
  have h0 : 0 ≤ ι i % 3 := Int.emod_nonneg _ (by norm_num)
  have h0' : 0 ≤ ι' i % 3 := Int.emod_nonneg _ (by norm_num)
  omega

/-- Distinct cubes of the same scale whose indices have the same residues have disjoint
threefold enlargements. -/
theorem disjoint_centeredTriple_of_residue_eq {j : ℕ} {ι ι' : Fin d → ℤ} (hne : ι ≠ ι')
    (h : residue ι = residue ι') :
    Disjoint (⟨j, ι⟩ : TriadicCube d).centeredTriple (⟨j, ι'⟩ : TriadicCube d).centeredTriple := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hmod := emod_three_eq_of_residue_eq h i
  have hsep : 3 ≤ |ι i - ι' i| := by
    rcases le_or_gt (ι i) (ι' i) with hle | hlt
    · rw [abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_pos (by omega)]
      omega
  apply TriadicCube.disjoint_centeredTriple_of_center_separation _ _ i
  have hpos : (0 : ℤ) < (3 : ℤ) ^ j := by positivity
  change 3 * ((3 : ℤ) ^ j + (3 : ℤ) ^ j) ≤ |2 * ((3 : ℤ) ^ j * ι i - (3 : ℤ) ^ j * ι' i)|
  rw [show 2 * ((3 : ℤ) ^ j * ι i - (3 : ℤ) ^ j * ι' i) = (2 * (3 : ℤ) ^ j) * (ι i - ι' i) by
    ring, abs_mul, abs_of_pos (by positivity)]
  nlinarith

open scoped Classical in
/-- The number of bad cubes of scale `j` near the cube of scale `m` centred at the origin whose
index has residues `r`. -/
noncomputable def classBadCount (ω : Configuration d) (m j : ℕ) (r : Fin d → Fin 3) : ℕ :=
  (((nearIndices d m j).subtype fun ι => residue ι = r).filter
    fun ι => (⟨j, ι.1⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card

open scoped Classical in
/-- The bad cubes near the cube of scale `m` split into residue classes. -/
theorem card_filter_bad_eq_sum_classBadCount (ω : Configuration d) (m j : ℕ) :
    ((nearIndices d m j).filter
        fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card =
      ∑ r : Fin d → Fin 3, classBadCount ω m j r := by
  rw [Finset.card_eq_sum_card_fiberwise (f := residue) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold classBadCount
  rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext ι
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨hι, hbad⟩, hr⟩
    exact ⟨⟨ι, hr⟩, ⟨hι, hbad⟩, rfl⟩
  · rintro ⟨⟨ι', hr⟩, ⟨hι, hbad⟩, rfl⟩
    exact ⟨⟨hι, hbad⟩, hr⟩

/-- `C(N, k) a^k ≤ (e N a / k)^k`. -/
theorem choose_mul_pow_le (N k : ℕ) (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) :
    (N.choose k : ℝ) * a ^ k ≤ (Real.exp 1 * N * a / k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (N.choose k : ℝ) ≤ (N : ℝ) ^ k / k ! := Nat.choose_le_pow_div k N
  have h2 : (k : ℝ) ^ k / k ! ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hkk : (0 : ℝ) < (k : ℝ) ^ k := by positivity
  have h3 : (1 : ℝ) / k ! ≤ Real.exp k / (k : ℝ) ^ k := by
    rw [div_le_div_iff₀ hfac hkk, one_mul]
    rw [div_le_iff₀ hfac] at h2
    linarith
  have hexp : Real.exp k = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  calc (N.choose k : ℝ) * a ^ k ≤ (N : ℝ) ^ k / k ! * a ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (N : ℝ) ^ k * a ^ k * (1 / k !) := by ring
    _ ≤ (N : ℝ) ^ k * a ^ k * (Real.exp k / (k : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (Real.exp 1 * N * a / k) ^ k := by
        rw [hexp, div_pow, mul_pow, mul_pow]
        field_simp

/-- **Many bad cubes in a residue class.** If every cube of scale `j ≥ 3` fails to be good with
probability at most `a`, then at least `k > 0` bad cubes of a residue class near the cube of scale
`m` centred at the origin occur with probability at most `(e N a / k)^k`,
`N = (2 · 3^{m-j} + 23)^d`. -/
theorem measure_le_classBadCount_le (p : unitInterval) {a : ℝ} (ha : 0 ≤ a) {m j : ℕ}
    (hj : 3 ≤ j)
    (hq : ∀ ι : Fin d → ℤ,
      latticeBondLaw d p {ω | (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω} ≤
        ENNReal.ofReal a)
    (r : Fin d → Fin 3) {k : ℕ} (hk : 0 < k) :
    latticeBondLaw d p {ω | k ≤ classBadCount ω m j r} ≤
      ENNReal.ofReal ((Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / k) ^ k) := by
  classical
  set s := (nearIndices d m j).subtype fun ι => residue ι = r with hsdef
  have hsep : Pairwise fun ι ι' : {ι : Fin d → ℤ // residue ι = r} =>
      Disjoint (⟨j, ι.1⟩ : TriadicCube d).centeredTriple
        (⟨j, ι'.1⟩ : TriadicCube d).centeredTriple := by
    intro ι ι' hne
    exact disjoint_centeredTriple_of_residue_eq (fun h => hne (Subtype.ext h))
      (ι.2.trans ι'.2.symm)
  have h := measure_le_card_bad_le p (fun ι : {ι : Fin d → ℤ // residue ι = r} =>
    (⟨j, ι.1⟩ : TriadicCube d)) (fun _ => hj) hsep s (ENNReal.ofReal a)
    (fun ι _ => hq ι.1) k
  have hscard : (s.card : ℝ) ≤ (2 * (3 : ℝ) ^ (m - j) + 23) ^ d := by
    rw [← card_nearIndices d m j]
    have : s.card ≤ (nearIndices d m j).card := by
      rw [hsdef, Finset.card_subtype]
      exact Finset.card_filter_le _ _
    exact_mod_cast this
  have hreal : ((s.card.choose k : ℕ) : ℝ) * a ^ k ≤
      (Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / k) ^ k := by
    refine (choose_mul_pow_le s.card k hk ha).trans ?_
    gcongr
  unfold classBadCount
  refine h.trans ?_
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end Rigidity.Percolation
