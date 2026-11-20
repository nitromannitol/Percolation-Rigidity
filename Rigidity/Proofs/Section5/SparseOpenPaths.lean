import Rigidity.Proofs.Section5.RenormWalk

/-!
# Sparse open sites on planar paths

A Peierls estimate controls long self-avoiding star paths that contain few open sites,
uniformly over a finite set of starting sites.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- The probability of a long star path with at most half its sites open decays exponentially
in the minimum length, uniformly over any finite set of starting sites. -/
theorem measure_exists_sparse_star_path_le {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (T : Finset PlanarCarrier) (N : ℕ) :
    ν (⋃ j : ℕ, ⋃ z ∈ T, ⋃ l ∈ starWalkLists (N + j) z,
      {η | l.Nodup ∧ 2 * l.countP η ≤ N + j}) ≤
        ENNReal.ofReal (4 * (T.card : ℝ) * (1 / 8 : ℝ) ^ N) := by
  have hterm (L : ℕ) :
      ν (⋃ z ∈ T, ⋃ l ∈ starWalkLists L z,
        {η | l.Nodup ∧ 2 * l.countP η ≤ L}) ≤
          ENNReal.ofReal (2 * (T.card : ℝ) * (1 / 8 : ℝ) ^ L) := by
    calc
      _ ≤ ∑ z ∈ T, ν (⋃ l ∈ starWalkLists L z,
          {η | l.Nodup ∧ 2 * l.countP η ≤ L}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ z ∈ T, ∑ l ∈ starWalkLists L z,
          ν {η | l.Nodup ∧ 2 * l.countP η ≤ L} :=
            Finset.sum_le_sum fun z _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ T, (9 ^ L) • ENNReal.ofReal (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L) :=
          Finset.sum_le_sum fun z _ =>
            (Finset.sum_le_card_nsmul _ _ _ fun l hl =>
              measure_countP_le hν hcl (length_of_mem_starWalkLists hl)).trans
              (nsmul_le_nsmul_left zero_le (card_starWalkLists_le L z))
      _ = ENNReal.ofReal ((T.card : ℝ) * 9 ^ L *
          (2 ^ (L + 1) * (1 / 144 : ℝ) ^ L)) := by
            have ha : ENNReal.ofReal ((T.card : ℝ) * 9 ^ L) =
                (T.card * 9 ^ L : ℕ) := by
              rw [← ENNReal.ofReal_natCast]
              norm_num
            rw [Finset.sum_const, smul_smul, nsmul_eq_mul,
              ENNReal.ofReal_mul (p := (T.card : ℝ) * 9 ^ L) (by positivity), ha]
      _ = ENNReal.ofReal (2 * (T.card : ℝ) * (1 / 8 : ℝ) ^ L) := by
          congr 1
          calc
            _ = 2 * (T.card : ℝ) * (9 * 2 * (1 / 144 : ℝ)) ^ L := by
              rw [mul_pow, mul_pow, pow_succ]
              ring
            _ = _ := by norm_num
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal
        (2 * (T.card : ℝ) * (1 / 8 : ℝ) ^ (N + j)) :=
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => hterm (N + j))
    _ = ENNReal.ofReal (∑' j : ℕ,
        (2 * (T.card : ℝ) * (1 / 8 : ℝ) ^ N) * (1 / 8 : ℝ) ^ j) := by
          simp_rw [pow_add, ← mul_assoc]
          exact (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
            ((summable_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by norm_num)
              (by norm_num)).mul_left _)).symm
    _ ≤ ENNReal.ofReal (4 * (T.card : ℝ) * (1 / 8 : ℝ) ^ N) := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        have hpos : 0 ≤ (T.card : ℝ) * (1 / 8 : ℝ) ^ N := by positivity
        norm_num
        nlinarith

/-- A connection across a vertical distance `N` through closed sites and at most `N / 2`
exceptional sites has exponentially small probability. -/
theorem measure_exists_star_connection_with_exceptions_le {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ((1 / 144 : ℝ) ^ 18))
    (T : Finset PlanarCarrier) {N : ℕ} (hN : 0 < N) :
    ν {η | ∃ (F : Finset PlanarCarrier) (u : PlanarCarrier) (_ : u ∈ T) (v : PlanarCarrier),
        2 * F.card ≤ N ∧ (N : ℤ) ≤ |u.2 - v.2| ∧
        (starGraphOn ({s | η s = false} ∪ ↑F)).Reachable u v} ≤
      ENNReal.ofReal (4 * (T.card : ℝ) * (1 / 8 : ℝ) ^ N) := by
  apply (measure_mono ?_).trans (measure_exists_sparse_star_path_le hν hcl T N)
  rintro η ⟨F, u, hu, v, hF, huv, ⟨w⟩⟩
  let p := w.bypass
  have hp : p.IsPath := w.bypass_isPath
  have hdist : |u.2 - v.2| ≤ (p.length : ℤ) := (abs_sub_le_length_starGraphOn p).2
  have hlen : N ≤ p.length := by exact_mod_cast huv.trans hdist
  have hpos : 0 < p.length := lt_of_lt_of_le hN hlen
  have hcnt := countP_support_le p hp hpos
  have hsparse : 2 * p.support.countP η ≤ p.length := by omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨p.length - N, u, hu, p.support, ?_, hp.support_nodup, ?_⟩
  · simpa only [Nat.add_sub_of_le hlen] using support_mem_starWalkLists_of_starGraphOn p
  · simpa only [Nat.add_sub_of_le hlen] using hsparse

end Rigidity.Proofs.Section5
