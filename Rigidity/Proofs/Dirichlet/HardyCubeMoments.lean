import Rigidity.Proofs.Dirichlet.LayerEnergy
import Rigidity.Proofs.Dirichlet.HardyMoments
import Rigidity.Proofs.Dirichlet.MesoscopicPoincare

/-!
# Moments of the Hardy weight of a cube

For a cube `Q` of side `N`, `q ≥ 1` and `0 < γ q < 1` (`γ ≤ 1/16`),
`Σ_{x∈Q} W_Q(x)^q ≤ (2d)^q N^{d − γq}/(1 − γq)`: the weight is a sum of `2d` one-dimensional
weights `w(dist) ≤ (dist + 1)^{−γ}`, each of which is summed slice by slice. Moreover
`W_Q(x + e_k) ≤ 2 W_Q(x)` on `Q`, so the edge averages of `W_Q` are at most `2 W_Q`.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

theorem hardyWeight_le_two_mul_succ {γ : ℝ} (hγ : γ ≤ 1 / 2) (s : ℕ) :
    hardyWeight γ s ≤ 2 * hardyWeight γ (s + 1) := by
  rw [hardyWeight_succ]
  have h0 := hardyWeight_pos (show γ < 1 by linarith) s
  have h1 : γ / ((s : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  nlinarith

/-- `W_Q(x + e_k) ≤ 2 W_Q(x)` for `x ∈ Q`. -/
theorem cubeHardyWeight_add_unit_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (Q : IntegerCube d)
    {x : Vertex d} (hx : x ∈ Q.vertices) (k : Fin d) :
    cubeHardyWeight γ Q (x + unit k) ≤ 2 * cubeHardyWeight γ Q x := by
  have hγ1 : γ < 1 := by linarith
  rw [cubeHardyWeight, cubeHardyWeight, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hjk : j = k
  · subst hjk
    rw [IntegerCube.mem_vertices] at hx
    have hk : (x + unit j) j = x j + 1 := by rw [add_unit_apply, if_pos rfl]
    simp only [cubeHardyWeightDir, hk]
    have h1 : hardyWeight γ (x j + 1 - Q.corner j).toNat ≤ hardyWeight γ (x j - Q.corner j).toNat :=
      hardyWeight_antitone hγ0 hγ1 (by omega)
    have h2 : hardyWeight γ (Q.corner j + Q.size - 1 - (x j + 1)).toNat ≤
        2 * hardyWeight γ (Q.corner j + Q.size - 1 - x j).toNat := by
      by_cases htop : x j + 1 = Q.corner j + Q.size
      · have e : (Q.corner j + Q.size - 1 - (x j + 1)).toNat =
            (Q.corner j + Q.size - 1 - x j).toNat := by omega
        rw [e]
        linarith [hardyWeight_pos hγ1 (Q.corner j + Q.size - 1 - x j).toNat]
      · have e : (Q.corner j + Q.size - 1 - x j).toNat =
            (Q.corner j + Q.size - 1 - (x j + 1)).toNat + 1 := by
          have := (hx j).2
          omega
        rw [e]
        exact hardyWeight_le_two_mul_succ hγ _
    linarith [hardyWeight_pos hγ1 (x j - Q.corner j).toNat]
  · have := cubeHardyWeightDir_add_smul_of_ne γ Q hjk x 1
    rw [one_smul] at this
    rw [this]
    linarith [cubeHardyWeightDir_pos hγ1 Q j x]

/-- **Slice counting**: `Σ_{x∈Q} h(x_j) ≤ N^{d−1} Σ_{t ∈ [z_j, z_j + N)} h(t)` for `h ≥ 0`. -/
theorem sum_vertices_comp_coord_le (Q : IntegerCube d) (j : Fin d) (h : ℤ → ℝ)
    (hh : ∀ t, 0 ≤ h t) :
    ∑ x ∈ Q.vertices, h (x j) ≤
      (Q.size : ℝ) ^ (d - 1) * ∑ t ∈ Finset.Ico (Q.corner j) (Q.corner j + Q.size), h t := by
  classical
  set I := Finset.Ico (Q.corner j) (Q.corner j + (Q.size : ℤ))
  have hmaps : ∀ x ∈ Q.vertices, x j ∈ I := fun x hx =>
    Finset.mem_Ico.mpr ((IntegerCube.mem_vertices Q x).mp hx j)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const,
    nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hh t)
  have hsub : Q.vertices.filter (fun x => x j = t) ⊆ Fintype.piFinset (Function.update
      (fun k => Finset.Ico (Q.corner k) (Q.corner k + (Q.size : ℤ))) j {t}) := by
    intro x hx
    obtain ⟨hxQ, hxt⟩ := Finset.mem_filter.mp hx
    rw [IntegerCube.mem_vertices] at hxQ
    refine Fintype.mem_piFinset.mpr fun k => ?_
    by_cases hk : k = j
    · subst hk
      simp [hxt]
    · rw [Function.update_of_ne hk]
      exact Finset.mem_Ico.mpr (hxQ k)
  have := (Finset.card_le_card hsub).trans_eq (card_piFinset_update Q j {t})
  rw [Finset.card_singleton, one_mul] at this
  exact_mod_cast this

/-- Reindexing the left distances. -/
theorem sum_Ico_toNat_sub (z : ℤ) (N : ℕ) (H : ℕ → ℝ) :
    ∑ t ∈ Finset.Ico z (z + N), H (t - z).toNat = ∑ s ∈ Finset.range N, H s := by
  refine Finset.sum_nbij' (fun t => (t - z).toNat) (fun s => z + s) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    simp only [Finset.mem_range]
    omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_Ico]
    omega
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    omega
  · intro s _
    omega
  · intro t _
    rfl

/-- Reindexing the right distances. -/
theorem sum_Ico_toNat_sub' (z : ℤ) (N : ℕ) (H : ℕ → ℝ) :
    ∑ t ∈ Finset.Ico z (z + N), H (z + N - 1 - t).toNat = ∑ s ∈ Finset.range N, H s := by
  refine Finset.sum_nbij' (fun t => (z + N - 1 - t).toNat) (fun s => z + N - 1 - s) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    simp only [Finset.mem_range]
    omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_Ico]
    omega
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    omega
  · intro s hs
    simp only [Finset.mem_range] at hs
    omega
  · intro t _
    rfl

/-- `Σ_{s<N} w_s^q ≤ N^{1−γq}/(1 − γq)` for `0 ≤ γ`, `1 ≤ q`, `γ q < 1`. -/
theorem sum_range_hardyWeight_rpow_le {γ q : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hq : 1 ≤ q)
    (hγq : γ * q < 1) (N : ℕ) :
    ∑ s ∈ Finset.range N, hardyWeight γ s ^ q ≤ (N : ℝ) ^ (1 - γ * q) / (1 - γ * q) := by
  refine le_trans (Finset.sum_le_sum fun s _ => ?_)
    (sum_range_rpow_neg_le (β := γ * q) (by positivity) hγq N)
  calc hardyWeight γ s ^ q ≤ (((s : ℝ) + 1) ^ (-γ)) ^ q :=
        Real.rpow_le_rpow (hardyWeight_pos hγ1 s).le (hardyWeight_le_rpow hγ0 hγ1 s)
          (by linarith)
    _ = ((s : ℝ) + 1) ^ (-(γ * q)) := by
        rw [← Real.rpow_mul (by positivity)]
        ring_nf

/-- **Moments of the Hardy weight of a cube**: for `d ≥ 1`, `0 < γ ≤ 1/16`, `q ≥ 1`, `γ q < 1`,
`Σ_{x∈Q} W_Q(x)^q ≤ (2d)^q N^{d−1} N^{1−γq}/(1 − γq)`. -/
theorem sum_cubeHardyWeight_rpow_le {γ q : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hq : 1 ≤ q)
    (hγq : γ * q < 1) (hd : 0 < d) (Q : IntegerCube d) :
    ∑ x ∈ Q.vertices, cubeHardyWeight γ Q x ^ q ≤
      (2 * (d : ℝ)) ^ q * (Q.size : ℝ) ^ (d - 1) *
        ((Q.size : ℝ) ^ (1 - γ * q) / (1 - γ * q)) := by
  have hγ1 : γ < 1 := by linarith
  set A : Fin d → Vertex d → ℝ := fun j x => hardyWeight γ (x j - Q.corner j).toNat
  set B : Fin d → Vertex d → ℝ := fun j x => hardyWeight γ (Q.corner j + Q.size - 1 - x j).toNat
  set M : ℝ := (Q.size : ℝ) ^ (1 - γ * q) / (1 - γ * q)
  have hA0 : ∀ j x, 0 ≤ A j x := fun j x => (hardyWeight_pos hγ1 _).le
  have hB0 : ∀ j x, 0 ≤ B j x := fun j x => (hardyWeight_pos hγ1 _).le
  -- pointwise power mean
  have hpt : ∀ x, cubeHardyWeight γ Q x ^ q ≤
      (2 * (d : ℝ)) ^ (q - 1) * ∑ j : Fin d, (A j x ^ q + B j x ^ q) := by
    intro x
    have hW : cubeHardyWeight γ Q x = ∑ j : Fin d, (A j x + B j x) := rfl
    have h1 := abs_sum_rpow_le (Finset.univ : Finset (Fin d)) (fun j => A j x + B j x) hq
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ∀ j : Fin d, |A j x + B j x| ^ q ≤ (2 : ℝ) ^ (q - 1) * (A j x ^ q + B j x ^ q) := by
      intro j
      have h := abs_sum_rpow_le (Finset.univ : Finset (Fin 2)) ![A j x, B j x] hq
      simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Nat.cast_ofNat] at h
      rwa [abs_of_nonneg (hA0 j x), abs_of_nonneg (hB0 j x)] at h
    rw [hW, ← abs_of_nonneg (Finset.sum_nonneg fun j _ => add_nonneg (hA0 j x) (hB0 j x))]
    calc |∑ j : Fin d, (A j x + B j x)| ^ q
        ≤ (d : ℝ) ^ (q - 1) * ∑ j : Fin d, |A j x + B j x| ^ q := h1
      _ ≤ (d : ℝ) ^ (q - 1) * ∑ j : Fin d, (2 : ℝ) ^ (q - 1) * (A j x ^ q + B j x ^ q) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h2 j) (by positivity)
      _ = (2 * (d : ℝ)) ^ (q - 1) * ∑ j : Fin d, (A j x ^ q + B j x ^ q) := by
          rw [← Finset.mul_sum, ← mul_assoc, Real.mul_rpow (by norm_num) (Nat.cast_nonneg d),
            mul_comm ((d : ℝ) ^ (q - 1))]
  -- the slice sums
  have hAsum : ∀ j : Fin d, ∑ x ∈ Q.vertices, A j x ^ q ≤ (Q.size : ℝ) ^ (d - 1) * M := by
    intro j
    refine (sum_vertices_comp_coord_le Q j (fun t => hardyWeight γ (t - Q.corner j).toNat ^ q)
      fun t => Real.rpow_nonneg (hardyWeight_pos hγ1 _).le _).trans ?_
    rw [sum_Ico_toNat_sub (Q.corner j) Q.size (fun s => hardyWeight γ s ^ q)]
    exact mul_le_mul_of_nonneg_left (sum_range_hardyWeight_rpow_le hγ0.le hγ1 hq hγq _)
      (by positivity)
  have hBsum : ∀ j : Fin d, ∑ x ∈ Q.vertices, B j x ^ q ≤ (Q.size : ℝ) ^ (d - 1) * M := by
    intro j
    refine (sum_vertices_comp_coord_le Q j
      (fun t => hardyWeight γ (Q.corner j + Q.size - 1 - t).toNat ^ q)
      fun t => Real.rpow_nonneg (hardyWeight_pos hγ1 _).le _).trans ?_
    rw [sum_Ico_toNat_sub' (Q.corner j) Q.size (fun s => hardyWeight γ s ^ q)]
    exact mul_le_mul_of_nonneg_left (sum_range_hardyWeight_rpow_le hγ0.le hγ1 hq hγq _)
      (by positivity)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd' : (0 : ℝ) < 2 * d := by linarith
  calc ∑ x ∈ Q.vertices, cubeHardyWeight γ Q x ^ q
      ≤ ∑ x ∈ Q.vertices, (2 * (d : ℝ)) ^ (q - 1) * ∑ j : Fin d, (A j x ^ q + B j x ^ q) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = (2 * (d : ℝ)) ^ (q - 1) * ∑ j : Fin d,
          (∑ x ∈ Q.vertices, A j x ^ q + ∑ x ∈ Q.vertices, B j x ^ q) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_add_distrib]
    _ ≤ (2 * (d : ℝ)) ^ (q - 1) * ∑ _j : Fin d,
          ((Q.size : ℝ) ^ (d - 1) * M + (Q.size : ℝ) ^ (d - 1) * M) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => add_le_add (hAsum j) (hBsum j))
          (by positivity)
    _ = (2 * (d : ℝ)) ^ q * (Q.size : ℝ) ^ (d - 1) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.rpow_sub_one hd'.ne']
        field_simp
        ring

end Rigidity.Dirichlet
