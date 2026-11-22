import Rigidity.Proofs.Cluster.MeyersPlanarBox

/-!
# Coarse gradients through the Meyers estimate

The deterministic core of Step 3 of the proof of Lemma 5.5 of Armstrong and Dario, display
(5.16) there, in dimension two. The coarsening `[w]_𝒫` of a function `w` on the cluster `𝒞(V)` of
a triadic cube `V` has, on a resolved integer square `B` whose cluster lies in `𝒞(V)`, the energy
bound of Lemma 3.3 with the weight `(3^{ρ'(z)})³`, where `ρ'` is the pair reach scale of `B`
(`planarBox_sum_gradNormIn_sq_le_clusterGradSq`). In each cell `□'` of a finite family covering
`𝒞(B)`, with `3□' ⊆ V` and overlap of the triples at most `N`, Hölder's inequality with the
exponents `p = 1 + ε/2` and its conjugate `q` and the Meyers estimate
`avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p`, `E = |∇w 1_{𝐚≠0}|²`, give
`∑_{□'} W E ≤ |□'| (avg_{□'} W^q)^{1/q} C_M^{1/p} avg_{3□'} E` (`sum_mul_le_of_meyers_cells`).
Hence, if `(avg_{□'} W^{3q})^{1/q} ≤ A` on every cell for a weight `W ≥ 3^{ρ'}`,
`∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ C² A C_M^{1/p} N ∑_{x ∈ V} E(x)`
(`planarBox_coarse_energy_le_of_meyers`).

Armstrong and Dario apply Hölder's inequality to the whole sum over the cells of the Meyers
partition; the inequality
`(|□_n|⁻¹ ∑ |□'|^{1-s/2} a_{□'}^{s/2})^{2/s} ≤ |□_n|⁻¹ ∑ |□'|^{2/s-1} a_{□'}` used there holds only
with `|□_n|^{-2/s}` on the right, and the global Hölder inequality loses a power of the number of
cells (`sum_rpow_le_of_meyers_cells` is the bound it gives). Hölder's inequality inside each cell
avoids this loss; the weight factor is then the largest cell average of the weight, which is
bounded when the cells are the triadic cubes of scale `⌈n/2⌉` inside `z + □_n` away from its
boundary. Here the weight is the pair reach of `𝒫` itself, bounded by three times the reach of the
planar partition, which has all moments.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical

variable {d : ℕ}

/-- **The Meyers estimate on cells.** Let `E ≥ 0`, `p ≥ 1`, and let `I` be a finite family of
cells `□' = cube k y` covering `D`, with triples `3□'` inside `W`, each point lying in at most `N`
of the triples, and satisfying the Meyers estimate `avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p`. Then
`∑_{x ∈ D} E(x)^p ≤ C_M (N ∑_{x ∈ W} E(x))^p`. -/
theorem sum_rpow_le_of_meyers_cells {E : Vertex d → ℝ} (hE : ∀ x, 0 ≤ E x) {p CM : ℝ}
    (hp : 1 ≤ p) (hCM : 0 ≤ CM) (I : Finset (ℕ × Vertex d)) (D W : Finset (Vertex d)) {N : ℕ}
    (hD : ∀ x ∈ D, ∃ c ∈ I, x ∈ cube c.1 c.2) (hW : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ W)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => E x ^ p) ≤ CM * avg (enl 1 c.1 c.2) E ^ p) :
    ∑ x ∈ D, E x ^ p ≤ CM * ((N : ℝ) * ∑ x ∈ W, E x) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hEp : ∀ x, 0 ≤ E x ^ p := fun x => Real.rpow_nonneg (hE x) p
  set S : ℕ × Vertex d → ℝ := fun c => ∑ x ∈ enl 1 c.1 c.2, E x with hS
  have hS0 : ∀ c, 0 ≤ S c := fun c => Finset.sum_nonneg fun x _ => hE x
  -- the cover
  have h1 : ∑ x ∈ D, E x ^ p ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, E x ^ p := by
    calc ∑ x ∈ D, E x ^ p ≤ ∑ x ∈ D, ∑ c ∈ I, (if x ∈ cube c.1 c.2 then E x ^ p else 0) := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨c, hc, hxc⟩ := hD x hx
          have h := Finset.single_le_sum (f := fun c : ℕ × Vertex d =>
            if x ∈ cube c.1 c.2 then E x ^ p else 0)
            (fun c _ => ite_nonneg (hEp x) le_rfl) hc
          simp only [if_pos hxc] at h
          exact h
      _ = ∑ c ∈ I, ∑ x ∈ D, (if x ∈ cube c.1 c.2 then E x ^ p else 0) := Finset.sum_comm
      _ ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, E x ^ p := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.1 hx).2)
            fun x _ _ => hEp x
  -- the Meyers estimate on each cell
  have h2 : ∀ c ∈ I, ∑ x ∈ cube c.1 c.2, E x ^ p ≤ CM * S c ^ p := by
    intro c hc
    have hcard : ((cube c.1 c.2).card : ℝ) = ((3 : ℝ) ^ c.1) ^ d := card_cube c.1 c.2
    have hcardE : ((enl 1 c.1 c.2).card : ℝ) = ((3 : ℝ) ^ (c.1 + 1)) ^ d := card_enl 1 c.1 c.2
    have hpos : (0 : ℝ) < ((cube c.1 c.2).card : ℝ) := by rw [hcard]; positivity
    have hposE : (0 : ℝ) < ((enl 1 c.1 c.2).card : ℝ) := by rw [hcardE]; positivity
    have hle : ((cube c.1 c.2).card : ℝ) ≤ ((enl 1 c.1 c.2).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (cube_subset_enl 1 c.1 c.2)
    have h1E : (1 : ℝ) ≤ ((enl 1 c.1 c.2).card : ℝ) := by
      rw [hcardE]
      exact one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hLp : ((enl 1 c.1 c.2).card : ℝ) ≤ ((enl 1 c.1 c.2).card : ℝ) ^ p := by
      conv_lhs => rw [← Real.rpow_one ((enl 1 c.1 c.2).card : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le h1E hp
    have hM' := hM c hc
    rw [avg, avg, Real.div_rpow (hS0 c) hposE.le] at hM'
    have hLp0 : 0 < ((enl 1 c.1 c.2).card : ℝ) ^ p := Real.rpow_pos_of_pos hposE p
    calc ∑ x ∈ cube c.1 c.2, E x ^ p
        = ((cube c.1 c.2).card : ℝ) *
            ((∑ x ∈ cube c.1 c.2, E x ^ p) / ((cube c.1 c.2).card : ℝ)) := by
          field_simp
      _ ≤ ((cube c.1 c.2).card : ℝ) * (CM * (S c ^ p / ((enl 1 c.1 c.2).card : ℝ) ^ p)) :=
          mul_le_mul_of_nonneg_left hM' hpos.le
      _ = CM * S c ^ p * (((cube c.1 c.2).card : ℝ) / ((enl 1 c.1 c.2).card : ℝ) ^ p) := by
          ring
      _ ≤ CM * S c ^ p * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCM (Real.rpow_nonneg (hS0 c) p))
          rw [div_le_one hLp0]
          exact hle.trans hLp
      _ = CM * S c ^ p := mul_one _
  -- the overlap of the triples
  have h3 : ∑ c ∈ I, S c ≤ (N : ℝ) * ∑ x ∈ W, E x := by
    calc ∑ c ∈ I, S c = ∑ c ∈ I, ∑ x ∈ W, (if x ∈ enl 1 c.1 c.2 then E x else 0) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [hS, Finset.sum_ite_mem, Finset.inter_eq_right.2 (hW c hc)]
      _ = ∑ x ∈ W, ∑ c ∈ I, (if x ∈ enl 1 c.1 c.2 then E x else 0) := Finset.sum_comm
      _ = ∑ x ∈ W, ((I.filter fun c => x ∈ enl 1 c.1 c.2).card : ℝ) * E x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ W, (N : ℝ) * E x := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right ?_ (hE x)
          exact_mod_cast hN x
      _ = (N : ℝ) * ∑ x ∈ W, E x := by rw [Finset.mul_sum]
  calc ∑ x ∈ D, E x ^ p ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, E x ^ p := h1
    _ ≤ ∑ c ∈ I, CM * S c ^ p := Finset.sum_le_sum h2
    _ = CM * ∑ c ∈ I, S c ^ p := by rw [Finset.mul_sum]
    _ ≤ CM * (∑ c ∈ I, S c) ^ p :=
        mul_le_mul_of_nonneg_left (sum_rpow_le_rpow_sum I S hp fun c _ => hS0 c) hCM
    _ ≤ CM * ((N : ℝ) * ∑ x ∈ W, E x) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Finset.sum_nonneg fun c _ => hS0 c) h3
          hp0) hCM

/-- **Hölder's inequality and the Meyers estimate in each cell.** Let `E, W ≥ 0`, `p` and `q`
Hölder conjugate, and let `I` be a finite family of cells `□' = cube k y` covering `D`, with triples
inside `V`, each point lying in at most `N` of the triples, the Meyers estimate
`avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p` and `(avg_{□'} W^q)^{1/q} ≤ A`. Then
`∑_{x ∈ D} W(x) E(x) ≤ A C_M^{1/p} N ∑_{x ∈ V} E(x)`. -/
theorem sum_mul_le_of_meyers_cells {E Wt : Vertex d → ℝ} (hE : ∀ x, 0 ≤ E x)
    (hW : ∀ x, 0 ≤ Wt x) {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex d)) (D V : Finset (Vertex d)) {N : ℕ}
    (hD : ∀ x ∈ D, ∃ c ∈ I, x ∈ cube c.1 c.2) (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => Wt x ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => E x ^ p) ≤ CM * avg (enl 1 c.1 c.2) E ^ p) :
    ∑ x ∈ D, Wt x * E x ≤ A * (CM ^ (1 / p) * ((N : ℝ) * ∑ x ∈ V, E x)) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hWE : ∀ x, 0 ≤ Wt x * E x := fun x => mul_nonneg (hW x) (hE x)
  set S : ℕ × Vertex d → ℝ := fun c => ∑ x ∈ enl 1 c.1 c.2, E x with hS
  have hS0 : ∀ c, 0 ≤ S c := fun c => Finset.sum_nonneg fun x _ => hE x
  -- the cover
  have h1 : ∑ x ∈ D, Wt x * E x ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, Wt x * E x := by
    calc ∑ x ∈ D, Wt x * E x
        ≤ ∑ x ∈ D, ∑ c ∈ I, (if x ∈ cube c.1 c.2 then Wt x * E x else 0) := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨c, hc, hxc⟩ := hD x hx
          have h := Finset.single_le_sum (f := fun c : ℕ × Vertex d =>
            if x ∈ cube c.1 c.2 then Wt x * E x else 0)
            (fun c _ => ite_nonneg (hWE x) le_rfl) hc
          simp only [if_pos hxc] at h
          exact h
      _ = ∑ c ∈ I, ∑ x ∈ D, (if x ∈ cube c.1 c.2 then Wt x * E x else 0) := Finset.sum_comm
      _ ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, Wt x * E x := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.1 hx).2)
            fun x _ _ => hWE x
  -- Hölder and the Meyers estimate in each cell
  have h2 : ∀ c ∈ I, ∑ x ∈ cube c.1 c.2, Wt x * E x ≤ A * (CM ^ (1 / p) * S c) := by
    intro c hc
    set L : ℝ := ((cube c.1 c.2).card : ℝ) with hL
    have hcard : L = ((3 : ℝ) ^ c.1) ^ d := card_cube c.1 c.2
    have hcardE : ((enl 1 c.1 c.2).card : ℝ) = ((3 : ℝ) ^ (c.1 + 1)) ^ d := card_enl 1 c.1 c.2
    have hpos : 0 < L := by rw [hcard]; positivity
    have hposE : (0 : ℝ) < ((enl 1 c.1 c.2).card : ℝ) := by rw [hcardE]; positivity
    have hle : L ≤ ((enl 1 c.1 c.2).card : ℝ) := by
      rw [hL]
      exact_mod_cast Finset.card_le_card (cube_subset_enl 1 c.1 c.2)
    have hHol := Real.inner_le_Lp_mul_Lq_of_nonneg (cube c.1 c.2) hpq.symm
      (f := Wt) (g := E) (fun x _ => hW x) (fun x _ => hE x)
    have hWq : (∑ x ∈ cube c.1 c.2, Wt x ^ q) ^ (1 / q) ≤ L ^ (1 / q) * A := by
      have h := hA c hc
      rw [avg] at h
      have he : ∑ x ∈ cube c.1 c.2, Wt x ^ q =
          L * ((∑ x ∈ cube c.1 c.2, Wt x ^ q) / L) := by field_simp
      rw [he, Real.mul_rpow hpos.le (div_nonneg (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (hW x) q) hpos.le)]
      exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hpos.le _)
    have hEp : (∑ x ∈ cube c.1 c.2, E x ^ p) ^ (1 / p) ≤
        L ^ (1 / p) * (CM ^ (1 / p) * (S c / ((enl 1 c.1 c.2).card : ℝ))) := by
      have h := hM c hc
      rw [avg, avg] at h
      have he : ∑ x ∈ cube c.1 c.2, E x ^ p = L * ((∑ x ∈ cube c.1 c.2, E x ^ p) / L) := by
        field_simp
      have hsum0 : 0 ≤ ∑ x ∈ cube c.1 c.2, E x ^ p :=
        Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hE x) p
      have hT0 : 0 ≤ S c / ((enl 1 c.1 c.2).card : ℝ) := div_nonneg (hS0 c) hposE.le
      rw [he, Real.mul_rpow hpos.le (div_nonneg hsum0 hpos.le)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hpos.le _)
      calc ((∑ x ∈ cube c.1 c.2, E x ^ p) / L) ^ (1 / p)
          ≤ (CM * (S c / ((enl 1 c.1 c.2).card : ℝ)) ^ p) ^ (1 / p) :=
            Real.rpow_le_rpow (div_nonneg hsum0 hpos.le) h (by positivity)
        _ = CM ^ (1 / p) * (S c / ((enl 1 c.1 c.2).card : ℝ)) := by
            rw [Real.mul_rpow hCM (Real.rpow_nonneg hT0 p), ← Real.rpow_mul hT0,
              mul_one_div_cancel hp0.ne', Real.rpow_one]
    have hLL : L ^ (1 / q) * L ^ (1 / p) = L := by
      have hsum : 1 / q + 1 / p = 1 := by
        rw [add_comm, hpq.one_div_add_one_div, div_one]
      rw [← Real.rpow_add hpos, hsum, Real.rpow_one]
    have hAC : 0 ≤ A * CM ^ (1 / p) := mul_nonneg hA0 (Real.rpow_nonneg hCM _)
    calc ∑ x ∈ cube c.1 c.2, Wt x * E x
        ≤ (∑ x ∈ cube c.1 c.2, Wt x ^ q) ^ (1 / q) * (∑ x ∈ cube c.1 c.2, E x ^ p) ^ (1 / p) :=
          hHol
      _ ≤ (L ^ (1 / q) * A) * (L ^ (1 / p) * (CM ^ (1 / p) *
            (S c / ((enl 1 c.1 c.2).card : ℝ)))) :=
          mul_le_mul hWq hEp (Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
            Real.rpow_nonneg (hE x) p) _) (by positivity)
      _ = A * CM ^ (1 / p) * (L / ((enl 1 c.1 c.2).card : ℝ)) * S c := by
          rw [show (L ^ (1 / q) * A) * (L ^ (1 / p) * (CM ^ (1 / p) *
            (S c / ((enl 1 c.1 c.2).card : ℝ)))) =
            A * CM ^ (1 / p) * ((L ^ (1 / q) * L ^ (1 / p)) / ((enl 1 c.1 c.2).card : ℝ)) * S c
            by ring, hLL]
      _ ≤ A * CM ^ (1 / p) * 1 * S c := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hAC) (hS0 c)
          rw [div_le_one hposE]
          exact hle
      _ = A * (CM ^ (1 / p) * S c) := by ring
  -- the overlap of the triples
  have h3 : ∑ c ∈ I, S c ≤ (N : ℝ) * ∑ x ∈ V, E x := by
    calc ∑ c ∈ I, S c = ∑ c ∈ I, ∑ x ∈ V, (if x ∈ enl 1 c.1 c.2 then E x else 0) := by
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [hS, Finset.sum_ite_mem, Finset.inter_eq_right.2 (hV c hc)]
      _ = ∑ x ∈ V, ∑ c ∈ I, (if x ∈ enl 1 c.1 c.2 then E x else 0) := Finset.sum_comm
      _ = ∑ x ∈ V, ((I.filter fun c => x ∈ enl 1 c.1 c.2).card : ℝ) * E x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ V, (N : ℝ) * E x := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right ?_ (hE x)
          exact_mod_cast hN x
      _ = (N : ℝ) * ∑ x ∈ V, E x := by rw [Finset.mul_sum]
  calc ∑ x ∈ D, Wt x * E x ≤ ∑ c ∈ I, ∑ x ∈ cube c.1 c.2, Wt x * E x := h1
    _ ≤ ∑ c ∈ I, A * (CM ^ (1 / p) * S c) := Finset.sum_le_sum h2
    _ = A * (CM ^ (1 / p) * ∑ c ∈ I, S c) := by rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ A * (CM ^ (1 / p) * ((N : ℝ) * ∑ x ∈ V, E x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hCM _)) hA0

variable {ω : Configuration 2}

/-- **Lemma 3.3 with `s = 2` for a function on a larger cluster.** On a resolved integer square
`B` whose cluster lies in `U₀`,
`∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ C² ∑_{z ∈ 𝒞(B)} (3^{ρ'(z)})³ |∇w 1_{𝐚≠0}|²_{U₀}(z)`,
with `C = 4 · (3/2) · 10² · 9² · 2√2` and `ρ'` the pair reach scale of `B`. -/
theorem planarBox_sum_gradNormIn_sq_le_clusterGradSq (hP : PlanarPartitionEvent ω)
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B) {U₀ : Finset (Vertex 2)}
    (hBU : boxClusterVertices ω B ⊆ U₀) (w : Vertex 2 → ℝ) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices
        (fun x => w (planarCoarseAnchor ω x)) x ^ 2 ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ 2 *
        ∑ z ∈ boxClusterVertices ω B,
          ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) ^ 3 *
            clusterGradSq ω U₀ w z := by
  have h := planarBox_sum_gradNormIn_coarseAnchor_rpow_le hP hBr w (s := 2) (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (le_of_eq_of_le rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_)
    (by positivity)))
  have he : ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) ^
      ((2 : ℝ) * ((2 : ℕ) : ℝ) - 1) =
      ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) ^ 3 := by
    rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [he, gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _)]
  exact mul_le_mul_of_nonneg_left (clusterGradSq_le_of_subset ω hBU w z) (by positivity)

/-- **Coarse gradients through the Meyers estimate** (the deterministic core of Step 3 of the proof
of Lemma 5.5 of Armstrong and Dario, display (5.16), in dimension two). Let `B` be a resolved
integer square whose cluster lies in the cluster `𝒞(V)` of a triadic cube `V`, `w` a function,
`E = |∇w 1_{𝐚≠0}|²` on `𝒞(V)`, `W ≥ 0` a weight with `W ≥ 3^{ρ'}` on `𝒞(B)`, `p > 1` with Hölder
conjugate `q`, and let a finite family of cells `□'` cover `𝒞(B)`, with `3□' ⊆ V`, overlap of the
triples at most `N`, the Meyers estimate `avg_{□'} E^p ≤ C_M (avg_{3□'} E)^p` and
`(avg_{□'} W^{3q})^{1/q} ≤ A`. Then `∑_{x ∈ B} |∇[w]_𝒫|²(x) ≤ C² A C_M^{1/p} N ∑_{x ∈ V} E(x)`. -/
theorem planarBox_coarse_energy_le_of_meyers (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    (hBV : boxClusterVertices ω B ⊆ clusterVertices ω V) (w : Vertex 2 → ℝ)
    (Wt : Vertex 2 → ℝ) (hWt0 : ∀ x, 0 ≤ Wt x)
    (hWt : ∀ z ∈ boxClusterVertices ω B,
      (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z ≤ Wt z)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex 2)) {N : ℕ}
    (hcov : ∀ z ∈ boxClusterVertices ω B, ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => clusterEnergy ω (clusterVertices ω V) w x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) w) ^ p) :
    ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices
        (fun x => w (planarCoarseAnchor ω x)) x ^ 2 ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ 2 *
        (A * (CM ^ (1 / p) * ((N : ℝ) *
          ∑ x ∈ V.toIntegerCube.vertices, clusterEnergy ω (clusterVertices ω V) w x))) := by
  set U₀ := clusterVertices ω V with hU₀
  set E : Vertex 2 → ℝ := clusterEnergy ω U₀ w with hEdef
  have hE0 : ∀ x, 0 ≤ E x := clusterEnergy_nonneg ω U₀ w
  have hcoarse := planarBox_sum_gradNormIn_sq_le_clusterGradSq hP hBr hBV w
  refine hcoarse.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  set C := boxClusterVertices ω B with hCdef
  have hGE : ∀ z ∈ C, clusterGradSq ω U₀ w z = E z := fun z hz => by
    rw [hEdef, clusterEnergy, if_pos (hBV hz)]
  have hstep1 : ∑ z ∈ C, ((3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z) ^ 3 *
      clusterGradSq ω U₀ w z ≤ ∑ z ∈ C, Wt z ^ 3 * E z := by
    refine Finset.sum_le_sum fun z hz => ?_
    rw [hGE z hz]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hWt z hz) 3) (hE0 z)
  exact hstep1.trans (sum_mul_le_of_meyers_cells hE0 (fun x => pow_nonneg (hWt0 x) 3) hpq hCM
    hA0 I C V.toIntegerCube.vertices hcov hV hN hA hM)

end Rigidity.Proofs.Cluster
