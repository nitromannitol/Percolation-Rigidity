import Rigidity.Percolation.Pisztora.WellConnected

/-!
# Finite open clusters above the critical point in dimension at least three

Above the critical point in dimension `d ≥ 3`, the open cluster of a vertex `x` is finite and
reaches `ℓ^∞`-distance `l` from `x` with probability at most `C exp(-c l)`
(`exists_finite_cluster_radius_le`); this is the exponential decay of the radius of finite
clusters (G. Grimmett, *Percolation*, 2nd ed., Theorem (8.21), due to Chayes, Chayes, Grimmett,
Kesten and Schonmann). Consequently a finite cluster has at least `n` vertices with probability at
most `C exp(-c n^{1/d})` (`exists_finite_cluster_card_le`).

The proof uses the cubes `x + Q_{M_k}`, `M_k = 2^{k+1} t`, `2t < l`. Except with probability
`A exp(-κ 2^k t)` (`crossing_fail_le`), the cube `x + Q_{M_k}` has a crossing root joined inside
it to every open path of coordinate diameter at least `M_k`. If this holds for every `k`, then the
open path from `x` to distance `l` joins `x` to the first root, and a crossing path of the `k`-th
cube, of diameter `2 M_k = M_{k+1}`, joins the `k`-th root to the next one; the cluster of `x`
then meets every face of every cube, so it is infinite. Summing over `k` gives the bound. This
route replaces the argument of the source by the crossing estimates of uniform slab
connectivity.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- Crossing failure at the `ℓ¹`-radius threshold `8t/10` in a cube of side at most `a (t + 1)` is
exponentially small in `t`. -/
theorem exists_crossing_fail_le_exp {p : unitInterval} {width : ℕ} {ρ c : ℝ}
    (hP : SlabParams d p width ρ c) (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (a : ℕ) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ (T : IntegerCube d) (t : ℕ), 10 * d * width ≤ 8 * t →
      8 * t < 10 * d * T.size → T.size ≤ a * (t + 1) →
      (latticeBondLaw d p) {ω | ¬ HasCrossingComponentConnectingPaths ω T.vertices
        (fun b => ↑(T.lowerFace b)) (fun b => ↑(T.upperFace b))
        (fun n γ => ∀ z : Vertex d, ∃ b : Fin (n + 1),
          ((8 * t : ℕ) : ℤ) < 10 * ∑ k, |γ b k - z k|)} ≤
        ENNReal.ofReal (A * Real.exp (-(κ * t))) := by
  have hw : 0 < width := hP.1
  have hc : 0 < c := hP.2.2.2.1
  set q : ℕ := 10 * d * width with hq
  have hq0 : 0 < q := Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hw
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  set κ₀ : ℝ := 8 * c / q with hκ₀
  have hκ₀0 : 0 < κ₀ := div_pos (by linarith) hq'
  obtain ⟨K, hK, hKb⟩ := exists_pow_mul_exp_neg_le hκ₀0 (2 * d + 1)
  refine ⟨((d : ℝ) + 2) * ((a : ℝ) + 1) ^ (2 * d + 1) * Real.exp (2 * c) * K, κ₀ / 2,
    mul_pos (by positivity) hK, half_pos hκ₀0, fun T t hr hfit hsize => ?_⟩
  refine (crossing_fail_le hP hd j i hij T (8 * t) hr hfit).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : (T.size : ℝ) + 1 ≤ ((a : ℝ) + 1) * ((t : ℝ) + 1) := by
    have : (T.size : ℝ) ≤ (a : ℝ) * ((t : ℝ) + 1) := by exact_mod_cast hsize
    nlinarith
  have hexp : Real.exp (-(c * ((8 * t / q - 1 : ℕ) : ℝ))) ≤
      Real.exp (2 * c) * Real.exp (-(κ₀ * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := ratio_sub_one_ge (8 * t) q hq0
    have h2 : κ₀ * t = c * (((8 * t : ℕ) : ℝ) / q) := by rw [hκ₀]; push_cast; ring
    have h5 := mul_le_mul_of_nonneg_left h1 hc.le
    rw [mul_sub] at h5
    linarith
  have hpow : ((T.size : ℝ) + 1) ^ (2 * d + 1) ≤
      ((a : ℝ) + 1) ^ (2 * d + 1) * ((t : ℝ) + 1) ^ (2 * d + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hs _
  have hKt := hKb t (Nat.cast_nonneg _)
  calc ((d : ℝ) + 2) * ((T.size : ℝ) + 1) ^ (2 * d + 1) *
        Real.exp (-(c * ((8 * t / q - 1 : ℕ) : ℝ)))
      ≤ ((d : ℝ) + 2) * (((a : ℝ) + 1) ^ (2 * d + 1) * ((t : ℝ) + 1) ^ (2 * d + 1)) *
          (Real.exp (2 * c) * Real.exp (-(κ₀ * t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hexp (Real.exp_nonneg _)
          (by positivity)
    _ = ((d : ℝ) + 2) * ((a : ℝ) + 1) ^ (2 * d + 1) * Real.exp (2 * c) *
          (((t : ℝ) + 1) ^ (2 * d + 1) * Real.exp (-(κ₀ * t))) := by ring
    _ ≤ ((d : ℝ) + 2) * ((a : ℝ) + 1) ^ (2 * d + 1) * Real.exp (2 * c) *
          (K * Real.exp (-(κ₀ / 2 * t))) := mul_le_mul_of_nonneg_left hKt (by positivity)
    _ = _ := by ring

/-- A walk that leaves the cube `x + Q_M`, starting from a vertex joined to `x` inside the cube,
passes through a vertex of the boundary of the cube joined to `x` inside the cube. -/
theorem exists_boundary_of_walk {ω : Configuration d} {x : Vertex d} {M : ℕ} :
    ∀ {a b : Vertex d} (w : (openGraph ω).Walk a b), a ∈ cubeAt x M →
      (openIn ω (cubeAt x M)).Reachable x a → b ∉ cubeAt x M →
      ∃ v ∈ cubeAt x M, (openIn ω (cubeAt x M)).Reachable x v ∧ ∃ i, |v i - x i| = M
  | _, _, .nil, ha, _, hb => absurd ha hb
  | a, _, .cons (v := c) h w, ha, hxa, hb => by
    by_cases hc : c ∈ cubeAt x M
    · exact exists_boundary_of_walk w hc (hxa.trans (SimpleGraph.Adj.reachable ⟨h, ha, hc⟩)) hb
    · refine ⟨a, ha, hxa, ?_⟩
      have hadj := ((openGraph_adj_iff ω a c).1 h).1
      rw [mem_cubeAt] at ha hc
      push Not at hc
      obtain ⟨i, hi⟩ := hc
      refine ⟨i, ?_⟩
      obtain ⟨h1a, h1b⟩ := abs_le.1 (abs_sub_le_one_of_nearestNeighbor_adj hadj i)
      obtain ⟨h2a, h2b⟩ := abs_le.1 (ha i)
      rw [abs_eq (by positivity)]
      rcases lt_abs.1 hi with hi | hi
      · left; omega
      · right; omega

/-- A connection inside a region is a connection in the open graph. -/
theorem reachable_openGraph_of_openIn {ω : Configuration d} {B : Set (Vertex d)} {a b : Vertex d}
    (h : (openIn ω B).Reachable a b) : (openGraph ω).Reachable a b := by
  apply SimpleGraph.Reachable.mono ?_ h
  intro u v huv
  exact huv.1

/-- A path of `ℓ^∞`-diameter at least `D` joining two vertices of a region inside it. -/
theorem exists_diameter_path_of_reachable {ω : Configuration d} {B : Set (Vertex d)}
    {a b : Vertex d} (h : (openIn ω B).Reachable a b) (ha : a ∈ B) {D : ℤ} (k : Fin d)
    (hD : D ≤ |b k - a k|) :
    ∃ n γ, IsSelectedOpenPath ω B (pathDiameterAtLeast D) n γ ∧ γ 0 = a := by
  obtain ⟨n, γ, h0, hlast, hsteps⟩ := exists_finPath_of_reachable h
  exact ⟨n, γ, ⟨⟨Fin.last n, 0, k, by rw [h0, hlast]; exact hD⟩, h0 ▸ ha, hsteps⟩, h0⟩

/-- **Finite clusters have exponentially small radius** (Grimmett, *Percolation*, Theorem (8.21)),
for `d ≥ 3`. Above the critical point, the open cluster of `x` is finite and reaches
`ℓ^∞`-distance `l` from `x` with probability at most `C exp(-c l)`. -/
theorem exists_finite_cluster_radius_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex d) (l : ℕ),
      latticeBondLaw d p {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
        ∃ y, (openGraph ω).Reachable x y ∧ ∃ i, (l : ℤ) ≤ |y i - x i|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * l))) := by
  have hd0 : 0 < d := by omega
  let j : Fin d := ⟨0, by omega⟩
  let i : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hp0 : 0 < (p : ℝ) := (criticalProbability_pos d).trans hp
  obtain ⟨width, ρ, c, hP⟩ :=
    (uniformCubeSlabConnectivity_of_criticalProbability_lt hd p hp).exists_slabParams j hp0
  obtain ⟨A, κ, hA, hκ, hcross⟩ := exists_crossing_fail_le_exp hP hd0 j i hij 5
  set q : ℕ := 10 * d * width with hq
  set r : ℝ := Real.exp (-κ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set C₁ : ℝ := A * Real.exp κ / (1 - r) with hC₁
  have hC₁0 : 0 < C₁ := div_pos (mul_pos hA (Real.exp_pos _)) (by linarith)
  refine ⟨C₁ + Real.exp (κ / 2 * (2 * (q + 1) : ℕ)), κ / 2, add_pos hC₁0 (Real.exp_pos _),
    half_pos hκ, fun x l => ?_⟩
  by_cases hl : l ≤ 2 * (q + 1)
  · exact measure_le_ofReal_exp_of_le _ _ (half_pos hκ).le (le_add_of_nonneg_left hC₁0.le)
      (by exact_mod_cast hl)
  push Not at hl
  set t₀ : ℕ := (l - 1) / 2 with ht₀
  have ht₀q : q + 1 ≤ t₀ := by omega
  have ht₀l : 2 * t₀ < l := by omega
  -- the events
  let G : ℕ → Set (Configuration d) := fun k =>
    {ω | HasCrossingComponentConnectingPaths ω (cubeIC x (2 * (2 ^ k * t₀))).vertices
      (fun b => ↑((cubeIC x (2 * (2 ^ k * t₀))).lowerFace b))
      (fun b => ↑((cubeIC x (2 * (2 ^ k * t₀))).upperFace b))
      (fun n γ => ∀ z : Vertex d, ∃ b : Fin (n + 1),
        ((8 * (2 ^ k * t₀) : ℕ) : ℤ) < 10 * ∑ k', |γ b k' - z k'|)}
  have hsub : {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
      ∃ y, (openGraph ω).Reachable x y ∧ ∃ i, (l : ℤ) ≤ |y i - x i|} ⊆ ⋃ k, (G k)ᶜ := by
    rintro ω ⟨hfin, y, hxy, i₀, hyl⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hcon
    have hpos : ∀ k, 0 < 2 ^ k * t₀ := fun k => Nat.mul_pos (by positivity) (by omega)
    have hG : ∀ k, ∃ root, IsCrossingRoot ω (cubeAt x (2 * (2 ^ k * t₀)))
        (fun b => ↑((cubeIC x (2 * (2 ^ k * t₀))).lowerFace b))
        (fun b => ↑((cubeIC x (2 * (2 ^ k * t₀))).upperFace b)) root ∧
        ConnectsSelectedPaths ω (cubeAt x (2 * (2 ^ k * t₀))) (cubeAt x (2 * (2 ^ k * t₀))) root
          (pathDiameterAtLeast (2 * ((2 ^ k * t₀ : ℕ) : ℤ))) := by
      intro k
      obtain ⟨root, h1, h2⟩ := HasCrossingComponentConnectingPaths.of_l1_radius_le (2 ^ k * t₀)
        (8 * (2 ^ k * t₀)) (hpos k) le_rfl (hcon k)
      rw [coe_cubeIC] at h1 h2
      exact ⟨root, h1, h2⟩
    choose root hroot hconn using hG
    have hxmem : ∀ M : ℕ, x ∈ cubeAt x M := fun M => mem_cubeAt.2 fun k => by simp
    -- the first root
    have h0 : (openGraph ω).Reachable x (root 0) := by
      obtain ⟨w⟩ := hxy
      have hyout : y ∉ cubeAt x (2 * (2 ^ 0 * t₀)) := by
        intro hy
        have h1 := mem_cubeAt.1 hy i₀
        simp only [pow_zero, one_mul] at h1
        have h2 : ((2 * t₀ : ℕ) : ℤ) < l := by exact_mod_cast ht₀l
        omega
      obtain ⟨v, hv, hxv, k, hvk⟩ := exists_boundary_of_walk w (hxmem _)
        (SimpleGraph.Reachable.refl _) hyout
      obtain ⟨n, γ, hγ, hγ0⟩ := exists_diameter_path_of_reachable hxv (hxmem _)
        (D := 2 * ((2 ^ 0 * t₀ : ℕ) : ℤ)) k (by rw [hvk]; norm_num)
      obtain ⟨z, -, hz1, hz2⟩ := hconn 0 n γ hγ.1 hγ.2.1 hγ.2.2
      rw [hγ0] at hz1
      exact reachable_openGraph_of_openIn (hz1.trans hz2.symm)
    -- consecutive roots
    have hstep : ∀ k, (openGraph ω).Reachable (root k) (root (k + 1)) := by
      intro k
      obtain ⟨⟨a, haB, haL, hra⟩, ⟨b, -, hbU, hrb⟩⟩ := (hroot k).2 j
      have ha' := (mem_cubeIC_lowerFace.1 (Finset.mem_coe.1 haL)).2
      have hb' := (mem_cubeIC_upperFace.1 (Finset.mem_coe.1 hbU)).2
      have hsubk : cubeAt x (2 * (2 ^ k * t₀)) ⊆ cubeAt x (2 * (2 ^ (k + 1) * t₀)) := by
        intro y hy
        rw [mem_cubeAt] at hy ⊢
        intro i'
        have := hy i'
        have hle : 2 * (2 ^ k * t₀) ≤ 2 * (2 ^ (k + 1) * t₀) := by
          have : 2 ^ k * t₀ ≤ 2 ^ (k + 1) * t₀ :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          omega
        have hle' : ((2 * (2 ^ k * t₀) : ℕ) : ℤ) ≤ ((2 * (2 ^ (k + 1) * t₀) : ℕ) : ℤ) := by
          exact_mod_cast hle
        linarith
      have hab := reachable_openIn_mono hsubk (hra.symm.trans hrb)
      obtain ⟨n, γ, hγ, hγ0⟩ := exists_diameter_path_of_reachable hab (hsubk haB)
        (D := 2 * ((2 ^ (k + 1) * t₀ : ℕ) : ℤ)) j (by
          rw [ha', hb']
          have : (x j + ((2 * (2 ^ k * t₀) : ℕ) : ℤ)) - (x j - ((2 * (2 ^ k * t₀) : ℕ) : ℤ)) =
              2 * ((2 ^ (k + 1) * t₀ : ℕ) : ℤ) := by
            push_cast
            ring
          rw [this, abs_of_nonneg (by positivity)])
      obtain ⟨z, -, hz1, hz2⟩ := hconn (k + 1) n γ hγ.1 hγ.2.1 hγ.2.2
      rw [hγ0] at hz1
      have hra' : (openGraph ω).Reachable (root k) a := reachable_openGraph_of_openIn hra
      exact hra'.trans (reachable_openGraph_of_openIn (hz1.trans hz2.symm))
    have hall : ∀ k, (openGraph ω).Reachable x (root k) := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih => exact ih.trans (hstep k)
    -- the cluster of `x` is unbounded
    obtain ⟨Bd, hBd⟩ := (hfin.image fun y => y j - x j).bddAbove
    set k : ℕ := Bd.toNat with hk
    obtain ⟨-, ⟨b, -, hbU, hrb⟩⟩ := (hroot k).2 j
    have hb' := (mem_cubeIC_upperFace.1 (Finset.mem_coe.1 hbU)).2
    have hxb : (openGraph ω).Reachable x b := (hall k).trans (reachable_openGraph_of_openIn hrb)
    have hle := hBd ⟨b, hxb, rfl⟩
    simp only [hb', add_sub_cancel_left] at hle
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    have hbig : 2 ^ k ≤ 2 * (2 ^ k * t₀) :=
      calc 2 ^ k = 2 ^ k * 1 := (mul_one _).symm
        _ ≤ 2 ^ k * t₀ := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 * (2 ^ k * t₀) := Nat.le_mul_of_pos_left _ (by norm_num)
    have hBdk : Bd ≤ (k : ℤ) := Int.self_le_toNat Bd
    have : ((2 ^ k : ℕ) : ℤ) ≤ ((2 * (2 ^ k * t₀) : ℕ) : ℤ) := by exact_mod_cast hbig
    have : (k : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hk2
    omega
  -- the probability bound
  set ρ₀ : ℝ := Real.exp (-(κ * t₀)) with hρ₀
  have hρ₀0 : 0 < ρ₀ := Real.exp_pos _
  have hρ₀r : ρ₀ ≤ r := by
    apply Real.exp_le_exp.2
    have : (1 : ℝ) ≤ t₀ := by exact_mod_cast (show 1 ≤ t₀ by omega)
    nlinarith
  have hρ₀1 : ρ₀ < 1 := hρ₀r.trans_lt hr1
  have hterm : ∀ k, latticeBondLaw d p (G k)ᶜ ≤ ENNReal.ofReal (A * ρ₀ * ρ₀ ^ k) := by
    intro k
    have h1 : 10 * d * width ≤ 8 * (2 ^ k * t₀) := by
      rw [← hq]
      have : t₀ ≤ 2 ^ k * t₀ := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have h2 : 8 * (2 ^ k * t₀) < 10 * d * (cubeIC x (2 * (2 ^ k * t₀))).size := by
      show 8 * (2 ^ k * t₀) < 10 * d * (2 * (2 * (2 ^ k * t₀)) + 1)
      have : 2 * (2 * (2 ^ k * t₀)) + 1 ≤ d * (2 * (2 * (2 ^ k * t₀)) + 1) :=
        Nat.le_mul_of_pos_left _ hd0
      calc 8 * (2 ^ k * t₀) < 10 * (2 * (2 * (2 ^ k * t₀)) + 1) := by omega
        _ ≤ 10 * (d * (2 * (2 * (2 ^ k * t₀)) + 1)) := by omega
        _ = _ := by ring
    have h3 : (cubeIC x (2 * (2 ^ k * t₀))).size ≤ 5 * (2 ^ k * t₀ + 1) := by
      show 2 * (2 * (2 ^ k * t₀)) + 1 ≤ 5 * (2 ^ k * t₀ + 1)
      omega
    refine (hcross (cubeIC x (2 * (2 ^ k * t₀))) (2 ^ k * t₀) h1 h2 h3).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hk1 : ((k + 1 : ℕ) : ℝ) * t₀ ≤ ((2 ^ k * t₀ : ℕ) : ℝ) := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      push_cast
      have : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
    have hpowk : ρ₀ * ρ₀ ^ k = Real.exp (-(κ * t₀)) ^ (k + 1) := by rw [hρ₀, pow_succ']
    rw [mul_assoc, hpowk, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hk1 hκ.le
    push_cast at this ⊢
    nlinarith
  have hsumm : Summable fun k : ℕ => A * ρ₀ * ρ₀ ^ k :=
    (summable_geometric_of_lt_one hρ₀0.le hρ₀1).mul_left _
  calc latticeBondLaw d p {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
        ∃ y, (openGraph ω).Reachable x y ∧ ∃ i, (l : ℤ) ≤ |y i - x i|}
      ≤ latticeBondLaw d p (⋃ k, (G k)ᶜ) := measure_mono hsub
    _ ≤ ∑' k, latticeBondLaw d p (G k)ᶜ := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (A * ρ₀ * ρ₀ ^ k) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' k, A * ρ₀ * ρ₀ ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm).symm
    _ ≤ ENNReal.ofReal ((C₁ + Real.exp (κ / 2 * (2 * (q + 1) : ℕ))) *
          Real.exp (-(κ / 2 * l))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ₀0.le hρ₀1]
        have hρl : ρ₀ ≤ Real.exp κ * Real.exp (-(κ / 2 * l)) := by
          rw [hρ₀, ← Real.exp_add]
          apply Real.exp_le_exp.2
          have : (l : ℝ) ≤ 2 * t₀ + 2 := by exact_mod_cast (show l ≤ 2 * t₀ + 2 by omega)
          nlinarith
        have h1r : 0 < 1 - r := by linarith
        have hinv : (1 - ρ₀)⁻¹ ≤ (1 - r)⁻¹ :=
          inv_anti₀ h1r (by linarith)
        calc A * ρ₀ * (1 - ρ₀)⁻¹ ≤ A * (Real.exp κ * Real.exp (-(κ / 2 * l))) * (1 - r)⁻¹ :=
              mul_le_mul (mul_le_mul_of_nonneg_left hρl hA.le) hinv
                (inv_nonneg.2 (by linarith)) (by positivity)
          _ = C₁ * Real.exp (-(κ / 2 * l)) := by rw [hC₁]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg _))
              (Real.exp_nonneg _)

/-- **Finite clusters have stretched-exponentially small volume**, for `d ≥ 3`: above the critical
point, the open cluster of `x` is finite with at least `n` vertices with probability at most
`C exp(-c n^{1/d})`. -/
theorem exists_finite_cluster_card_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex d) (n : ℕ),
      latticeBondLaw d p {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
        n ≤ {y | (openGraph ω).Reachable x y}.ncard} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (n : ℝ) ^ (d : ℝ)⁻¹))) := by
  obtain ⟨C, c, hC, hc, hrad⟩ := exists_finite_cluster_radius_le hd hp
  refine ⟨C * Real.exp c, c / 4, mul_pos hC (Real.exp_pos _), by positivity, fun x n => ?_⟩
  set v : ℝ := (n : ℝ) ^ (d : ℝ)⁻¹ with hv
  have hv0 : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hvn : v ^ d = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (NeZero.ne d)
  set l : ℕ := ⌊v / 4⌋₊ with hl
  have hlv : (l : ℝ) ≤ v / 4 := Nat.floor_le (by positivity)
  have hlv' : v / 4 - 1 < l := Nat.sub_one_lt_floor _
  have hsub : {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
      n ≤ {y | (openGraph ω).Reachable x y}.ncard} ⊆
      {ω | {y | (openGraph ω).Reachable x y}.Finite ∧
        ∃ y, (openGraph ω).Reachable x y ∧ ∃ i, (l : ℤ) ≤ |y i - x i|} := by
    rintro ω ⟨hfin, hn⟩
    refine ⟨hfin, ?_⟩
    by_contra h
    push Not at h
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · have hl0 : l = 0 := by
        rw [hl, hv, hn0]
        simp [Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne d)))]
      have := h x (SimpleGraph.Reachable.refl _) ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      simp [hl0] at this
    · have hcard := ncard_le_of_close (S := {y | (openGraph ω).Reachable x y}) x (D := l)
        (fun y hy k => h y hy k)
      have hlt : ((2 * l) ^ d : ℕ) < n := by
        have h2l : ((2 * l : ℕ) : ℝ) ≤ v / 2 := by push_cast; linarith
        have hpow := pow_le_pow_left₀ (by positivity) h2l d
        rw [div_pow, hvn] at hpow
        have h2d : (2 : ℝ) ≤ 2 ^ d := by
          calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne d))
        have hn1 : (0 : ℝ) < n := by exact_mod_cast hn0
        have : (n : ℝ) / 2 ^ d < n := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        exact_mod_cast hpow.trans_lt this
      omega
  refine (measure_mono hsub).trans ((hrad x l).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

end Rigidity.Percolation
