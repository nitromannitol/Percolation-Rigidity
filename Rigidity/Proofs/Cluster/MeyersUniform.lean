import Rigidity.Proofs.Cluster.MeyersPartitionBox
import Rigidity.Proofs.Cluster.PlanarMeyersHarmonic

/-!
# The Meyers estimate with the moment exponent chosen first

In the proof of Proposition 3.8 of Armstrong and Dario the exponents `ε` (from the Gehring lemma)
and `t = (2+ε)(1+ε)(d+1)/(2ε)` (of the moment of the cell sizes) depend only on the reverse Hölder
constant, and only the final constant depends on the bound `K` of the moment
`∑_{x ∈ □} size(cell(x))^t ≤ K |□|`. This order matters when the moment bound comes from a minimal
scale: Armstrong and Dario fix `t` first and then the minimal scale `𝓜_t(𝓡)`, whose constant
depends on `t`.

The theorems of this file restate `meyers_triadic`, `meyers_cluster_of_local`, `planar_meyers`,
`planar_meyers_clusterHarmonic` and `partition_meyers` in the form `∃ ε t, ∀ K, ∃ C`; the proofs
are those of the original statements, in which `ε` and `t` do not depend on `K`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {d : ℕ}

/-- **The Meyers estimate, with `ε` and `t` chosen before the moment bound** (Armstrong–Dario,
Proposition 3.8, deterministic part). As `meyers_triadic`, with the exponents `ε` and `t`
independent of the constant `K` of the moment bound `∑_{x ∈ □} size(cell(x))^t ≤ K |□|`. -/
theorem meyers_triadic_uniform (hd : 1 ≤ d) {A₀ : ℝ} (hA₀ : 1 ≤ A₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (x₀ : Vertex d) (G : Vertex d → ℝ) (s : Vertex d → ℕ), (∀ x, 0 ≤ G x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          avg (cube k y) G ≤
            A₀ * avg (enl 1 k y) (fun x => G x ^ ((d : ℝ) / (d + 1))) ^ (((d : ℝ) + 1) / d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => G x ^ (1 + ε / 2)) ≤ C * avg (enl 1 n x₀) G ^ (1 + ε / 2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set θ : ℝ := (d : ℝ) / (d + 1) with hθdef
  have hθ0 : 0 < θ := div_pos hd' (by linarith)
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one (by linarith)]
    linarith
  have hinv : 1 / θ = ((d : ℝ) + 1) / d := by rw [hθdef, one_div_div]
  have h1θ : 0 < 1 / θ := one_div_pos.mpr hθ0
  set A : ℝ := A₀ * ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) with hAdef
  have hA : 1 ≤ A := by
    have h1 : 1 ≤ ((3 : ℝ) ^ (2 * d)) ^ (1 / θ) :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num)) h1θ.le
    nlinarith
  obtain ⟨ε, hε0, -, CG, hCG0, hGeh⟩ := gehring_triadic (d := d) hθ0 hθ1 hA (j := 2) (by norm_num)
  have hεne : ε ≠ 0 := hε0.ne'
  have h1εne : 1 + ε ≠ 0 := by positivity
  have h2εne : 1 + ε / 2 ≠ 0 := by positivity
  set p : ℝ := (1 + ε) / (1 + ε / 2) with hp
  set q : ℝ := 2 * (1 + ε) / ε with hq
  have hp1 : 1 < p := by
    rw [hp, one_lt_div (by linarith)]
    linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    rw [hp, hq, inv_div, inv_div]
    field_simp
    ring
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set α : ℝ := 1 / θ * (1 + ε / 2) with hα
  have hα0 : 0 < α := mul_pos h1θ (by linarith)
  set t : ℝ := d * α * q with ht
  have ht0 : 0 < t := mul_pos (mul_pos hd' hα0) hq0
  refine ⟨ε, hε0, t, ht0, fun K hK => ?_⟩
  have hC0 : 0 ≤ CG ^ (1 / p) * K ^ (1 / q) :=
    mul_nonneg (Real.rpow_nonneg hCG0 _) (Real.rpow_nonneg hK _)
  refine ⟨CG ^ (1 / p) * K ^ (1 / q), hC0, ?_⟩
  intro n x₀ G s hG hcell hnb hΩcell hRH hmom
  set f := cellAvg s G θ with hf
  set g : Vertex d → ℝ := fun x => f x ^ (1 / θ) with hg
  have hf0 : ∀ x, 0 ≤ f x := cellAvg_nonneg s hG θ
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (hf0 x) _
  -- Step 1: the reverse Hölder inequality for `g` with enlargement `9□'`
  have hRH' : ∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
      avg (cube k y) G ≤ A₀ * avg (enl 1 k y) (fun x => G x ^ θ) ^ (1 / θ) := by
    intro k y hk hsub
    rw [hinv]
    exact hRH k y hk hsub
  have hRHg : ∀ k y, enl 2 k y ⊆ enl 1 n x₀ →
      avg (cube k y) g ≤ A * avg (enl 2 k y) (fun x => g x ^ θ) ^ (1 / θ) :=
    fun k y hsub => reverse_holder_cellAvg hcell hnb hG hθ0 hθ1.le hA₀ hRH' k y hsub
  -- Step 2: Gehring's lemma for `g`
  have hgeh := hGeh n x₀ g hg0 hRHg
  set a := avg (enl 1 n x₀) G with ha
  have hΩpos : (0 : ℝ) < (enl 1 n x₀).card := by
    rw [card_enl]
    positivity
  have ha0 : 0 ≤ a := div_nonneg (Finset.sum_nonneg fun x _ => hG x) hΩpos.le
  have hgΩ : avg (enl 1 n x₀) g ≤ a :=
    div_le_div_of_nonneg_right (sum_cellAvg_rpow_le hcell hG hθ0 hθ1.le hΩcell)
      (Nat.cast_nonneg _)
  have hgΩ0 : 0 ≤ avg (enl 1 n x₀) g :=
    div_nonneg (Finset.sum_nonneg fun x _ => hg0 x) hΩpos.le
  have hQpos : (0 : ℝ) < (cube n x₀).card := card_cube_pos n x₀
  have h1ε : 0 ≤ 1 + ε := by linarith
  have hsumg : ∑ x ∈ cube n x₀, g x ^ (1 + ε) ≤ (cube n x₀).card * (CG * a ^ (1 + ε)) := by
    have h1 : avg (cube n x₀) (fun x => g x ^ (1 + ε)) ≤ CG * a ^ (1 + ε) :=
      hgeh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hgΩ0 hgΩ h1ε) hCG0)
    rw [avg, div_le_iff₀ hQpos] at h1
    linarith
  -- Step 3: Hölder's inequality removes the cell sizes
  set w : Vertex d → ℝ := fun x => ((cube (s x) x).card : ℝ) ^ α with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpt : ∀ x, G x ^ (1 + ε / 2) ≤ g x ^ (1 + ε / 2) * w x := by
    intro x
    have hcpos := card_cube_pos (s x) x
    have h1 : G x ^ θ ≤ (cube (s x) x).card * f x := by
      have h2 : G x ^ θ ≤ ∑ z ∈ cube (s x) x, G z ^ θ :=
        Finset.single_le_sum (fun z _ => Real.rpow_nonneg (hG z) θ) (mem_cube_self _ x)
      simp only [hf, cellAvg, avg]
      rw [mul_div_cancel₀ _ hcpos.ne']
      exact h2
    have h3 : G x ≤ ((cube (s x) x).card : ℝ) ^ (1 / θ) * g x := by
      have h4 := Real.rpow_le_rpow (Real.rpow_nonneg (hG x) θ) h1 h1θ.le
      rwa [← Real.rpow_mul (hG x), mul_one_div_cancel hθ0.ne', Real.rpow_one,
        Real.mul_rpow (Nat.cast_nonneg _) (hf0 x)] at h4
    have h5 := Real.rpow_le_rpow (hG x) h3 (by linarith : (0 : ℝ) ≤ 1 + ε / 2)
    rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hg0 x),
      ← Real.rpow_mul (Nat.cast_nonneg _)] at h5
    simp only [hw, hα]
    linarith
  have hHold := Real.inner_le_Lp_mul_Lq_of_nonneg (cube n x₀) hpq
    (f := fun x => g x ^ (1 + ε / 2)) (g := w) (fun x _ => Real.rpow_nonneg (hg0 x) _)
    (fun x _ => hw0 x)
  have hpow1 : ∀ x, (g x ^ (1 + ε / 2)) ^ p = g x ^ (1 + ε) := by
    intro x
    rw [← Real.rpow_mul (hg0 x)]
    congr 1
    rw [hp]
    field_simp
  have hpow2 : ∀ x, w x ^ q = ((3 : ℝ) ^ s x) ^ t := by
    intro x
    simp only [hw]
    rw [← Real.rpow_mul (Nat.cast_nonneg _), card_cube, ← Real.rpow_natCast ((3 : ℝ) ^ s x) d,
      ← Real.rpow_mul (by positivity), ht]
    congr 1
    ring
  simp only [hpow1, hpow2] at hHold
  have hsumG : ∑ x ∈ cube n x₀, G x ^ (1 + ε / 2) ≤
      ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) * (K * (cube n x₀).card) ^ (1 / q) := by
    calc ∑ x ∈ cube n x₀, G x ^ (1 + ε / 2)
        ≤ ∑ x ∈ cube n x₀, g x ^ (1 + ε / 2) * w x := Finset.sum_le_sum fun x _ => hpt x
      _ ≤ (∑ x ∈ cube n x₀, g x ^ (1 + ε)) ^ (1 / p) *
            (∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t) ^ (1 / q) := hHold
      _ ≤ ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) *
            (K * (cube n x₀).card) ^ (1 / q) := by
          refine mul_le_mul (Real.rpow_le_rpow (Finset.sum_nonneg fun x _ =>
            Real.rpow_nonneg (hg0 x) _) hsumg (one_div_pos.mpr hp0).le)
            (Real.rpow_le_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
              hmom (one_div_pos.mpr hq0).le) (Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
                Real.rpow_nonneg (by positivity) _) _)
            (Real.rpow_nonneg (mul_nonneg hQpos.le (mul_nonneg hCG0 (Real.rpow_nonneg ha0 _))) _)
  -- the powers of `|□|` and of `a`
  have hexp : (1 + ε) * (1 / p) = 1 + ε / 2 := by
    rw [hp]
    field_simp
  have hpq' : 1 / p + 1 / q = 1 := by
    rw [one_div, one_div]
    exact hpq.inv_add_inv_eq_one
  have hfinal : ((cube n x₀).card * (CG * a ^ (1 + ε))) ^ (1 / p) * (K * (cube n x₀).card) ^ (1 / q)
      = (cube n x₀).card * (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by
    rw [Real.mul_rpow hQpos.le (mul_nonneg hCG0 (Real.rpow_nonneg ha0 _)),
      Real.mul_rpow hCG0 (Real.rpow_nonneg ha0 _), Real.mul_rpow hK hQpos.le,
      ← Real.rpow_mul ha0, hexp]
    have hQ : ((cube n x₀).card : ℝ) ^ (1 / p) * ((cube n x₀).card : ℝ) ^ (1 / q) =
        (cube n x₀).card := by
      rw [← Real.rpow_add hQpos, hpq', Real.rpow_one]
    calc ((cube n x₀).card : ℝ) ^ (1 / p) * (CG ^ (1 / p) * a ^ (1 + ε / 2)) *
          (K ^ (1 / q) * ((cube n x₀).card : ℝ) ^ (1 / q))
        = (((cube n x₀).card : ℝ) ^ (1 / p) * ((cube n x₀).card : ℝ) ^ (1 / q)) *
            (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by ring
      _ = (cube n x₀).card * (CG ^ (1 / p) * K ^ (1 / q) * a ^ (1 + ε / 2)) := by rw [hQ]
  rw [hfinal] at hsumG
  rw [avg, div_le_iff₀ hQpos]
  linarith

/-- **The Meyers estimate on a cluster with a weight for each cube, with `ε` and `t` chosen before
the moment bound** (Armstrong–Dario, Proposition 3.8, deterministic part). As
`meyers_cluster_of_local`, with `ε` and `t` independent of `K`. -/
theorem meyers_cluster_of_local_uniform (hd : 1 ≤ d) {CS CG : ℝ} (hCS : 0 ≤ CS)
    (hCG : 0 ≤ CG) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (n : ℕ) (x₀ : Vertex d) (U₀ : Finset (Vertex d))
        (u : Vertex d → ℝ) (s : Vertex d → ℕ),
        (∀ x ∈ U₀, x ∈ enl 1 n x₀ → (∀ y, (openGraph ω).Adj x y → y ∈ U₀) →
          openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          ∃ (U' : Finset (Vertex d)) (size : Vertex d → ℝ), (∀ x, 0 ≤ size x) ∧
            U' ⊆ enl 1 k y ∧ U' ⊆ U₀ ∧
            (∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U') ∧
            (∀ x ∈ U₀, x ∈ cube k y → x ∈ U') ∧ ClusterSobolevTwo ω U' size CS ∧
            ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2) := by
  set A₀ : ℝ := max 1 (8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) *
    (3 : ℝ) ^ (d + 2)) with hA₀
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_triadic_uniform (d := d) hd (le_max_left 1 _) (A₀ := A₀)
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω n x₀ U₀ u s hu hcell hnb hΩ hcubes hmom
  refine hMK n x₀ (clusterEnergy ω U₀ u) s (clusterEnergy_nonneg ω U₀ u) hcell hnb hΩ ?_ hmom
  intro k y hk hsub
  obtain ⟨U', size, hsize, h1, h2, h3, h4, h5, h6⟩ := hcubes k y hk hsub
  have hrh := reverse_holder_clusterEnergy_local ω (by omega) U₀ u k y
    (fun x hx hxe hall => hu x hx (hsub hxe) hall) U' h1 h2 h3 h4 size hsize hCS hCG h5 h6
  refine hrh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ?_ _))
  exact div_nonneg (Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (clusterEnergy_nonneg ω U₀ u x) _) (Nat.cast_nonneg _)

/-- **The cluster of the triple `3□'` with its Sobolev weight, in the plane.** There is `C_S` such
that, on the planar partition event, for a triadic cube `V ⊇ 3□'`, `□' = cube k y`, whose triple
has planar partition cubes of scale at most `k` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|`, the
cluster `C(3□')` of the integer square `enlSquare k y` lies in `𝒞(V) ∩ 3□'`, is closed under open
edges inside `3□'`, contains `𝒞(V) ∩ □'` and carries a Sobolev inequality with constant `C_S` and a
weight whose `8`-th moment is at most `256 C_G |3□'|`. These are the cube hypotheses of
`meyers_cluster_of_local` (the step of the proof of `planar_meyers` that does not involve the
moment bound of the cells). -/
theorem exists_planarBox_meyers_cube :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration 2), PlanarPartitionEvent ω →
      ∀ (V : TriadicCube 2) (k : ℕ) (y : Vertex 2),
      (↑(enl 1 k y) : Set (Vertex 2)) ⊆ V.vertices →
      (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) →
      ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2) →
      ∃ (U' : Finset (Vertex 2)) (size : Vertex 2 → ℝ), (∀ x, 0 ≤ size x) ∧
        U' ⊆ enl 1 k y ∧ U' ⊆ clusterVertices ω V ∧
        (∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U') ∧
        (∀ x ∈ clusterVertices ω V, x ∈ cube k y → x ∈ U') ∧ ClusterSobolevTwo ω U' size CS ∧
        ∑ x ∈ U', size x ^ (2 * ((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) + 2)) ≤
          256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_planarBox_sum_sq_le
  refine ⟨K₀, hK₀, fun {CG} hCG ω hP V k y hV hres hreach => ?_⟩
  have hBr := planarBoxResolved_enlSquare hP hres
  have hB : (enlSquare k y).size = 3 ^ (k + 1) := rfl
  set B := enlSquare k y with hBdef
  set U' := boxClusterVertices ω B with hU'def
  set P := planarBoxCoarseData hP B hBr with hPdef
  set weight : Vertex 2 → ℝ := fun z => ((3 : ℝ) ^ P.reachScale z) ^ 2 +
    (3 : ℝ) ^ P.pairReachScale z with hweight
  have hw0 : ∀ z, 0 ≤ weight z := fun z => by positivity
  set size : Vertex 2 → ℝ := fun z => weight z ^ ((1 : ℝ) / 4) with hsizedef
  have hsize4 : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) = weight z := fun z => by
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    norm_num
  have hU'E : ∀ z ∈ U', z ∈ enl 1 k y := fun z hz =>
    mem_enlSquare_vertices.1 (Finset.mem_filter.1 hz).1
  have hRHS : ENNReal.ofReal CG * 3 ^ ((k + 1) * 2) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (by norm_num))
  have hfin : ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≠ ∞ := ne_top_of_le_ne_top hRHS hreach
  have hzfin : ∀ z ∈ enl 1 k y, planarReach ω z ≠ ∞ := by
    intro z hz htop
    apply hfin
    refine top_unique ?_
    calc (⊤ : ℝ≥0∞) = planarReach ω z ^ 8 := by rw [htop, ENNReal.top_pow (by norm_num)]
      _ ≤ ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 :=
          Finset.single_le_sum (f := fun z => planarReach ω z ^ 8) (fun _ _ => bot_le) hz
  have hR : ∀ z ∈ U', weight z ≤ 4 * (planarReach ω z).toReal ^ 2 := by
    intro z hz
    have hne := hzfin z (hU'E z hz)
    have h1 : (3 : ℝ) ^ P.reachScale z ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono hne (three_pow_reachScale_le_planarReach_box hP hBr hz)
      simpa using this
    have h2 : (3 : ℝ) ^ P.pairReachScale z ≤ 3 * (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hne)
        (three_pow_pairReachScale_le_planarReach_box hP hBr z)
      simpa [ENNReal.toReal_mul] using this
    have h3 : 1 ≤ (planarReach ω z).toReal := by
      have := ENNReal.toReal_mono hne (one_le_planarReach hP z)
      simpa using this
    have h0 : 0 ≤ (3 : ℝ) ^ P.reachScale z := by positivity
    have hsq : ((3 : ℝ) ^ P.reachScale z) ^ 2 ≤ (planarReach ω z).toReal ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have hRR : (planarReach ω z).toReal ≤ (planarReach ω z).toReal ^ 2 := by nlinarith
    show ((3 : ℝ) ^ P.reachScale z) ^ 2 + (3 : ℝ) ^ P.pairReachScale z ≤
      4 * (planarReach ω z).toReal ^ 2
    linarith
  have hmomR : ∑ z ∈ U', weight z ^ ((4 : ℕ) : ℝ) ≤ 256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
    simp only [Real.rpow_natCast]
    calc ∑ z ∈ U', weight z ^ 4 ≤ ∑ z ∈ U', 256 * (planarReach ω z).toReal ^ 8 :=
          Finset.sum_le_sum fun z hz => by
            calc weight z ^ 4 ≤ (4 * (planarReach ω z).toReal ^ 2) ^ 4 :=
                  pow_le_pow_left₀ (hw0 z) (hR z hz) 4
              _ = 256 * (planarReach ω z).toReal ^ 8 := by ring
      _ ≤ ∑ z ∈ enl 1 k y, 256 * (planarReach ω z).toReal ^ 8 :=
          Finset.sum_le_sum_of_subset_of_nonneg hU'E (fun z _ _ => by positivity)
      _ = 256 * (∑ z ∈ enl 1 k y, planarReach ω z ^ 8).toReal := by
          rw [ENNReal.toReal_sum (fun z hz => ENNReal.pow_ne_top (hzfin z hz)), Finset.mul_sum]
          simp only [ENNReal.toReal_pow]
      _ ≤ 256 * (ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hRHS hreach) (by norm_num)
      _ = 256 * CG * (3 : ℝ) ^ ((k + 1) * 2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCG, ENNReal.toReal_pow,
            ENNReal.toReal_ofNat]
          ring
  refine ⟨U', size, fun z => Real.rpow_nonneg (hw0 z) _, hU'E, ?_, ?_, ?_, ?_, ?_⟩
  · exact boxClusterVertices_subset_clusterVertices fun x hx =>
      hV (Finset.mem_coe.2 (mem_enlSquare_vertices.1 hx))
  · intro z hz w hadj hw
    exact mem_boxClusterVertices.2 (mem_planarBoxCluster_of_adj hP hBr
      (mem_boxClusterVertices.1 hz) hadj (mem_enlSquare_vertices.2 hw))
  · exact fun x hx hxc => mem_boxClusterVertices_of_mem_cube hP hBr hx hxc
  · intro w hw
    have h := hSobK ω hP B (by rw [hB]; positivity) hBr w hw
    rw [lowerSobolevTwo_two]
    have hterm : ∀ z, size z ^ (2 * ((2 : ℕ) : ℝ)) * clusterGradSq ω U' w z ^ ((1 : ℝ) / 2) =
        weight z * gradNormIn (openGraph ω) U' w z := fun z => by
      rw [hsize4, gradNormIn_openGraph_eq, Real.sqrt_eq_rpow]
    rw [Finset.sum_congr rfl fun z _ => hterm z, show (2 : ℝ) / 1 = 2 by norm_num, Real.rpow_two]
    exact h
  · refine (Finset.sum_congr rfl fun z _ => ?_).trans_le hmomR
    rw [hsizedef, ← Real.rpow_mul (hw0 z)]
    congr 1
    push_cast
    ring

/-- **The Meyers estimate on planar clusters, with `ε` and `t` chosen before the moment bound**
(Armstrong–Dario, Proposition 3.8, deterministic part, in dimension two). As `planar_meyers`, with
the exponents `ε` and `t` depending only on `C_G`, and the constant `C` on `C_G` and `K`. -/
theorem planar_meyers_uniform {CG : ℝ} (hCG : 0 ≤ CG) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2) (n : ℕ)
        (x₀ : Vertex 2) (u : Vertex 2 → ℝ) (s : Vertex 2 → ℕ),
        (↑(enl 1 n x₀) : Set (Vertex 2)) ⊆ V.vertices →
        (∀ x ∈ clusterVertices ω V, x ∈ enl 1 n x₀ →
          (∀ y, (openGraph ω).Adj x y → y ∈ clusterVertices ω V) → openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω (clusterVertices ω V) u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω (clusterVertices ω V) u) ^ (1 + ε / 2) := by
  obtain ⟨CS, hCS, hcube⟩ := exists_planarBox_meyers_cube
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_cluster_of_local_uniform (d := 2) (by norm_num) hCS
    (CG := 256 * CG) (by positivity)
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω hP V n x₀ u s hV hu hcell hnb hΩ hcubes hmom
  refine hMK ω n x₀ (clusterVertices ω V) u s hu hcell hnb hΩ (fun k y hk hsub => ?_) hmom
  obtain ⟨hres, hreach⟩ := hcubes k y hk hsub
  exact hcube hCG ω hP V k y (fun x hx => hV (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 hx))))
    hres hreach

/-- **The planar Meyers estimate for the functions of `A_*(V)`, with `ε` and `t` chosen before the
moment bound** (Armstrong–Dario, Proposition 3.8, deterministic part, in dimension two). As
`planar_meyers_clusterHarmonic`, with `ε` and `t` independent of `K`. -/
theorem planar_meyers_clusterHarmonic_uniform {CG : ℝ} (hCG : 0 ≤ CG) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2) := by
  obtain ⟨ε, hε, t, ht, hM⟩ := planar_meyers_uniform hCG
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω hP V hV w hw n x₀ s hint hcell hnb hΩ hcubes hmom
  have hsub : (↑(enl 1 n x₀) : Set (Vertex 2)) ⊆ V.vertices := fun x hx =>
    hint x (Finset.mem_coe.1 hx) x fun i => by simp
  exact hMK ω hP V n x₀ (clusterExtend ω V w) s hsub
    (fun x hx hxe _ => openLaplacian_clusterExtend_eq_zero hP hV hw hx (hint x hxe))
    hcell hnb hΩ hcubes hmom

/-- **The cluster of the triple `3□'` with its Sobolev weight, in every dimension `d ≥ 2`.** As
`exists_planarBox_meyers_cube`, for the crossing cluster `𝒞_*(V)` of a resolved cube and the cluster
of the triple `3□'`, whose partition cubes have scale less than `k`. -/
theorem exists_partitionBox_meyers_cube (hd : 2 ≤ d) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration d), PartitionEvent ω →
      ∀ (V : TriadicCube d), PartitionResolved ω V → ∀ (k : ℕ) (y : Vertex d),
      (↑(enl 1 k y) : Set (Vertex d)) ⊆ V.vertices →
      (∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) →
      ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) ≤
        ENNReal.ofReal CG * 3 ^ ((k + 1) * d) →
      ∃ (U' : Finset (Vertex d)) (size : Vertex d → ℝ), (∀ x, 0 ≤ size x) ∧
        U' ⊆ enl 1 k y ∧ U' ⊆ crossingClusterVertices ω V ∧
        (∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U') ∧
        (∀ x ∈ crossingClusterVertices ω V, x ∈ cube k y → x ∈ U') ∧
        ClusterSobolevTwo ω U' size CS ∧
        ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d) := by
  have hd0 : 0 < d := by omega
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_clusterSobolevTwo_box hd
  refine ⟨K₀, hK₀, fun {CG} hCG ω hP V hV k y hVsub hres hreach => ?_⟩
  have hBr := partitionBoxResolved_enlSquare hP hres
  set B := enlSquare k y with hBdef
  have hBpos : 0 < B.size := by
    change 0 < 3 ^ (k + 1)
    positivity
  set U' := partitionBoxCluster ω B with hU'def
  set P := partitionBoxCoarseData hd0 hP B hBr with hPdef
  set size : Vertex d → ℝ := fun z => (3 : ℝ) ^ P.reachScale z with hsizedef
  have hU'E : ∀ z ∈ U', z ∈ enl 1 k y := fun z hz =>
    mem_enlSquare_vertices.1 (Finset.mem_filter.1 hz).1
  have hBV : (↑B.vertices : Set (Vertex d)) ⊆ V.vertices := fun z hz =>
    hVsub (Finset.mem_coe.2 (mem_enlSquare_vertices.1 (Finset.mem_coe.1 hz)))
  have hN : (2 * (d : ℝ) * ((d : ℝ) + 2)) = ((2 * d * (d + 2) : ℕ) : ℝ) := by push_cast; ring
  have hmomR : ∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d) := by
    have hterm : ∀ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        partitionReach ω z ^ (2 * d * (d + 2)) := by
      intro z hz
      rw [hN, Real.rpow_natCast, hsizedef, ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      exact pow_le_pow_left₀ zero_le (three_pow_reachScale_le_partitionReach_box hd0 hP hBr hz) _
    have hsum : ENNReal.ofReal (∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun z _ => Real.rpow_nonneg (by positivity) _]
      calc ∑ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)))
          ≤ ∑ z ∈ U', partitionReach ω z ^ (2 * d * (d + 2)) := Finset.sum_le_sum hterm
        _ ≤ ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hU'E fun _ _ _ => zero_le
        _ ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * d) := hreach
        _ = ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
            rw [ENNReal.ofReal_mul hCG, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  refine ⟨U', size, fun z => by positivity, hU'E, ?_, ?_, ?_, ?_, ?_⟩
  · exact partitionBoxCluster_subset_crossingClusterVertices hd0 hP hBr hV hBV
  · intro z hz w hadj hw
    exact mem_partitionBoxCluster_of_adj hd0 hP hBr hz hadj (mem_enlSquare_vertices.2 hw)
  · exact fun x hx hxc => mem_partitionBoxCluster_of_mem_cube hd0 hP hV hres hx hxc
  · exact hSobK ω hP B hBpos hBr
  · exact hmomR

/-- **The Meyers estimate on the crossing clusters of the partition into good cubes, with `ε` and
`t` chosen before the moment bound** (Armstrong–Dario, Proposition 3.8, deterministic part, in
every dimension `d ≥ 2`). As `partition_meyers`, with `ε` and `t` independent of `K`. -/
theorem partition_meyers_uniform (hd : 2 ≤ d) {CG : ℝ} (hCG : 0 ≤ CG) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (_ : PartitionEvent ω) (V : TriadicCube d)
        (_ : PartitionResolved ω V) (n : ℕ) (x₀ : Vertex d) (u : Vertex d → ℝ)
        (s : Vertex d → ℕ),
        (↑(enl 1 n x₀) : Set (Vertex d)) ⊆ V.vertices →
        (∀ x ∈ crossingClusterVertices ω V, x ∈ enl 1 n x₀ →
          (∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω V) →
            openLaplacian ω u x = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) ∧
            ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) ≤
              ENNReal.ofReal CG * 3 ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (crossingClusterVertices ω V) u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω (crossingClusterVertices ω V) u) ^ (1 + ε / 2) := by
  obtain ⟨CS, hCS, hcube⟩ := exists_partitionBox_meyers_cube hd
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_cluster_of_local_uniform (d := d) (by omega) hCS hCG
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω hP V hV n x₀ u s hVsub hu hcell hnb hΩ hcubes hmom
  refine hMK ω n x₀ (crossingClusterVertices ω V) u s hu hcell hnb hΩ
    (fun k y hk hsub => ?_) hmom
  obtain ⟨hres, hreach⟩ := hcubes k y hk hsub
  exact hcube hCG ω hP V hV k y
    (fun x hx => hVsub (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 hx)))) hres hreach

end Rigidity.Proofs.Cluster
