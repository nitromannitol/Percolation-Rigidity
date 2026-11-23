import Rigidity.Proofs.Regularity.PlanarHarmonicApproximation

/-!
# Armstrong–Dario, Lemma 7.1, in dimension two: from squares to balls

Armstrong and Dario (arXiv:1609.09431v2) prove Lemma 7.1 on the triadic cubes `□_m` and use it on
balls at the start of the proof of Lemma 7.3. On `ℤ²`, for a function `f` (the coarsening
`[u]_𝒫`) and nonnegative quantities `Γ_j` (the oscillation
`inf_a |□_j|^{-1/2} ‖u - a‖_{L²(𝒞_*(□_j))}` of `u` on the cluster), the proof of Lemma 7.1 gives,
for `3^j` above a scale `X₀` and `□_{j + 3}` inside the domain,

* (7.3) `inf_{w ∈ Ā(□_m)} ‖f - w‖_{L̲²(□_m)} ≤ C₁ 3^{-m α} Γ_{m + 3}`;
* the inequality of Step 4, `Γ_j ≤ inf_a ‖f - a‖_{L̲²(□_j)} + K 3^{-j} Γ_{j + 3}`, from (7.4) and
  the triangle inequality;
* and, on the whole domain `B_R`, `Γ_j ≤ (R / 3^j) B` with
  `B = inf_a R^{-1} ‖u - a‖_{L²(𝒞_∞ ∩ B_R)}`.

The iteration of Step 4 (`le_sum_squareIterCoeff`) and the comparison of the norms on squares and
balls give the harmonic approximation hypothesis of Lemma 7.2 on the balls of the lattice with
`E = B / R` (`harmonicApproximation_of_squares`). For `r ∈ [X, R / A]` the ball `B_r` lies in the
square `□_m` with `2 r ≤ 3^m < 6 r`; the iteration runs from `m + 3` while `□_{m + 3 + 3 n}` stays
in the domain, so that `n ≥ 1` once `A ≥ 4374 L`; the oscillations of `f` on the squares
`□_{m + 3 + 3 k}` are bounded by the excess over the constants on balls of radii in `[A r, R]`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- **A ball inside a square**, for the distance to the lattice harmonic functions: if `B_r ⊆ □_m`
and `□_j ⊆ B_r`, the distance on `B_r` is at most `3^m / 3^j` times the one on `□_m`. -/
theorem ballDist_le_squareHarmonicDist {r : ℝ} {m j : ℕ}
    (hsub : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        y ∈ triadicCubeFinset 2 m 0)
    (hj : (3 : ℝ) ^ j ≤ r) (f : Vertex 2 → ℝ) :
    ballDist (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent 2 => f x.val) ≤ (3 : ℝ) ^ m / 3 ^ j * squareHarmonicDist m f := by
  haveI : Nonempty (squareHarmonic m) := ⟨⟨0, zero_mem_squareHarmonic m⟩⟩
  rw [squareHarmonicDist, Real.mul_iInf_of_nonneg (by positivity)]
  refine le_ciInf fun F => ?_
  have hv : (fun x : latticeComponent 2 => F.1 x.val) ∈ latticeHarmonicClass 0 r :=
    ⟨F.1, fun _ => rfl, fun y hy => F.2 y (hsub y hy)⟩
  have hbdd : BddBelow (Set.range fun v : latticeHarmonicClass (0 : Vertex 2) r =>
      componentBallSeminorm (latticeComponent 2) 0 r
        ((fun x : latticeComponent 2 => f x.val) - (v : latticeComponent 2 → ℝ))) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact apply_nonneg _ _⟩
  calc ballDist (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent 2 => f x.val)
      ≤ componentBallSeminorm (latticeComponent 2) 0 r
          ((fun x : latticeComponent 2 => f x.val) - fun x : latticeComponent 2 => F.1 x.val) :=
        ciInf_le hbdd ⟨_, hv⟩
    _ = componentBallL2 (latticeComponent 2) 0 r
          (fun x : latticeComponent 2 => (f - F.1) x.val) := rfl
    _ ≤ (3 : ℝ) ^ m / 3 ^ j * squareL2 m (f - F.1) := componentBallL2_le_squareL2 hsub hj _

/-- **A square inside a ball**, for the oscillation: if `3^j ≤ s`, the oscillation on `□_j` is at
most `(2 s + 3) / 3^j` times the excess over the constants on the lattice ball `B_s`. -/
theorem squareOsc_le_ballExcess {s : ℝ} {j : ℕ} (hj : (3 : ℝ) ^ j ≤ s) (f : Vertex 2 → ℝ) :
    squareOsc j f ≤ (2 * s + 3) / 3 ^ j *
      ballExcess (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) := by
  have h3 : (0 : ℝ) < 3 ^ j := by positivity
  have hs : 0 ≤ s := h3.le.trans hj
  have hK : 0 ≤ (2 * s + 3) / 3 ^ j := by positivity
  rw [ballExcess, Real.mul_iInf_of_nonneg hK]
  refine le_ciInf fun w => ?_
  obtain ⟨c, hc⟩ := w.2
  calc squareOsc j f ≤ squareL2 j (fun y => f y - c) := squareOsc_le j f c
    _ ≤ (2 * s + 3) / 3 ^ j * componentBallL2 (latticeComponent 2) 0 s
          (fun x : latticeComponent 2 => (fun y => f y - c) x.val) :=
        squareL2_le_componentBallL2 hj _
    _ = (2 * s + 3) / 3 ^ j * componentBallSeminorm (latticeComponent 2) 0 s
          ((fun x : latticeComponent 2 => f x.val) - (w : latticeComponent 2 → ℝ)) := by
        rw [componentBallSeminorm_apply]
        congr 2
        funext x
        simp [hc x]

/-- A power of three between `2 r` and `6 r`. -/
theorem exists_three_pow_near {r : ℝ} (hr : 1 ≤ r) :
    ∃ m : ℕ, 2 * r ≤ 3 ^ m ∧ (3 : ℝ) ^ m < 6 * r := by
  classical
  have hex : ∃ m : ℕ, 2 * r ≤ (3 : ℝ) ^ m :=
    (pow_unbounded_of_one_lt (2 * r) (by norm_num : (1 : ℝ) < 3)).imp fun _ h => h.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; linarith
  · have hlt := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at hlt
    have e : (3 : ℝ) ^ Nat.find hex = 3 * 3 ^ (Nat.find hex - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; linarith

/-- The coefficients `∏_{i < k} K / 3^{j + 3 i}` of the iteration of Step 4. -/
noncomputable def squareIterCoeff (K : ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => squareIterCoeff K j k * (K / 3 ^ (j + 3 * k))

theorem squareIterCoeff_nonneg {K : ℝ} (hK : 0 ≤ K) (j k : ℕ) : 0 ≤ squareIterCoeff K j k := by
  induction k with
  | zero => simp [squareIterCoeff]
  | succ k ih => simp only [squareIterCoeff]; exact mul_nonneg ih (by positivity)

theorem squareIterCoeff_le {K : ℝ} (hK : 0 ≤ K) (j k : ℕ) :
    squareIterCoeff K j k ≤ (K / 3 ^ j) ^ k := by
  induction k with
  | zero => simp [squareIterCoeff]
  | succ k ih =>
    simp only [squareIterCoeff]
    rw [pow_succ]
    refine mul_le_mul ih ?_ (by positivity) (by positivity)
    exact div_le_div_of_nonneg_left hK (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))

/-- **The iteration of Step 4 of the proof of Lemma 7.1.** If
`Γ_i ≤ D_i + K 3^{-i} Γ_{i + 3}` for `i ≥ j` with `P (i + 3)`, `P` downward closed, then
`Γ_j ≤ ∑_{k < n} c_k D_{j + 3 k} + c_n Γ_{j + 3 n}` whenever `P (j + 3 n)`. -/
theorem le_sum_squareIterCoeff {Γ D : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) {P : ℕ → Prop} (j : ℕ)
    (hP : ∀ i i', i ≤ i' → P i' → P i)
    (hstep : ∀ i, j ≤ i → P (i + 3) → Γ i ≤ D i + K / 3 ^ i * Γ (i + 3)) :
    ∀ n, P (j + 3 * n) → Γ j ≤ ∑ k ∈ range n, squareIterCoeff K j k * D (j + 3 * k) +
      squareIterCoeff K j n * Γ (j + 3 * n) := by
  intro n
  induction n with
  | zero => intro _; simp [squareIterCoeff]
  | succ n ih =>
    intro hPn
    have h1 := ih (hP _ _ (by omega) hPn)
    have e : j + 3 * n + 3 = j + 3 * (n + 1) := by ring
    have h2 := hstep (j + 3 * n) (by omega) (by rw [e]; exact hPn)
    rw [e] at h2
    have hc := squareIterCoeff_nonneg hK j n
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    rw [sum_range_succ]
    simp only [squareIterCoeff]
    nlinarith [h1, h3]

theorem sum_pow_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ range n, q ^ k ≤ 2 := by
  have h1 : q - 1 < 0 := by linarith
  rw [geom_sum_eq (by linarith : q ≠ 1) n, div_le_iff_of_neg h1]
  have := pow_nonneg hq0 n
  linarith

/-- The quotients `ballExcess s u / s` over `s ∈ [a, R]`, `a > 0`, are bounded. -/
theorem bddAbove_ballExcess_div {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (P : AddSubgroup (C → ℝ)) (u : C → ℝ) {a R : ℝ} (ha : 0 < a) :
    BddAbove (Set.range fun s : Set.Icc a R =>
      ballExcess (componentBallSeminorm C 0) P s u / s) := by
  set M := ∑ x ∈ componentEuclideanBall C 0 R, |u x|
  have hM : 0 ≤ M := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨M / a, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hs : a ≤ (s : ℝ) := s.2.1
  have hsR : (s : ℝ) ≤ R := s.2.2
  have h1 : ballExcess (componentBallSeminorm C 0) P s u ≤ M := by
    refine (ballExcess_le_self _ _ _ _).trans ?_
    rw [componentBallSeminorm_apply]
    exact componentBallL2_le_of_abs_le _ _ _ hM fun x hx =>
      single_le_sum (f := fun x => |u x|) (fun _ _ => abs_nonneg _)
        (componentEuclideanBall_mono _ _ hsR hx)
  calc ballExcess (componentBallSeminorm C 0) P s u / s ≤ M / s :=
        div_le_div_of_nonneg_right h1 (ha.le.trans hs)
    _ ≤ M / a := div_le_div_of_nonneg_left hM ha hs

/-- The oscillation of `f` on `□_i` against the slopes `ballExcess s / s ≤ S` over the radii
`s ∈ [A r, R]`, for `2 r ≤ 3^i ≤ R`. -/
theorem squareOsc_le_of_slope {f : Vertex 2 → ℝ} {A r R S : ℝ} {i : ℕ} (hA : 0 < A) (hr : 0 < r)
    (h2r : 2 * r ≤ 3 ^ i) (hAr : A * r ≤ R) (h3iR : (3 : ℝ) ^ i ≤ R) (hS0 : 0 ≤ S)
    (hS : ∀ s : ℝ, A * r ≤ s → s ≤ R →
      ballExcess (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) ≤
          s * S) :
    squareOsc i f ≤ (A + 5) ^ 2 * 3 ^ i * S := by
  have h3i : (0 : ℝ) < 3 ^ i := by positivity
  have h3i1 : (1 : ℝ) ≤ 3 ^ i := one_le_pow₀ (by norm_num)
  have hs3 : (3 : ℝ) ^ i ≤ max (A * r) (3 ^ i) := le_max_right _ _
  have h1 := squareOsc_le_ballExcess hs3 f
  have h2 := hS (max (A * r) (3 ^ i)) (le_max_left _ _) (max_le hAr h3iR)
  have hAr' : A * r ≤ A / 2 * 3 ^ i := by
    have := mul_le_mul_of_nonneg_left h2r hA.le
    linarith
  have hA3 : 0 ≤ A * 3 ^ i := by positivity
  have hsle : max (A * r) (3 ^ i) ≤ (A / 2 + 1) * 3 ^ i := max_le (by linarith) (by linarith)
  have h2s : 2 * max (A * r) (3 ^ i) + 3 ≤ (A + 5) * 3 ^ i := by linarith
  have hspos : 0 < max (A * r) ((3 : ℝ) ^ i) := lt_of_lt_of_le h3i hs3
  have hA5 : (A + 5) * (A / 2 + 1) ≤ (A + 5) ^ 2 := by nlinarith
  calc squareOsc i f
      ≤ (2 * max (A * r) (3 ^ i) + 3) / 3 ^ i *
          ballExcess (componentBallSeminorm (latticeComponent 2) 0)
            (clusterConstants (latticeComponent 2)) (max (A * r) (3 ^ i))
            (fun x : latticeComponent 2 => f x.val) := h1
    _ ≤ (2 * max (A * r) (3 ^ i) + 3) / 3 ^ i * (max (A * r) (3 ^ i) * S) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (A + 5) * 3 ^ i / 3 ^ i * ((A / 2 + 1) * 3 ^ i * S) := by gcongr
    _ = ((A + 5) * (A / 2 + 1)) * (3 ^ i * S) := by
        rw [mul_div_assoc, div_self h3i.ne', mul_one]; ring
    _ ≤ (A + 5) ^ 2 * (3 ^ i * S) := mul_le_mul_of_nonneg_right hA5 (by positivity)
    _ = (A + 5) ^ 2 * 3 ^ i * S := by ring

/-- The sum of the iteration over the squares `□_{m + 3 + 3 k}`, `k < n`. -/
theorem sum_squareIterCoeff_le {f : Vertex 2 → ℝ} {A K S : ℝ} {m n : ℕ} (hK : 0 ≤ K)
    (hS0 : 0 ≤ S) (hKm : 2 * K ≤ 3 ^ m)
    (hD : ∀ k < n, squareOsc (m + 3 + 3 * k) f ≤ (A + 5) ^ 2 * 3 ^ (m + 3 + 3 * k) * S) :
    ∑ k ∈ range n, squareIterCoeff K (m + 3) k * squareOsc (m + 3 + 3 * k) f ≤
      2 * (A + 5) ^ 2 * 3 ^ (m + 3) * S := by
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hq0 : 0 ≤ K / 3 ^ m := by positivity
  have hq : K / 3 ^ m ≤ 1 / 2 := by rw [div_le_iff₀ h3m]; linarith
  have h27 : ∀ k : ℕ, (3 : ℝ) ^ (3 * k) = 27 ^ k := fun k => by rw [pow_mul]; norm_num
  calc ∑ k ∈ range n, squareIterCoeff K (m + 3) k * squareOsc (m + 3 + 3 * k) f
      ≤ ∑ k ∈ range n, (K / 3 ^ (m + 3)) ^ k * ((A + 5) ^ 2 * 3 ^ (m + 3 + 3 * k) * S) :=
        sum_le_sum fun k hk => mul_le_mul (squareIterCoeff_le hK _ _)
          (hD k (mem_range.1 hk)) (squareOsc_nonneg _ _) (by positivity)
    _ = (A + 5) ^ 2 * 3 ^ (m + 3) * S * ∑ k ∈ range n, (K / 3 ^ m) ^ k := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        have e1 : (3 : ℝ) ^ (m + 3 + 3 * k) = 3 ^ (m + 3) * 27 ^ k := by rw [pow_add, h27]
        have e2 : (K / 3 ^ (m + 3)) ^ k = (K / 3 ^ m) ^ k / 27 ^ k := by
          rw [← div_pow]; congr 1; rw [pow_add]; ring
        have h27k : (27 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
        rw [e1, e2, show (K / 3 ^ m) ^ k / 27 ^ k * ((A + 5) ^ 2 * (3 ^ (m + 3) * 27 ^ k) * S) =
          (A + 5) ^ 2 * 3 ^ (m + 3) * S * (K / 3 ^ m) ^ k * (27 ^ k / 27 ^ k) by ring,
          div_self h27k, mul_one]
    _ ≤ (A + 5) ^ 2 * 3 ^ (m + 3) * S * 2 :=
        mul_le_mul_of_nonneg_left (sum_pow_le_two hq0 hq n) (by positivity)
    _ = 2 * (A + 5) ^ 2 * 3 ^ (m + 3) * S := by ring

/-- The last term of the iteration, on `□_{m + 3 + 3 n}`, for `n ≥ 1` maximal with
`L 3^{m + 3 + 3 n} ≤ R`. -/
theorem squareIterCoeff_mul_top_le {K L R B Γt : ℝ} {m n : ℕ} (hK : 0 ≤ K) (hL : 0 < L)
    (hB : 0 ≤ B) (hR0 : 0 < R) (hn1 : 1 ≤ n) (hKm : 2 * K ≤ 3 ^ m)
    (hnspec : R < L * 3 ^ (m + 3 + 3 * (n + 1)))
    (hG : Γt ≤ R / 3 ^ (m + 3 + 3 * n) * B) :
    squareIterCoeff K (m + 3) n * Γt ≤ 19683 * K * L ^ 2 * (B / R) := by
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have h27 : ∀ k : ℕ, (3 : ℝ) ^ (3 * k) = 27 ^ k := fun k => by rw [pow_mul]; norm_num
  have hc := squareIterCoeff_le hK (m + 3) n
  have hc0 := squareIterCoeff_nonneg hK (m + 3) n
  set q := K / 3 ^ m with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq : q ≤ 1 / 2 := by rw [hqdef, div_le_iff₀ h3m]; linarith
  set T : ℝ := 3 ^ m * 27 ^ (n + 1) with hTdef
  have hTpos : 0 < T := by positivity
  have hT : (3 : ℝ) ^ (m + 3 + 3 * n) = T := by
    rw [hTdef, show m + 3 + 3 * n = m + 3 * (n + 1) by ring, pow_add, h27]
  have hT' : (3 : ℝ) ^ (m + 3 + 3 * (n + 1)) = 27 * T := by
    rw [hTdef, show m + 3 + 3 * (n + 1) = m + 3 * (n + 2) by ring, pow_add, h27]; ring
  have hRlt : R < 27 * L * T := by rw [hT'] at hnspec; linarith
  have hc' : (K / 3 ^ (m + 3)) ^ n = q ^ n / 27 ^ n := by
    rw [hqdef, ← div_pow]; congr 1; rw [pow_add]; ring
  have hqn : q ^ n ≤ q := pow_le_of_le_one hq0 (by linarith) (by omega)
  have hq3 : q ^ n * 3 ^ m ≤ K := by
    calc q ^ n * 3 ^ m ≤ q * 3 ^ m := mul_le_mul_of_nonneg_right hqn h3m.le
      _ = K := by rw [hqdef, div_mul_cancel₀ K h3m.ne']
  have hRB : 0 ≤ R / T * B := by positivity
  have hstep : squareIterCoeff K (m + 3) n * Γt ≤ q ^ n / 27 ^ n * (R / T * B) := by
    calc squareIterCoeff K (m + 3) n * Γt
        ≤ squareIterCoeff K (m + 3) n * (R / 3 ^ (m + 3 + 3 * n) * B) :=
          mul_le_mul_of_nonneg_left hG hc0
      _ = squareIterCoeff K (m + 3) n * (R / T * B) := by rw [hT]
      _ ≤ (K / 3 ^ (m + 3)) ^ n * (R / T * B) := mul_le_mul_of_nonneg_right hc hRB
      _ = q ^ n / 27 ^ n * (R / T * B) := by rw [hc']
  have hRR : R * R ≤ (27 * L * T) * (27 * L * T) := mul_self_le_mul_self hR0.le hRlt.le
  have hqn0 : 0 ≤ q ^ n := pow_nonneg hq0 n
  have h27n : (0 : ℝ) < 27 ^ n := by positivity
  have key : q ^ n / 27 ^ n * (R / T * B) * R ≤ 19683 * K * L ^ 2 * B := by
    calc q ^ n / 27 ^ n * (R / T * B) * R = q ^ n * (R * R) * B / (27 ^ n * T) := by ring
      _ ≤ q ^ n * ((27 * L * T) * (27 * L * T)) * B / (27 ^ n * T) := by gcongr
      _ = 19683 * (q ^ n * 3 ^ m) * L ^ 2 * B * ((27 ^ n / 27 ^ n) * (T / T)) := by
          rw [hTdef]; ring
      _ = 19683 * (q ^ n * 3 ^ m) * L ^ 2 * B := by
          rw [div_self h27n.ne', div_self hTpos.ne', mul_one, mul_one]
      _ ≤ 19683 * K * L ^ 2 * B := by gcongr
  refine hstep.trans ?_
  rw [mul_div_assoc', le_div_iff₀ hR0]
  linarith [key]

/-- The scale above which `harmonicApproximation_of_squares` holds. -/
noncomputable def squareScale (A L C₁ K α : ℝ) : ℝ :=
  max K (max 1 ((9 * C₁ * max (324 * (A + 5) ^ 2) (19683 * K * L ^ 2)) ^ (2 / α)))

/-- The final bound of `harmonicApproximation_of_squares`: for `r ≥ 1` above
`(9 C₁ max(M₁, M₂))^{2/α}`, `9 C₁ r^{-α} (M₁ r S + M₂ E r) ≤ r^{1 - α/2} (S + E)`. -/
theorem nine_mul_le_rpow {C₁ α r S E M₁ M₂ : ℝ} (hα : 0 < α) (hC₁ : 0 ≤ C₁) (hr : 1 ≤ r)
    (hS : 0 ≤ S) (hE : 0 ≤ E) (hM₁ : 0 ≤ M₁)
    (hX : (9 * C₁ * max M₁ M₂) ^ (2 / α) ≤ r) :
    9 * (C₁ / r ^ α * (M₁ * r * S + M₂ * (E * r))) ≤ r ^ (1 - α / 2) * (S + E) := by
  have hr0 : 0 < r := by linarith
  set Cs := 9 * C₁ * max M₁ M₂ with hCsdef
  have hCs0 : 0 ≤ Cs := by positivity
  have hCsr : Cs ≤ r ^ (α / 2) := by
    have h1 : (Cs ^ (2 / α)) ^ (α / 2) = Cs := by
      rw [← Real.rpow_mul hCs0, show 2 / α * (α / 2) = (1 : ℝ) by field_simp, Real.rpow_one]
    calc Cs = (Cs ^ (2 / α)) ^ (α / 2) := h1.symm
      _ ≤ r ^ (α / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hCs0 _) hX (by positivity)
  have hpow : r ^ (1 - α / 2) = r ^ (α / 2) * (r / r ^ α) := by
    rw [show (1 - α / 2) = α / 2 + (1 - α) by ring, Real.rpow_add hr0, Real.rpow_sub hr0,
      Real.rpow_one]
  have hrr : 0 ≤ r / r ^ α := by positivity
  have hmax : M₁ * S + M₂ * E ≤ max M₁ M₂ * (S + E) := by
    have h1 := mul_le_mul_of_nonneg_right (le_max_left M₁ M₂) hS
    have h2 := mul_le_mul_of_nonneg_right (le_max_right M₁ M₂) hE
    linarith
  calc 9 * (C₁ / r ^ α * (M₁ * r * S + M₂ * (E * r)))
      = 9 * C₁ * (r / r ^ α) * (M₁ * S + M₂ * E) := by ring
    _ ≤ 9 * C₁ * (r / r ^ α) * (max M₁ M₂ * (S + E)) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = Cs * (r / r ^ α) * (S + E) := by rw [hCsdef]; ring
    _ ≤ r ^ (α / 2) * (r / r ^ α) * (S + E) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsr hrr) (by positivity)
    _ = r ^ (1 - α / 2) * (S + E) := by rw [hpow]

/-- **From squares to balls** (Armstrong–Dario, proof of Lemma 7.1, Step 4, and the start of the
proof of Lemma 7.3, in dimension two). Let `f` be a function on `ℤ²` and `Γ_j ≥ 0` real numbers
such that, for `3^j ≥ X₀` and `L 3^{j + 3} ≤ R`,
`inf_{w ∈ Ā(□_j)} ‖f - w‖_{L̲²(□_j)} ≤ C₁ 3^{-j α} Γ_{j + 3}` and
`Γ_j ≤ inf_a ‖f - a‖_{L̲²(□_j)} + K 3^{-j} Γ_{j + 3}`, and `Γ_j ≤ (R / 3^j) B` for `3^j ≥ X₀`
and `L 3^j ≤ R`. Then, for `A ≥ 4374 L` and `X` above `X₀` and `squareScale`, `f` satisfies the
harmonic approximation hypothesis of Lemma 7.2 on the balls of `ℤ²`, with the lattice harmonic
functions, the exponent `α / 2` and `E = B / R`. -/
theorem harmonicApproximation_of_squares {A L C₁ K α X₀ X R B : ℝ} {f : Vertex 2 → ℝ}
    {Γ : ℕ → ℝ} (hΓ0 : ∀ j, 0 ≤ Γ j) (hL : 1 ≤ L) (hA : 4374 * L ≤ A) (hC₁ : 0 ≤ C₁)
    (hK : 0 ≤ K) (hα : 0 < α) (hX₀ : X₀ ≤ X) (hX : squareScale A L C₁ K α ≤ X) (hB : 0 ≤ B)
    (H1 : ∀ m : ℕ, X₀ ≤ 3 ^ m → L * 3 ^ (m + 3) ≤ R →
      squareHarmonicDist m f ≤ C₁ / ((3 : ℝ) ^ m) ^ α * Γ (m + 3))
    (H2 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ (j + 3) ≤ R →
      Γ j ≤ squareOsc j f + K / 3 ^ j * Γ (j + 3))
    (H3 : ∀ j : ℕ, X₀ ≤ 3 ^ j → L * 3 ^ j ≤ R → Γ j ≤ R / 3 ^ j * B) :
    HarmonicApproximation (componentBallSeminorm (latticeComponent 2) 0)
      (latticeHarmonicClass 0) (clusterConstants (latticeComponent 2)) A (α / 2) X R (B / R)
      (fun x : latticeComponent 2 => f x.val) := by
  classical
  intro r hXr hrA
  have hXK : K ≤ X := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXC : (9 * C₁ * max (324 * (A + 5) ^ 2) (19683 * K * L ^ 2)) ^ (2 / α) ≤ X :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hr1 : 1 ≤ r := hX1.trans hXr
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < A := by linarith
  have hRA : A * r ≤ R := by
    rw [le_div_iff₀ hA0] at hrA; linarith
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos hA0 hr0) hRA
  have h27 : ∀ k : ℕ, (3 : ℝ) ^ (3 * k) = 27 ^ k := fun k => by rw [pow_mul]; norm_num
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near hr1
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  -- the ball `B_r` lies in `□_m` and contains `□_{m - 2}`
  have hsub : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < r →
        y ∈ triadicCubeFinset 2 m 0 := fun y hy => mem_square_of_dist_lt (by linarith)
  have hm9 : (3 : ℝ) ^ m ≤ 9 * 3 ^ (m - 2) := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m - 2 = 0 := by omega
      rw [this, pow_zero, mul_one]
      calc (3 : ℝ) ^ m ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ 9 := by norm_num
    · have : (3 : ℝ) ^ m = 3 ^ 2 * 3 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; norm_num
  have hj : (3 : ℝ) ^ (m - 2) ≤ r := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m - 2 = 0 := by omega
      rw [this, pow_zero]; exact hr1
    · have : (3 : ℝ) ^ m = 3 ^ 2 * 3 ^ (m - 2) := by rw [← pow_add]; congr 1; omega
      rw [this] at hm2; norm_num at hm2; linarith
  have hratio : (3 : ℝ) ^ m / 3 ^ (m - 2) ≤ 9 := by
    rw [div_le_iff₀ (by positivity)]; exact hm9
  have hdist0 := ballDist_le_squareHarmonicDist hsub hj f
  have hX₀m : X₀ ≤ 3 ^ m := by linarith
  have hKm : 2 * K ≤ 3 ^ m := by linarith
  -- the domain contains `□_{m + 6}`
  have hdom6 : L * 3 ^ (m + 6) ≤ R := by
    have e : (3 : ℝ) ^ (m + 6) = 729 * 3 ^ m := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hm2.le (by positivity : (0 : ℝ) ≤ 729 * L)
    have h2 := mul_le_mul_of_nonneg_right hA hr0.le
    linarith
  -- the number of steps of the iteration
  have hexn : ∃ n : ℕ, R < L * 3 ^ (m + 3 + 3 * (n + 1)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / L / 3 ^ (m + 3)) (by norm_num : (1 : ℝ) < 27)
    refine ⟨n, ?_⟩
    have e : (3 : ℝ) ^ (m + 3 + 3 * (n + 1)) = 3 ^ (m + 3) * 27 ^ (n + 1) := by
      rw [pow_add, h27]
    rw [e]
    have h27n : (27 : ℝ) ^ n ≤ 27 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_div, div_lt_iff₀ (by positivity)] at hn
    have := mul_le_mul_of_nonneg_right h27n (by positivity : (0 : ℝ) ≤ L * 3 ^ (m + 3))
    linarith
  obtain ⟨n, hnspec, hnmin⟩ : ∃ n : ℕ, R < L * 3 ^ (m + 3 + 3 * (n + 1)) ∧
      ∀ k < n, ¬ R < L * 3 ^ (m + 3 + 3 * (k + 1)) :=
    ⟨Nat.find hexn, Nat.find_spec hexn, fun k hk => Nat.find_min hexn hk⟩
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    have h0 : n = 0 := by omega
    rw [h0, show m + 3 + 3 * (0 + 1) = m + 6 by ring] at hnspec
    linarith
  have hndom : L * 3 ^ (m + 3 + 3 * n) ≤ R := by
    have h := hnmin (n - 1) (by omega)
    push Not at h
    rwa [show n - 1 + 1 = n by omega] at h
  -- the iteration of Step 4 from `m + 3`
  have hPmono : ∀ i i', i ≤ i' → L * 3 ^ i' ≤ R → L * 3 ^ i ≤ R := fun i i' h hP' =>
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) hL0.le) hP'
  have hiter := le_sum_squareIterCoeff (Γ := Γ) (D := fun i => squareOsc i f) hK
    (P := fun i => L * 3 ^ i ≤ R) (m + 3) hPmono (fun i hi hPi => H2 i (hX₀m.trans
      (pow_le_pow_right₀ (by norm_num) (by omega))) hPi) n hndom
  -- the supremum of the slopes
  have hS := bddAbove_ballExcess_div (latticeComponent 2) (clusterConstants (latticeComponent 2))
    (fun x : latticeComponent 2 => f x.val) (a := A * r) (R := R) (mul_pos hA0 hr0)
  obtain ⟨S, hSdef⟩ : ∃ S, S = ⨆ s : Set.Icc (A * r) R,
      ballExcess (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) / s :=
    ⟨_, rfl⟩
  have hSs : ∀ s : ℝ, A * r ≤ s → s ≤ R →
      ballExcess (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) ≤
          s * S := by
    intro s hsA hsR
    have hspos : 0 < s := lt_of_lt_of_le (mul_pos hA0 hr0) hsA
    have h := le_ciSup hS ⟨s, hsA, hsR⟩
    rw [← hSdef] at h
    have h' : ballExcess (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) / s ≤
          S := h
    rw [div_le_iff₀ hspos] at h'
    linarith
  have hS0 : 0 ≤ S := by
    have h := le_ciSup hS ⟨A * r, le_rfl, hRA⟩
    rw [← hSdef] at h
    exact (div_nonneg (ballExcess_nonneg _ _ _ _) (mul_pos hA0 hr0).le).trans h
  have hD : ∀ k < n, squareOsc (m + 3 + 3 * k) f ≤ (A + 5) ^ 2 * 3 ^ (m + 3 + 3 * k) * S := by
    intro k hk
    have hiR := hPmono (m + 3 + 3 * k) _ (by omega) hndom
    have h3i : (3 : ℝ) ^ m ≤ 3 ^ (m + 3 + 3 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3iR : (3 : ℝ) ^ (m + 3 + 3 * k) ≤ R := by
      have := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ 3 ^ (m + 3 + 3 * k))
      linarith
    exact squareOsc_le_of_slope hA0 hr0 (hm1.trans h3i) hRA h3iR hS0 hSs
  have hT1 := sum_squareIterCoeff_le hK hS0 hKm hD
  have hG := H3 (m + 3 + 3 * n) (hX₀m.trans (pow_le_pow_right₀ (by norm_num) (by omega))) hndom
  have hT2 := squareIterCoeff_mul_top_le hK hL0 hB hR0 hn1 hKm hnspec hG
  -- assembling
  have hH1 := H1 m hX₀m (hPmono _ _ (by omega) hndom)
  have hΓ : Γ (m + 3) ≤ 2 * (A + 5) ^ 2 * 3 ^ (m + 3) * S + 19683 * K * L ^ 2 * (B / R) := by
    have h := hiter
    linarith
  have h3m3 : (3 : ℝ) ^ (m + 3) ≤ 162 * r := by
    have e : (3 : ℝ) ^ (m + 3) = 27 * 3 ^ m := by ring
    rw [e]; linarith
  have hrα : r ^ α ≤ ((3 : ℝ) ^ m) ^ α := Real.rpow_le_rpow hr0.le (by linarith) hα.le
  have hrαpos : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hE0 : 0 ≤ B / R / r := by positivity
  have hcoef : C₁ / ((3 : ℝ) ^ m) ^ α ≤ C₁ / r ^ α := div_le_div_of_nonneg_left hC₁ hrαpos hrα
  have hBR : B / R = B / R / r * r := by
    rw [div_mul_cancel₀ _ hr0.ne']
  have hΓ' : Γ (m + 3) ≤ 324 * (A + 5) ^ 2 * r * S + 19683 * K * L ^ 2 * (B / R / r * r) := by
    have : 2 * (A + 5) ^ 2 * 3 ^ (m + 3) * S ≤ 2 * (A + 5) ^ 2 * (162 * r) * S := by gcongr
    rw [← hBR]
    linarith
  have hfin := nine_mul_le_rpow (M₁ := 324 * (A + 5) ^ 2) (M₂ := 19683 * K * L ^ 2) hα hC₁ hr1
    hS0 hE0 (by positivity) (hXC.trans hXr)
  rw [hSdef] at hfin
  calc ballDist (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicClass 0 r) r
        (fun x : latticeComponent 2 => f x.val)
      ≤ (3 : ℝ) ^ m / 3 ^ (m - 2) * squareHarmonicDist m f := hdist0
    _ ≤ 9 * (C₁ / ((3 : ℝ) ^ m) ^ α * Γ (m + 3)) :=
        mul_le_mul hratio hH1 (squareHarmonicDist_nonneg _ _) (by norm_num)
    _ ≤ 9 * (C₁ / r ^ α * (324 * (A + 5) ^ 2 * r * S +
          19683 * K * L ^ 2 * (B / R / r * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcoef hΓ' (hΓ0 _) (by positivity)) (by norm_num)
    _ = 9 * (C₁ / r ^ α * (324 * (A + 5) ^ 2 * r * (⨆ s : Set.Icc (A * r) R,
          ballExcess (componentBallSeminorm (latticeComponent 2) 0)
            (clusterConstants (latticeComponent 2)) s (fun x : latticeComponent 2 => f x.val) / s) +
          19683 * K * L ^ 2 * (B / R / r * r))) := by rw [hSdef]
    _ ≤ _ := hfin

end Rigidity.Proofs.Regularity
