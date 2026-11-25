import Rigidity.Proofs.Barlow.HeatDecay

/-!
# Exit times of the lazy walk

The heat kernel `openHeat` is the Poisson average of the powers `Qⁿ` of the lazy kernel
`Q(x, z) = 1/4` (`z ∼ x`), `Q(x, x) = 1 - deg(x)/4`. This file sets up, for the walk `X` with
kernel `Q` and a set `A`, the exit probabilities `P^w(σ_A ≤ n)` (`exitProb`) and the truncated
generating functions `E^w[s^{σ_A}; σ_A ≤ n]` (`exitGen`) by their first-step recursions, where
`σ_A` is the first time at which `X` is outside `A`. The strong Markov property at an exit time,
used by Barlow (*Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004),
proofs of Lemma 3.5 and Proposition 3.7), enters through:

* `exitGen_eq_abel`: `E[s^σ; σ ≤ n] = sⁿ P(σ ≤ n) + (1 - s) Σ_{k < n} s^k P(σ ≤ k)`;
* `exitGen_le_mul_of_subset`: for `B ⊆ A`, `E^w[s^{σ_A}] ≤ K · E^w[s^{σ_B}]` if `E^z[s^{σ_A}] ≤ K`
  at the points `z` where the walk leaves `B`;
* `mul_exitProb_le`: optional stopping for a space-time supersolution `h`, by backward induction:
  `c · P^w(σ_A ≤ n) ≤ h(0, w)` if `h ≥ c` where the walk leaves `A`;
* `tsum_notMem_lazyPow_le_exitProb`: `P^w(X_n ∉ A) ≤ P^w(σ_A ≤ n)`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Barlow

variable {ω : Configuration 2}

/-! ### One step of the lazy walk -/

/-- One step of the lazy walk: `(Qu)(x) = (1 - deg(x)/4) u(x) + ¼ Σ_{z ∼ x} u(z)`. -/
noncomputable def lazyStep (ω : Configuration 2) (u : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  (1 - ((openGraph ω).degree x : ℝ) / 4) * u x +
    (1 / 4) * ∑ z ∈ (openGraph ω).neighborFinset x, u z

theorem lazyPow_succ_eq_lazyStep (n : ℕ) (x y : Vertex 2) :
    lazyPow (openGraph ω) 4 (n + 1) x y = lazyStep ω (fun z => lazyPow (openGraph ω) 4 n z y) x := by
  rw [lazyPow_succ, lazyStep]
  norm_num

theorem one_sub_degree_div_nonneg (x : Vertex 2) :
    0 ≤ 1 - ((openGraph ω).degree x : ℝ) / 4 := by
  have : ((openGraph ω).degree x : ℝ) ≤ 4 := by exact_mod_cast openGraph_degree_le_four ω x
  linarith

theorem lazyStep_mono {u v : Vertex 2 → ℝ} {x : Vertex 2}
    (h : ∀ z, (z = x ∨ z ∈ (openGraph ω).neighborFinset x) → u z ≤ v z) :
    lazyStep ω u x ≤ lazyStep ω v x := by
  unfold lazyStep
  have h1 := mul_le_mul_of_nonneg_left (h x (Or.inl rfl)) (one_sub_degree_div_nonneg (ω := ω) x)
  have h2 : ∑ z ∈ (openGraph ω).neighborFinset x, u z ≤ ∑ z ∈ (openGraph ω).neighborFinset x, v z :=
    Finset.sum_le_sum fun z hz => h z (Or.inr hz)
  linarith

theorem lazyStep_const (c : ℝ) (x : Vertex 2) : lazyStep ω (fun _ => c) x = c := by
  unfold lazyStep
  rw [Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul]
  ring

theorem lazyStep_const_mul (c : ℝ) (u : Vertex 2 → ℝ) (x : Vertex 2) :
    lazyStep ω (fun z => c * u z) x = c * lazyStep ω u x := by
  unfold lazyStep
  rw [← Finset.mul_sum]
  ring

theorem lazyStep_add (u v : Vertex 2 → ℝ) (x : Vertex 2) :
    lazyStep ω (fun z => u z + v z) x = lazyStep ω u x + lazyStep ω v x := by
  unfold lazyStep
  rw [Finset.sum_add_distrib]
  ring

theorem lazyStep_sum (S : Finset ℕ) (f : ℕ → Vertex 2 → ℝ) (x : Vertex 2) :
    lazyStep ω (fun z => ∑ k ∈ S, f k z) x = ∑ k ∈ S, lazyStep ω (f k) x := by
  unfold lazyStep
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

theorem lazyStep_nonneg {u : Vertex 2 → ℝ} {x : Vertex 2}
    (h : ∀ z, (z = x ∨ z ∈ (openGraph ω).neighborFinset x) → 0 ≤ u z) : 0 ≤ lazyStep ω u x := by
  have := lazyStep_mono (ω := ω) (u := fun _ => (0 : ℝ)) (v := u) h
  rwa [lazyStep_const] at this

theorem lazyStep_le_one {u : Vertex 2 → ℝ} {x : Vertex 2}
    (h : ∀ z, (z = x ∨ z ∈ (openGraph ω).neighborFinset x) → u z ≤ 1) : lazyStep ω u x ≤ 1 := by
  have := lazyStep_mono (ω := ω) (u := u) (v := fun _ => (1 : ℝ)) h
  rwa [lazyStep_const] at this

/-- `lazyStep` commutes with summable sums. -/
theorem tsum_lazyStep (F : Vertex 2 → Vertex 2 → ℝ) (hF : ∀ z, Summable (F z)) (x : Vertex 2) :
    ∑' y, lazyStep ω (fun z => F z y) x = lazyStep ω (fun z => ∑' y, F z y) x := by
  unfold lazyStep
  have hs : Summable fun y => ∑ z ∈ (openGraph ω).neighborFinset x, F z y :=
    summable_sum fun z _ => hF z
  rw [((hF x).mul_left _).tsum_add (hs.mul_left _), tsum_mul_left, tsum_mul_left,
    Summable.tsum_finsetSum fun z _ => hF z]

/-! ### Exit probabilities and generating functions -/

/-- `P^w(σ_A ≤ n)`, `σ_A` the first time the lazy walk is outside `A`. -/
noncomputable def exitProb (ω : Configuration 2) (A : Set (Vertex 2)) : ℕ → Vertex 2 → ℝ
  | 0 => fun w => if w ∈ A then 0 else 1
  | n + 1 => fun w => if w ∈ A then lazyStep ω (exitProb ω A n) w else 1

/-- `E^w[s^{σ_A}; σ_A ≤ n]`. -/
noncomputable def exitGen (ω : Configuration 2) (A : Set (Vertex 2)) (s : ℝ) :
    ℕ → Vertex 2 → ℝ
  | 0 => fun w => if w ∈ A then 0 else 1
  | n + 1 => fun w => if w ∈ A then s * lazyStep ω (exitGen ω A s n) w else 1

theorem exitProb_of_notMem {A : Set (Vertex 2)} {w : Vertex 2} (hw : w ∉ A) (n : ℕ) :
    exitProb ω A n w = 1 := by
  cases n <;> simp [exitProb, hw]

theorem exitProb_zero_of_mem {A : Set (Vertex 2)} {w : Vertex 2} (hw : w ∈ A) :
    exitProb ω A 0 w = 0 := by
  simp [exitProb, hw]

theorem exitProb_succ_of_mem {A : Set (Vertex 2)} {w : Vertex 2} (hw : w ∈ A) (n : ℕ) :
    exitProb ω A (n + 1) w = lazyStep ω (exitProb ω A n) w := by
  simp [exitProb, hw]

theorem exitGen_of_notMem {A : Set (Vertex 2)} {s : ℝ} {w : Vertex 2} (hw : w ∉ A) (n : ℕ) :
    exitGen ω A s n w = 1 := by
  cases n <;> simp [exitGen, hw]

theorem exitGen_zero_of_mem {A : Set (Vertex 2)} {s : ℝ} {w : Vertex 2} (hw : w ∈ A) :
    exitGen ω A s 0 w = 0 := by
  simp [exitGen, hw]

theorem exitGen_succ_of_mem {A : Set (Vertex 2)} {s : ℝ} {w : Vertex 2} (hw : w ∈ A) (n : ℕ) :
    exitGen ω A s (n + 1) w = s * lazyStep ω (exitGen ω A s n) w := by
  simp [exitGen, hw]

theorem exitProb_mem_Icc (A : Set (Vertex 2)) :
    ∀ n w, 0 ≤ exitProb ω A n w ∧ exitProb ω A n w ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitProb_zero_of_mem hw]; norm_num
    · rw [exitProb_of_notMem hw]; norm_num
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitProb_succ_of_mem hw]
      exact ⟨lazyStep_nonneg fun z _ => (ih z).1, lazyStep_le_one fun z _ => (ih z).2⟩
    · rw [exitProb_of_notMem hw]; norm_num

theorem exitGen_mem_Icc (A : Set (Vertex 2)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ n w, 0 ≤ exitGen ω A s n w ∧ exitGen ω A s n w ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_zero_of_mem hw]; norm_num
    · rw [exitGen_of_notMem hw]; norm_num
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_succ_of_mem hw]
      have h0 := lazyStep_nonneg (ω := ω) (u := exitGen ω A s n) (x := w) fun z _ => (ih z).1
      have h1 := lazyStep_le_one (ω := ω) (u := exitGen ω A s n) (x := w) fun z _ => (ih z).2
      exact ⟨mul_nonneg hs0 h0, by nlinarith⟩
    · rw [exitGen_of_notMem hw]; norm_num

theorem exitProb_mono_succ (A : Set (Vertex 2)) :
    ∀ n w, exitProb ω A n w ≤ exitProb ω A (n + 1) w := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitProb_zero_of_mem hw, exitProb_succ_of_mem hw]
      exact lazyStep_nonneg fun z _ => (exitProb_mem_Icc A 0 z).1
    · rw [exitProb_of_notMem hw, exitProb_of_notMem hw]
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitProb_succ_of_mem hw, exitProb_succ_of_mem hw]
      exact lazyStep_mono fun z _ => ih z
    · rw [exitProb_of_notMem hw, exitProb_of_notMem hw]

theorem exitProb_mono {A : Set (Vertex 2)} {m n : ℕ} (hmn : m ≤ n) (w : Vertex 2) :
    exitProb ω A m w ≤ exitProb ω A n w := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (exitProb_mono_succ A n w)

theorem exitGen_mono_succ (A : Set (Vertex 2)) {s : ℝ} (hs0 : 0 ≤ s) :
    ∀ n w, exitGen ω A s n w ≤ exitGen ω A s (n + 1) w := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_zero_of_mem hw, exitGen_succ_of_mem hw]
      refine mul_nonneg hs0 (lazyStep_nonneg fun z _ => ?_)
      by_cases hz : z ∈ A
      · rw [exitGen_zero_of_mem hz]
      · rw [exitGen_of_notMem hz]; norm_num
    · rw [exitGen_of_notMem hw, exitGen_of_notMem hw]
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_succ_of_mem hw, exitGen_succ_of_mem hw]
      exact mul_le_mul_of_nonneg_left (lazyStep_mono fun z _ => ih z) hs0
    · rw [exitGen_of_notMem hw, exitGen_of_notMem hw]

theorem exitGen_mono {A : Set (Vertex 2)} {s : ℝ} (hs0 : 0 ≤ s) {m n : ℕ} (hmn : m ≤ n)
    (w : Vertex 2) : exitGen ω A s m w ≤ exitGen ω A s n w := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (exitGen_mono_succ A hs0 n w)

/-- A smaller set is left earlier: `E[s^{σ_A}] ≤ E[s^{σ_{A'}}]` for `A' ⊆ A`. -/
theorem exitGen_anti {A A' : Set (Vertex 2)} (hA : A' ⊆ A) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ n w, exitGen ω A s n w ≤ exitGen ω A' s n w := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A'
    · rw [exitGen_zero_of_mem hw, exitGen_zero_of_mem (hA hw)]
    · rw [exitGen_of_notMem hw]
      exact (exitGen_mem_Icc A hs0 hs1 0 w).2
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A'
    · rw [exitGen_succ_of_mem hw, exitGen_succ_of_mem (hA hw)]
      exact mul_le_mul_of_nonneg_left (lazyStep_mono fun z _ => ih z) hs0
    · rw [exitGen_of_notMem hw]
      exact (exitGen_mem_Icc A hs0 hs1 _ w).2

/-- **The Abel identity**: `E[s^σ; σ ≤ n] = sⁿ P(σ ≤ n) + (1 - s) Σ_{k < n} s^k P(σ ≤ k)`. -/
theorem exitGen_eq_abel (A : Set (Vertex 2)) (s : ℝ) :
    ∀ n w, exitGen ω A s n w =
      s ^ n * exitProb ω A n w + (1 - s) * ∑ k ∈ Finset.range n, s ^ k * exitProb ω A k w := by
  intro n
  induction n with
  | zero =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_zero_of_mem hw, exitProb_zero_of_mem hw]; simp
    · rw [exitGen_of_notMem hw, exitProb_of_notMem hw]; simp
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitGen_succ_of_mem hw, exitProb_succ_of_mem hw, Finset.sum_range_succ',
        exitProb_zero_of_mem hw]
      have hfun : exitGen ω A s n = fun z => s ^ n * exitProb ω A n z +
          (1 - s) * ∑ k ∈ Finset.range n, s ^ k * exitProb ω A k z := funext ih
      rw [hfun, lazyStep_add, lazyStep_const_mul, lazyStep_const_mul, lazyStep_sum]
      have hk : ∀ k ∈ Finset.range n, lazyStep ω (fun z => s ^ k * exitProb ω A k z) w =
          s ^ k * exitProb ω A (k + 1) w := by
        intro k _
        rw [lazyStep_const_mul, exitProb_succ_of_mem hw]
      rw [Finset.sum_congr rfl hk]
      have hk2 : ∑ k ∈ Finset.range n, s ^ (k + 1) * exitProb ω A (k + 1) w =
          s * ∑ k ∈ Finset.range n, s ^ k * exitProb ω A (k + 1) w := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hk2]
      ring
    · rw [exitGen_of_notMem hw, exitProb_of_notMem hw]
      have hk : ∀ k ∈ Finset.range (n + 1), s ^ k * exitProb ω A k w = s ^ k := fun k _ => by
        rw [exitProb_of_notMem hw, mul_one]
      rw [Finset.sum_congr rfl hk]
      have hg := geom_sum_mul s (n + 1)
      linarith [hg]

/-- `sⁿ P(σ ≤ n) ≤ E[s^σ; σ ≤ n]` for `0 ≤ s ≤ 1`. -/
theorem pow_mul_exitProb_le_exitGen (A : Set (Vertex 2)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (n : ℕ) (w : Vertex 2) : s ^ n * exitProb ω A n w ≤ exitGen ω A s n w := by
  rw [exitGen_eq_abel A s n w]
  have : 0 ≤ (1 - s) * ∑ k ∈ Finset.range n, s ^ k * exitProb ω A k w :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (pow_nonneg hs0 k) (exitProb_mem_Icc A k w).1)
  linarith

/-- If `P^w(σ ≤ k) ≤ p + a k` for `k ≤ n`, then `E^w[s^σ; σ ≤ n] ≤ p + a s/(1 - s)`. -/
theorem exitGen_le_of_exitProb_le (A : Set (Vertex 2)) {s p a : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (ha : 0 ≤ a) {n : ℕ} {w : Vertex 2} (h : ∀ k ≤ n, exitProb ω A k w ≤ p + a * k) :
    exitGen ω A s n w ≤ p + a * (s / (1 - s)) := by
  rw [exitGen_eq_abel A s n w]
  have h1 : s ^ n * exitProb ω A n w ≤ s ^ n * (p + a * n) :=
    mul_le_mul_of_nonneg_left (h n le_rfl) (pow_nonneg hs0 n)
  have h2 : (1 - s) * ∑ k ∈ Finset.range n, s ^ k * exitProb ω A k w ≤
      (1 - s) * ∑ k ∈ Finset.range n, s ^ k * (p + a * k) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (h k (Finset.mem_range.1 hk).le) (pow_nonneg hs0 k)) (by linarith)
  -- the value for `P(σ ≤ k) = p + a k`
  have hval : ∀ m : ℕ, s ^ m * (p + a * m) + (1 - s) * ∑ k ∈ Finset.range m, s ^ k * (p + a * k) =
      p + a * ∑ k ∈ Finset.range m, s ^ (k + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have e : s ^ (m + 1) * (p + a * ((m + 1 : ℕ) : ℝ)) + (1 - s) *
          (∑ k ∈ Finset.range m, s ^ k * (p + a * k) + s ^ m * (p + a * m)) =
          (s ^ m * (p + a * m) + (1 - s) * ∑ k ∈ Finset.range m, s ^ k * (p + a * k)) +
            a * s ^ (m + 1) := by
        push_cast
        ring
      rw [e, ihm]
      ring
  have hgeom : ∑ k ∈ Finset.range n, s ^ (k + 1) ≤ s / (1 - s) := by
    have hpos : 0 < 1 - s := by linarith
    rw [le_div_iff₀ hpos]
    have hg := geom_sum_mul s n
    have e : ∑ k ∈ Finset.range n, s ^ (k + 1) = s * ∑ k ∈ Finset.range n, s ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    nlinarith [pow_nonneg hs0 n]
  have := hval n
  nlinarith [mul_le_mul_of_nonneg_left hgeom ha]

/-- **The strong Markov property at the exit time of `B ⊆ A`**: if `E^z[s^{σ_A}; σ_A ≤ m] ≤ K`
for `m ≤ N` at the points `z ∉ B` adjacent to `B`, then
`E^w[s^{σ_A}; σ_A ≤ m] ≤ K · E^w[s^{σ_B}; σ_B ≤ m]` on `B` and its outer boundary. -/
theorem exitGen_le_mul_of_subset {A B : Set (Vertex 2)} (hBA : B ⊆ A) {s K : ℝ} (hs0 : 0 ≤ s)
    {N : ℕ}
    (hbd : ∀ z ∉ B, (∃ v ∈ B, (openGraph ω).Adj v z) → ∀ m ≤ N, exitGen ω A s m z ≤ K) :
    ∀ m ≤ N, ∀ w, (w ∈ B ∨ ∃ v ∈ B, (openGraph ω).Adj v w) →
      exitGen ω A s m w ≤ K * exitGen ω B s m w := by
  intro m
  induction m with
  | zero =>
    intro _ w hw
    by_cases hwB : w ∈ B
    · rw [exitGen_zero_of_mem hwB, exitGen_zero_of_mem (hBA hwB), mul_zero]
    · rw [exitGen_of_notMem hwB, mul_one]
      exact hbd w hwB (hw.resolve_left hwB) 0 (Nat.zero_le _)
  | succ m ih =>
    intro hm w hw
    by_cases hwB : w ∈ B
    · rw [exitGen_succ_of_mem hwB, exitGen_succ_of_mem (hBA hwB)]
      have h := lazyStep_mono (ω := ω) (u := exitGen ω A s m)
        (v := fun z => K * exitGen ω B s m z) (x := w) fun z hz => by
          refine ih (by omega) z ?_
          rcases hz with rfl | hz
          · exact Or.inl hwB
          · by_cases hzB : z ∈ B
            · exact Or.inl hzB
            · exact Or.inr ⟨w, hwB, ((openGraph ω).mem_neighborFinset w z).1 hz⟩
      rw [lazyStep_const_mul] at h
      calc s * lazyStep ω (exitGen ω A s m) w ≤ s * (K * lazyStep ω (exitGen ω B s m) w) :=
            mul_le_mul_of_nonneg_left h hs0
        _ = K * (s * lazyStep ω (exitGen ω B s m) w) := by ring
    · rw [exitGen_of_notMem hwB, mul_one]
      exact hbd w hwB (hw.resolve_left hwB) (m + 1) hm

/-- **Optional stopping for a supersolution** (by backward induction): if `h(j, ·) ≥ Q h(j + 1, ·)`
on `A` for `j < n`, `h ≥ 0` on `A` and `h(j, z) ≥ c` at the points `z ∉ A` adjacent to `A`, then
`c · P^w(σ_A ≤ m) ≤ h(n - m, w)` for `m ≤ n` on `A` and its outer boundary. -/
theorem mul_exitProb_le {A : Set (Vertex 2)} {n : ℕ} {c : ℝ} {h : ℕ → Vertex 2 → ℝ}
    (hrec : ∀ j < n, ∀ w ∈ A, lazyStep ω (h (j + 1)) w ≤ h j w)
    (hnn : ∀ j ≤ n, ∀ w ∈ A, 0 ≤ h j w)
    (hout : ∀ j ≤ n, ∀ z ∉ A, (∃ v ∈ A, (openGraph ω).Adj v z) → c ≤ h j z) :
    ∀ m ≤ n, ∀ w, (w ∈ A ∨ ∃ v ∈ A, (openGraph ω).Adj v w) →
      c * exitProb ω A m w ≤ h (n - m) w := by
  intro m
  induction m with
  | zero =>
    intro _ w hw
    by_cases hwA : w ∈ A
    · rw [exitProb_zero_of_mem hwA, mul_zero]
      exact hnn n le_rfl w hwA
    · rw [exitProb_of_notMem hwA, mul_one, Nat.sub_zero]
      exact hout n le_rfl w hwA (hw.resolve_left hwA)
  | succ m ih =>
    intro hm w hw
    by_cases hwA : w ∈ A
    · rw [exitProb_succ_of_mem hwA, ← lazyStep_const_mul]
      have h1 := lazyStep_mono (ω := ω) (u := fun z => c * exitProb ω A m z) (v := h (n - m))
        (x := w) fun z hz => by
          refine ih (by omega) z ?_
          rcases hz with rfl | hz
          · exact Or.inl hwA
          · by_cases hzA : z ∈ A
            · exact Or.inl hzA
            · exact Or.inr ⟨w, hwA, ((openGraph ω).mem_neighborFinset w z).1 hz⟩
      have h2 := hrec (n - (m + 1)) (by omega) w hwA
      have e : n - (m + 1) + 1 = n - m := by omega
      rw [e] at h2
      exact h1.trans h2
    · rw [exitProb_of_notMem hwA, mul_one]
      exact hout _ (by omega) w hwA (hw.resolve_left hwA)

/-- `P^w(X_n ∉ A) ≤ P^w(σ_A ≤ n)`. -/
theorem tsum_notMem_lazyPow_le_exitProb (A : Set (Vertex 2)) :
    ∀ n w, ∑' y, (if y ∈ A then 0 else lazyPow (openGraph ω) 4 n w y) ≤ exitProb ω A n w := by
  have hdeg := openGraph_degree_le_four ω
  have hsum : ∀ n z, Summable fun y => (if y ∈ A then 0 else lazyPow (openGraph ω) 4 n z y) :=
    fun n z => (hasSum_lazyPow_of_degree_le (by norm_num) hdeg n z).summable.of_nonneg_of_le
      (fun y => by split_ifs; exacts [le_rfl, (lazyPow_mem_Icc (by norm_num) hdeg n z y).1])
      (fun y => by split_ifs; exacts [(lazyPow_mem_Icc (by norm_num) hdeg n z y).1, le_rfl])
  intro n
  induction n with
  | zero =>
    intro w
    have e : (fun y => if y ∈ A then (0 : ℝ) else lazyPow (openGraph ω) 4 0 w y) =
        fun y => if y = w then (if w ∈ A then 0 else 1) else 0 := by
      funext y
      rw [lazyPow_zero]
      by_cases hyw : y = w
      · subst hyw; simp
      · simp [hyw, Ne.symm hyw]
    rw [e, tsum_ite_eq]
    by_cases hw : w ∈ A
    · rw [if_pos hw, exitProb_zero_of_mem hw]
    · rw [if_neg hw, exitProb_of_notMem hw]
  | succ n ih =>
    intro w
    by_cases hw : w ∈ A
    · rw [exitProb_succ_of_mem hw]
      have e : (fun y => if y ∈ A then (0 : ℝ) else lazyPow (openGraph ω) 4 (n + 1) w y) =
          fun y => lazyStep ω (fun z => if y ∈ A then 0 else lazyPow (openGraph ω) 4 n z y) w := by
        funext y
        by_cases hy : y ∈ A
        · simp only [hy, if_true]
          rw [lazyStep_const]
        · rw [if_neg hy, lazyPow_succ_eq_lazyStep]
          simp only [hy, if_false]
      rw [e, tsum_lazyStep (fun z y => if y ∈ A then 0 else lazyPow (openGraph ω) 4 n z y)
        (fun z => hsum n z) w]
      exact lazyStep_mono fun z _ => ih z
    · rw [exitProb_of_notMem hw]
      calc ∑' y, (if y ∈ A then 0 else lazyPow (openGraph ω) 4 (n + 1) w y)
          ≤ ∑' y, lazyPow (openGraph ω) 4 (n + 1) w y :=
            Summable.tsum_le_tsum (fun y => by
              split_ifs
              · exact (lazyPow_mem_Icc (by norm_num) hdeg _ w y).1
              · exact le_rfl) (hsum (n + 1) w)
              (hasSum_lazyPow_of_degree_le (by norm_num) hdeg (n + 1) w).summable
        _ = 1 := (hasSum_lazyPow_of_degree_le (by norm_num) hdeg (n + 1) w).tsum_eq

end Rigidity.Barlow
