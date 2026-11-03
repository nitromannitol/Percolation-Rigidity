import Rigidity.Proofs.Section5.MengerRays
import Rigidity.Proofs.Section5.LoopFromCrossings

/-!
# The cut form of the Kesten channel construction (step `step:5.21-renorm-paths`)

`KestenChannelCutStep` (`Rigidity/Steps/Section5/DisjointPathsToInfinity.lean`): for
`R ≥ R₁(C_f)`, if the renormalized site `z` lies in an infinite open cluster of the renormalized
process of size `R` and `x ∈ (2R + 1) z + Q_R`, then for every finite connected `S ⊆ 𝒞_∞`
containing `x` of `ℓ¹` diameter at least `R` and every set `X` of at most `C_f` vertices of `𝒞_∞`,
some infinite path of `𝒞_∞` starts in `S` and avoids `X`. No literature input is used: the very
good cubes carry their Kesten channels by definition, and the planar input is the crossing lemma
`exists_mem_support_of_crossing` (a left-right and a top-bottom crossing of a lattice rectangle
share a vertex).

Write `r = ⌊11R/10⌋ = R + ⌊R/10⌋`, `w = ⌈√r⌉` and `N = ⌊(2r + 1)/w⌋` for the number of channels
of each direction of a very good cube `(2R + 1) z' + Q_r`. A channel is *unhit* if it avoids `X`.

* The channels of one direction lie in disjoint bands, so among `C_f + 1` of them one is unhit
  (`exists_unhit_channel`).
* Any horizontal and any vertical channel of one cube meet (`reachIn_of_channels`); so once one
  unhit channel of a very good cube is joined off `X` to a vertex `s₀`, all of them are
  (`reached_of_channel`).
* For neighbouring sites, the overlap of the two cubes has width `2⌊R/10⌋ ≥ (C_f + 2) w`, so it
  contains `C_f + 1` transverse channel bands of the first cube; an unhit transverse channel there
  meets the unhit channels of the second cube (`exists_linked_channels`).
* A path of `S` from `x` to its first exit from `x + Q_{⌊R/10⌋ - 1}` stays in
  `(2R + 1) z + Q_r` and crosses `C_f + 1` channel bands transversally; an unhit channel among
  them meets `S` at a vertex `s₀` (`exists_reached_of_crossing`).
* Along the renormalized cluster of `z` all unhit channels are joined off `X` to `s₀`; their
  starts are unbounded, so `s₀` has infinitely many vertices joined to it off `X`, and König's
  lemma (`Menger.exists_ray_of_infinite`) gives the infinite path.
-/

noncomputable section

open Classical Function Set LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

namespace Kesten

open Rigidity.Section5

variable {ω : Configuration 2}

/-- The width `⌈√r⌉` of the Kesten channels of `x + Q_r`. -/
def chanWidth (r : ℕ) : ℕ := Nat.ceil (Real.sqrt r)

theorem abs_add_abs_of_adj {u v : Vertex 2} (h : (openGraph ω).Adj u v) :
    |u 0 - v 0| + |u 1 - v 1| = 1 := by
  obtain ⟨hadj, -⟩ := h
  have h1 := lattice_adj_iff_l1Dist.1 hadj
  simpa [latticeL1Dist, Fin.sum_univ_two] using h1

theorem abs_sub_le_one_of_adj {u v : Vertex 2} (h : (openGraph ω).Adj u v) (i : Fin 2) :
    |u i - v i| ≤ 1 := by
  have h1 := abs_add_abs_of_adj h
  have h2 := abs_nonneg (u 0 - v 0)
  have h3 := abs_nonneg (u 1 - v 1)
  fin_cases i <;> simp <;> omega

theorem support_subset_of_openIn {B : Set (Vertex 2)} :
    ∀ {u v : Vertex 2} (p : (openIn ω B).Walk u v), u ∈ B → ∀ x ∈ p.support, x ∈ B
  | _, _, .nil, hu, x, hx => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ hu
  | _, _, .cons h p, hu, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact support_subset_of_openIn p h.2.2 x hx

theorem exists_walk_of_reachable_openIn {B : Set (Vertex 2)} {y z : Vertex 2}
    (h : (openIn ω B).Reachable y z) (hy : y ∈ B) :
    ∃ W : (openGraph ω).Walk y z, ∀ x ∈ W.support, x ∈ B := by
  obtain ⟨p⟩ := h
  have hle : openIn ω B ≤ openGraph ω := fun _ _ h => h.1
  refine ⟨p.mapLe hle, fun x hx => ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact support_subset_of_openIn p hy x hx

/-! ### Channels -/

/-- A Kesten channel of the cube `c + Q_r` across direction `i`, in the band `j` of width `w` in
the other coordinate `k`, starting at `y` and staying in `T`. -/
def IsChannel (ω : Configuration 2) (T : Set (Vertex 2)) (c : Vertex 2) (r w j : ℕ) (i k : Fin 2)
    (y : Vertex 2) : Prop :=
  ∃ z, ∃ W : (openGraph ω).Walk y z, (∀ v ∈ W.support, v ∈ band c r w j k ∧ v ∈ T) ∧
    y i = c i - r ∧ z i = c i + r

/-- A horizontal channel of `a + Q_r` and a vertical channel of `b + Q_r` meet when the band of
each lies within the extent of the other cube. -/
theorem reachIn_of_channels {T : Set (Vertex 2)} {a b : Vertex 2} {r w jH jV : ℕ}
    {yH yV : Vertex 2} (hH : IsChannel ω T a r w jH 0 1 yH) (hV : IsChannel ω T b r w jV 1 0 yV)
    (h1 : b 1 - r ≤ a 1 - r + jH * w) (h1' : a 1 - r + (jH + 1) * w - 1 ≤ b 1 + r)
    (h0 : a 0 - r ≤ b 0 - r + jV * w) (h0' : b 0 - r + (jV + 1) * w - 1 ≤ a 0 + r) :
    ReachIn ω T yH yV := by
  obtain ⟨zH, WH, hWH, hyH, hzH⟩ := hH
  obtain ⟨zV, WV, hWV, hyV, hzV⟩ := hV
  have hP : ∀ v ∈ WH.support, b 1 - r ≤ v 1 ∧ v 1 ≤ b 1 + r := fun v hv => by
    obtain ⟨-, hlo, hhi⟩ := (hWH v hv).1
    constructor <;> linarith
  have hQ : ∀ v ∈ WV.support, a 0 - r ≤ v 0 ∧ v 0 ≤ a 0 + r := fun v hv => by
    obtain ⟨-, hlo, hhi⟩ := (hWV v hv).1
    constructor <;> linarith
  obtain ⟨u, huH, huV⟩ := exists_mem_support_of_crossing WH WV hP hQ hyH.le hzH.ge hyV.le hzV.ge
  exact (reachIn_of_mem_support WH (fun v hv => (hWH v hv).2) huH).trans
    (reachIn_of_mem_support WV (fun v hv => (hWV v hv).2) huV).symm

theorem band_disjoint {c : Vertex 2} {r w j j' : ℕ} {k : Fin 2} {v : Vertex 2} (hw : 1 ≤ w)
    (h : v ∈ band c r w j k) (h' : v ∈ band c r w j' k) : j = j' := by
  obtain ⟨-, h1, h2⟩ := h
  obtain ⟨-, h1', h2'⟩ := h'
  have hw' : (0 : ℤ) ≤ w := by positivity
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : ((j : ℤ) + 1) * w ≤ (j' : ℤ) * w :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hw'
    linarith
  · have : ((j' : ℤ) + 1) * w ≤ (j : ℤ) * w :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) hw'
    linarith

/-- Among channels of one direction with more indices than removed vertices, one is unhit. -/
theorem exists_unhit_channel {c : Vertex 2} {r : ℕ} {i k : Fin 2}
    (hK : HasKestenChannels ω c r i k) (X : Finset (Vertex 2)) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, j < (2 * r + 1) / chanWidth r) (hw : 1 ≤ chanWidth r)
    (hcard : X.card < J.card) :
    ∃ j ∈ J, ∃ y, IsChannel ω (↑X)ᶜ c r (chanWidth r) j i k y := by
  by_contra hne
  have hf : ∀ j ∈ J, ∃ v ∈ X, v ∈ band c r (chanWidth r) j k := by
    intro j hj
    obtain ⟨y, z, hy, hz, hyi, hzi, hreach⟩ := hK j (hJ j hj)
    obtain ⟨W, hW⟩ := exists_walk_of_reachable_openIn hreach hy
    by_contra hnv
    exact hne ⟨j, hj, y, z, W, fun v hv => ⟨hW v hv, fun hvX => hnv ⟨v, hvX, hW v hv⟩⟩, hyi,
      hzi⟩
  choose! f hfX hfb using hf
  have hinj : Set.InjOn f J := fun j hj j' hj' hjj =>
    band_disjoint hw (hfb j hj) (hjj ▸ hfb j' hj')
  exact absurd (Finset.card_le_card_of_injOn f hfX hinj) (not_le.2 hcard)

/-! ### Arithmetic of the bands -/

/-- A block of `a + 1` consecutive bands of width `w` starting after the offset `d`. -/
theorem exists_block (d w a : ℕ) (hw : 1 ≤ w) :
    ∃ j₀, d ≤ j₀ * w ∧ (j₀ + (a + 1)) * w ≤ d + (a + 2) * w - 1 := by
  refine ⟨(d + w - 1) / w, ?_, ?_⟩
  · have h1 := Nat.div_add_mod (d + w - 1) w
    have h2 := Nat.mod_lt (d + w - 1) (by omega : 0 < w)
    rw [Nat.mul_comm] at h1
    omega
  · have h1 := Nat.div_add_mod (d + w - 1) w
    have h2 := Nat.mod_lt (d + w - 1) (by omega : 0 < w)
    rw [Nat.mul_comm] at h1
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul a 2 w]
    omega

/-- The size conditions on `R`: `⌊11R/10⌋ = R + ⌊R/10⌋`, channels of width at least `1`, and
`C_f + 2` channel widths fit in `⌊R/10⌋`. -/
theorem params {Cf R : ℕ} (hR : 800 * (Cf + 2) ^ 2 + 10 ≤ R) :
    11 * R / 10 = R + R / 10 ∧ 1 ≤ chanWidth (11 * R / 10) ∧
      (Cf + 2) * chanWidth (11 * R / 10) ≤ R / 10 ∧ 1 ≤ R / 10 := by
  set r := 11 * R / 10 with hr
  have hr1 : 1 ≤ r := by omega
  have hr2 : r ≤ 2 * R := by omega
  set s := Nat.sqrt r
  have hs1 : 1 ≤ s := Nat.sqrt_pos.2 hr1
  have hss : s ^ 2 ≤ r := Nat.sqrt_le' r
  have hws : chanWidth r ≤ s + 1 := by
    refine Nat.ceil_le.2 (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
    exact_mod_cast (Nat.lt_succ_sqrt' r).le
  have hw1 : 1 ≤ chanWidth r := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have := Nat.ceil_eq_zero.1 h0
    have hpos : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast hr1)
    linarith
  refine ⟨by omega, hw1, ?_, by omega⟩
  have h20 : 20 * (Cf + 2) * s ≤ R := by
    by_contra hlt
    have hlt' := Nat.mul_self_lt_mul_self (not_le.1 hlt)
    have : 20 * (Cf + 2) * s * (20 * (Cf + 2) * s) ≤ R * R := by
      calc 20 * (Cf + 2) * s * (20 * (Cf + 2) * s) = 400 * (Cf + 2) ^ 2 * s ^ 2 := by ring
        _ ≤ 400 * (Cf + 2) ^ 2 * (2 * R) := Nat.mul_le_mul_left _ (hss.trans hr2)
        _ = (800 * (Cf + 2) ^ 2) * R := by ring
        _ ≤ R * R := Nat.mul_le_mul_right _ (by omega)
    omega
  have : (Cf + 2) * chanWidth r ≤ 2 * (Cf + 2) * s := by
    calc (Cf + 2) * chanWidth r ≤ (Cf + 2) * (s + 1) := Nat.mul_le_mul_left _ hws
      _ ≤ (Cf + 2) * (2 * s) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (Cf + 2) * s := by ring
  refine this.trans ((Nat.le_div_iff_mul_le (by norm_num)).2 ?_)
  calc 2 * (Cf + 2) * s * 10 = 20 * (Cf + 2) * s := by ring
    _ ≤ R := h20

/-! ### Propagation of joined channels -/

/-- An unhit channel of `c + Q_r` of either direction, in the band `j`, starting at `y`. -/
def AnyChannel (ω : Configuration 2) (X : Finset (Vertex 2)) (c : Vertex 2) (r j : ℕ)
    (y : Vertex 2) : Prop :=
  IsChannel ω (↑X)ᶜ c r (chanWidth r) j 0 1 y ∨ IsChannel ω (↑X)ᶜ c r (chanWidth r) j 1 0 y

/-- Every unhit channel of `c + Q_r` is joined to `s₀` off `X`. -/
def Reached (ω : Configuration 2) (X : Finset (Vertex 2)) (c : Vertex 2) (r : ℕ) (s₀ : Vertex 2) :
    Prop :=
  ∀ j < (2 * r + 1) / chanWidth r, ∀ y, AnyChannel ω X c r j y → ReachIn ω (↑X)ᶜ s₀ y

/-- An unhit channel of `a + Q_r` and one of `b + Q_r` joined off `X`. -/
def Linked (ω : Configuration 2) (X : Finset (Vertex 2)) (a b : Vertex 2) (r : ℕ) : Prop :=
  ∃ j < (2 * r + 1) / chanWidth r, ∃ y, AnyChannel ω X a r j y ∧
    ∃ j' < (2 * r + 1) / chanWidth r, ∃ y', AnyChannel ω X b r j' y' ∧ ReachIn ω (↑X)ᶜ y y'

theorem Linked.symm {X : Finset (Vertex 2)} {a b : Vertex 2} {r : ℕ} (h : Linked ω X a b r) :
    Linked ω X b a r := by
  obtain ⟨j, hj, y, hy, j', hj', y', hy', hr⟩ := h
  exact ⟨j', hj', y', hy', j, hj, y, hy, hr.symm⟩

theorem succ_mul_le_of_lt_div {j n w : ℕ} (h : j < n / w) : (j + 1) * w ≤ n :=
  (Nat.mul_le_mul_right w (Nat.succ_le_of_lt h)).trans (Nat.div_mul_le_self n w)

theorem lt_div_of_succ_mul_le {j n w : ℕ} (hw : 1 ≤ w) (h : (j + 1) * w ≤ n) : j < n / w :=
  Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (by omega)).2 h)

theorem cast_succ_mul_le_of_lt_div {j r w : ℕ} (h : j < (2 * r + 1) / w) :
    ((j : ℤ) + 1) * w ≤ 2 * r + 1 := by
  exact_mod_cast succ_mul_le_of_lt_div h

/-- A horizontal and a vertical channel of one cube meet. -/
theorem reachIn_same_cube {T : Set (Vertex 2)} {c : Vertex 2} {r jH jV : ℕ} {yH yV : Vertex 2}
    (hH : IsChannel ω T c r (chanWidth r) jH 0 1 yH) (hV : IsChannel ω T c r (chanWidth r) jV 1 0 yV)
    (hjH : jH < (2 * r + 1) / chanWidth r) (hjV : jV < (2 * r + 1) / chanWidth r) :
    ReachIn ω T yH yV := by
  have h1 := cast_succ_mul_le_of_lt_div hjH
  have h2 := cast_succ_mul_le_of_lt_div hjV
  have h3 : (0 : ℤ) ≤ jH * chanWidth r := by positivity
  have h4 : (0 : ℤ) ≤ jV * chanWidth r := by positivity
  exact reachIn_of_channels hH hV (by linarith) (by linarith) (by linarith) (by linarith)

/-- If one unhit channel of a very good cube is joined to `s₀` off `X`, all of them are. -/
theorem reached_of_channel {X : Finset (Vertex 2)} {c : Vertex 2} {r j : ℕ} {y s₀ : Vertex 2}
    (hc : IsVeryGood ω c r) (hw : 1 ≤ chanWidth r) (hN : X.card < (2 * r + 1) / chanWidth r)
    (hj : j < (2 * r + 1) / chanWidth r) (hy : AnyChannel ω X c r j y)
    (hs : ReachIn ω (↑X)ᶜ s₀ y) : Reached ω X c r s₀ := by
  have hJ : ∀ j ∈ Finset.range ((2 * r + 1) / chanWidth r), j < (2 * r + 1) / chanWidth r :=
    fun j hj => Finset.mem_range.1 hj
  have hcard : X.card < (Finset.range ((2 * r + 1) / chanWidth r)).card := by
    rwa [Finset.card_range]
  have hV : (∃ jH < (2 * r + 1) / chanWidth r, ∃ yH, IsChannel ω (↑X)ᶜ c r (chanWidth r) jH 0 1 yH ∧
      ReachIn ω (↑X)ᶜ s₀ yH) → ∀ jV < (2 * r + 1) / chanWidth r, ∀ yV,
        IsChannel ω (↑X)ᶜ c r (chanWidth r) jV 1 0 yV → ReachIn ω (↑X)ᶜ s₀ yV :=
    fun ⟨jH, hjH, yH, hH, hs⟩ jV hjV yV hV' => hs.trans (reachIn_same_cube hH hV' hjH hjV)
  have hH : (∃ jV < (2 * r + 1) / chanWidth r, ∃ yV, IsChannel ω (↑X)ᶜ c r (chanWidth r) jV 1 0 yV ∧
      ReachIn ω (↑X)ᶜ s₀ yV) → ∀ jH < (2 * r + 1) / chanWidth r, ∀ yH,
        IsChannel ω (↑X)ᶜ c r (chanWidth r) jH 0 1 yH → ReachIn ω (↑X)ᶜ s₀ yH :=
    fun ⟨jV, hjV, yV, hV', hs⟩ jH hjH yH hH' => hs.trans (reachIn_same_cube hH' hV' hjH hjV).symm
  obtain ⟨jH₁, hjH₁, yH₁, hH₁⟩ := exists_unhit_channel hc.2.1 X _ hJ hw hcard
  obtain ⟨jV₁, hjV₁, yV₁, hV₁⟩ := exists_unhit_channel hc.2.2 X _ hJ hw hcard
  have hjH₁' := Finset.mem_range.1 hjH₁
  have hjV₁' := Finset.mem_range.1 hjV₁
  rcases hy with hy | hy
  · have hallV := hV ⟨j, hj, y, hy, hs⟩
    have hallH := hH ⟨jV₁, hjV₁', yV₁, hV₁, hallV jV₁ hjV₁' yV₁ hV₁⟩
    exact fun j' hj' y' hy' => hy'.elim (hallH j' hj' y') (hallV j' hj' y')
  · have hallH := hH ⟨j, hj, y, hy, hs⟩
    have hallV := hV ⟨jH₁, hjH₁', yH₁, hH₁, hallH jH₁ hjH₁' yH₁ hH₁⟩
    exact fun j' hj' y' hy' => hy'.elim (hallH j' hj' y') (hallV j' hj' y')

theorem Reached.of_linked {X : Finset (Vertex 2)} {a b : Vertex 2} {r : ℕ} {s₀ : Vertex 2}
    (hb : IsVeryGood ω b r) (hw : 1 ≤ chanWidth r) (hN : X.card < (2 * r + 1) / chanWidth r)
    (hl : Linked ω X a b r) (ha : Reached ω X a r s₀) : Reached ω X b r s₀ := by
  obtain ⟨j, hj, y, hy, j', hj', y', hy', hr⟩ := hl
  exact reached_of_channel hb hw hN hj' hy' ((ha j hj y hy).trans hr)

/-- The size conditions on the bands, for `r = R + m` with `(C_f + 2) w ≤ m`: a block of
`C_f + 1` bands of `a + Q_r` beyond the offset `2R + 1`, inside `a + Q_r`. -/
theorem exists_overlap_block {Cf R m r : ℕ} (hr : r = R + m) (hw : 1 ≤ chanWidth r)
    (hm : (Cf + 2) * chanWidth r ≤ m) :
    ∃ j₀, 2 * R + 1 ≤ j₀ * chanWidth r ∧ ∀ j ∈ Finset.Ico j₀ (j₀ + (Cf + 1)),
      j < (2 * r + 1) / chanWidth r ∧ 2 * R + 1 ≤ j * chanWidth r := by
  obtain ⟨j₀, h1, h2⟩ := exists_block (2 * R + 1) (chanWidth r) Cf hw
  refine ⟨j₀, h1, fun j hj => ?_⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
  refine ⟨lt_div_of_succ_mul_le hw ?_, h1.trans (Nat.mul_le_mul_right _ hj1)⟩
  calc (j + 1) * chanWidth r ≤ (j₀ + (Cf + 1)) * chanWidth r := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2 * r + 1 := by omega

/-- Very good cubes of horizontally or vertically neighbouring renormalized sites carry linked
unhit channels. -/
theorem linked_of_neighbours {X : Finset (Vertex 2)} {Cf R m r : ℕ} {a b : Vertex 2}
    (hr : r = R + m) (hw : 1 ≤ chanWidth r) (hm : (Cf + 2) * chanWidth r ≤ m)
    (hX : X.card ≤ Cf) (ha : IsVeryGood ω a r) (hb : IsVeryGood ω b r)
    (hab : (b 0 = a 0 + (2 * R + 1) ∧ b 1 = a 1) ∨ (b 1 = a 1 + (2 * R + 1) ∧ b 0 = a 0)) :
    Linked ω X a b r := by
  obtain ⟨j₀, -, hblock⟩ := exists_overlap_block (Cf := Cf) hr hw hm
  have hJ : ∀ j ∈ Finset.Ico j₀ (j₀ + (Cf + 1)), j < (2 * r + 1) / chanWidth r :=
    fun j hj => (hblock j hj).1
  have hcardJ : X.card < (Finset.Ico j₀ (j₀ + (Cf + 1))).card := by
    rw [Nat.card_Ico]
    omega
  have hN : X.card < (2 * r + 1) / chanWidth r := by
    have := (hblock j₀ (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩)).1
    have h2 := (hblock (j₀ + Cf) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)).1
    omega
  have hR : ∀ J : Finset ℕ, (∀ j ∈ J, j < (2 * r + 1) / chanWidth r) →
      ∀ j ∈ J, ∀ j' < (2 * r + 1) / chanWidth r, ((j : ℤ) + 1) * chanWidth r ≤ 2 * r + 1 ∧
        ((j' : ℤ) + 1) * chanWidth r ≤ 2 * r + 1 ∧ (0 : ℤ) ≤ j' * chanWidth r :=
    fun J hJ j hj j' hj' => ⟨cast_succ_mul_le_of_lt_div (hJ j hj),
      cast_succ_mul_le_of_lt_div hj', by positivity⟩
  have hrange : ∀ j ∈ Finset.range ((2 * r + 1) / chanWidth r), j < (2 * r + 1) / chanWidth r :=
    fun j hj => Finset.mem_range.1 hj
  have hcardN : X.card < (Finset.range ((2 * r + 1) / chanWidth r)).card := by
    rwa [Finset.card_range]
  rcases hab with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · obtain ⟨jV, hjV, yV, hV⟩ := exists_unhit_channel ha.2.2 X _ hJ hw hcardJ
    obtain ⟨jH, hjH, yH, hH⟩ := exists_unhit_channel hb.2.1 X _ hrange hw hcardN
    have hjH' := Finset.mem_range.1 hjH
    obtain ⟨hV1, hH1, hH0⟩ := hR _ hJ jV hjV jH hjH'
    have hV2 : ((2 * R + 1 : ℕ) : ℤ) ≤ ((jV * chanWidth r : ℕ) : ℤ) :=
      by exact_mod_cast (hblock jV hjV).2
    push_cast at hV2
    refine ⟨jV, hJ jV hjV, yV, Or.inr hV, jH, hjH', yH, Or.inl hH, ?_⟩
    exact (reachIn_of_channels hH hV (by linarith) (by linarith) (by linarith)
      (by linarith)).symm
  · obtain ⟨jH, hjH, yH, hH⟩ := exists_unhit_channel ha.2.1 X _ hJ hw hcardJ
    obtain ⟨jV, hjV, yV, hV⟩ := exists_unhit_channel hb.2.2 X _ hrange hw hcardN
    have hjV' := Finset.mem_range.1 hjV
    obtain ⟨hH1, hV1, hV0⟩ := hR _ hJ jH hjH jV hjV'
    have hH2 : ((2 * R + 1 : ℕ) : ℤ) ≤ ((jH * chanWidth r : ℕ) : ℤ) :=
      by exact_mod_cast (hblock jH hjH).2
    push_cast at hH2
    refine ⟨jH, hJ jH hjH, yH, Or.inl hH, jV, hjV', yV, Or.inr hV, ?_⟩
    exact reachIn_of_channels hH hV (by linarith) (by linarith) (by linarith) (by linarith)

/-! ### The crossing of the connected set -/

theorem bounds_of_mem_cubeAt {c v : Vertex 2} {r : ℕ} (h : v ∈ cubeAt c r) (i : Fin 2) :
    c i - r ≤ v i ∧ v i ≤ c i + r := by
  have := abs_le.1 (h i)
  constructor <;> linarith [this.1, this.2]

/-- A walk inside `T_S ∩ (c + Q_r)` going up by `m` in the coordinate `k` crosses a block of
`C_f + 1` bands of the very good cube `c + Q_r`; an unhit channel among them meets the walk at a
vertex `s₀ ∈ T_S`, to which all unhit channels of the cube are then joined off `X`. -/
theorem exists_reached_of_crossing {X : Finset (Vertex 2)} {Cf m r : ℕ} {TS : Set (Vertex 2)}
    {c a b : Vertex 2} {k : Fin 2} (W : (openGraph ω).Walk a b)
    (hW : ∀ v ∈ W.support, v ∈ TS ∧ v ∈ cubeAt c r) (hlo : c k - r ≤ a k) (hab : a k + m ≤ b k)
    (hhi : a k + m ≤ c k + r) (hc : IsVeryGood ω c r) (hw : 1 ≤ chanWidth r)
    (hm : (Cf + 2) * chanWidth r ≤ m) (hX : X.card ≤ Cf)
    (hN : X.card < (2 * r + 1) / chanWidth r) : ∃ s₀ ∈ TS, Reached ω X c r s₀ := by
  set d := (a k - (c k - r)).toNat with hd
  have hd' : (d : ℤ) = a k - (c k - r) := Int.toNat_of_nonneg (by linarith)
  obtain ⟨j₀, h1, h2⟩ := exists_block d (chanWidth r) Cf hw
  have hJ : ∀ j ∈ Finset.Ico j₀ (j₀ + (Cf + 1)), j < (2 * r + 1) / chanWidth r ∧
      a k ≤ c k - r + j * chanWidth r ∧ c k - r + (j + 1) * chanWidth r - 1 ≤ a k + m := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    have e1 : j₀ * chanWidth r ≤ j * chanWidth r := Nat.mul_le_mul_right _ hj1
    have e2 : (j + 1) * chanWidth r ≤ (j₀ + (Cf + 1)) * chanWidth r :=
      Nat.mul_le_mul_right _ (by omega)
    have f1 : (d : ℤ) ≤ (j : ℤ) * chanWidth r := by exact_mod_cast h1.trans e1
    have f2 : ((j : ℤ) + 1) * chanWidth r ≤ d + m := by
      have : (j + 1) * chanWidth r ≤ d + m := by omega
      exact_mod_cast this
    refine ⟨lt_div_of_succ_mul_le hw ?_, by linarith, by linarith⟩
    have h3 : (d : ℤ) + m ≤ 2 * r := by linarith
    have h4 : d + m ≤ 2 * r := by exact_mod_cast h3
    omega
  have hcard : X.card < (Finset.Ico j₀ (j₀ + (Cf + 1))).card := by
    rw [Nat.card_Ico]
    omega
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · obtain ⟨j, hj, y, z, WV, hWV, hy1, hz1⟩ :=
      exists_unhit_channel hc.2.2 X _ (fun j hj => (hJ j hj).1) hw hcard
    obtain ⟨hjN, hja, hjb⟩ := hJ j hj
    have hP : ∀ v ∈ W.support, c 1 - r ≤ v 1 ∧ v 1 ≤ c 1 + r :=
      fun v hv => bounds_of_mem_cubeAt (hW v hv).2 1
    have hQ : ∀ v ∈ WV.support, c 0 - r + j * chanWidth r ≤ v 0 ∧
        v 0 ≤ c 0 - r + (j + 1) * chanWidth r - 1 := fun v hv => (hWV v hv).1.2
    obtain ⟨u, huW, huV⟩ := exists_mem_support_of_crossing W WV hP hQ hja (by linarith)
      hy1.le hz1.ge
    exact ⟨u, (hW u huW).1, reached_of_channel hc hw hN hjN (Or.inr ⟨z, WV, hWV, hy1, hz1⟩)
      (reachIn_of_mem_support WV (fun v hv => (hWV v hv).2) huV).symm⟩
  · obtain ⟨j, hj, y, z, WH, hWH, hy1, hz1⟩ :=
      exists_unhit_channel hc.2.1 X _ (fun j hj => (hJ j hj).1) hw hcard
    obtain ⟨hjN, hja, hjb⟩ := hJ j hj
    have hP : ∀ v ∈ WH.support, c 1 - r + j * chanWidth r ≤ v 1 ∧
        v 1 ≤ c 1 - r + (j + 1) * chanWidth r - 1 := fun v hv => (hWH v hv).1.2
    have hQ : ∀ v ∈ W.support, c 0 - r ≤ v 0 ∧ v 0 ≤ c 0 + r :=
      fun v hv => bounds_of_mem_cubeAt (hW v hv).2 0
    obtain ⟨u, huH, huW⟩ := exists_mem_support_of_crossing WH W hP hQ hy1.le hz1.ge hja
      (by linarith)
    exact ⟨u, (hW u huW).1, reached_of_channel hc hw hN hjN (Or.inl ⟨z, WH, hWH, hy1, hz1⟩)
      (reachIn_of_mem_support WH (fun v hv => (hWH v hv).2) huH).symm⟩

/-- The first step of a walk from outside `P` into `P`, with the initial segment before it. -/
theorem exists_walk_exit {P : Vertex 2 → Prop} :
    ∀ {a b : Vertex 2} (W : (openGraph ω).Walk a b), ¬ P a → P b →
      ∃ v u, (openGraph ω).Adj v u ∧ P u ∧ u ∈ W.support ∧
        ∃ W' : (openGraph ω).Walk a v, ∀ y ∈ W'.support, y ∈ W.support ∧ ¬ P y
  | _, _, .nil, ha, hb => absurd hb ha
  | a, _, @SimpleGraph.Walk.cons _ _ _ a' _ h p, ha, hb => by
    by_cases ha' : P a'
    · refine ⟨a, a', h, ha', by simp, .nil, fun y hy => ?_⟩
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      subst hy
      exact ⟨by simp, ha⟩
    · obtain ⟨v, u, hvu, hu, huW, W', hW'⟩ := exists_walk_exit p ha' hb
      refine ⟨v, u, hvu, hu, by simp [huW], .cons h W', fun y hy => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨by simp, ha⟩
      · exact ⟨by simp [(hW' y hy).1], (hW' y hy).2⟩

/-- A set of `ℓ¹` diameter at least `R` has a point at `ℓ^∞` distance at least `⌊R/10⌋` from
any given point. -/
theorem exists_far_of_diam {R : ℕ} {x : Vertex 2} {TS : Set (Vertex 2)}
    (hdiam : ∃ y ∈ TS, ∃ y' ∈ TS, (R : ℝ) ≤ l1 (y - y')) :
    ∃ y ∈ TS, ∃ k, ((R / 10 : ℕ) : ℤ) ≤ |y k - x k| := by
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  obtain ⟨y, hy, y', hy', hR'⟩ := hdiam
  have hl1 : l1 (y - y') = ((|y 0 - y' 0| + |y 1 - y' 1| : ℤ) : ℝ) := by
    simp [l1, Fin.sum_univ_two]
  rw [hl1, show (R : ℝ) = ((R : ℤ) : ℝ) by norm_cast, Int.cast_le] at hR'
  have b0 := abs_lt.1 (hne y hy 0)
  have b1 := abs_lt.1 (hne y hy 1)
  have b0' := abs_lt.1 (hne y' hy' 0)
  have b1' := abs_lt.1 (hne y' hy' 1)
  have c0 : |y 0 - y' 0| ≤ 2 * ((R / 10 : ℕ) : ℤ) - 2 := abs_le.2 ⟨by omega, by omega⟩
  have c1 : |y 1 - y' 1| ≤ 2 * ((R / 10 : ℕ) : ℤ) - 2 := abs_le.2 ⟨by omega, by omega⟩
  omega

/-- A walk of `𝒞_∞` inside the connected set `S`, read in `ℤ²`. -/
theorem exists_walk_of_isConnectedSet {C : OpenComponent ω} {S : Set C}
    (hS : IsConnectedSet C S) {x y : C} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ W : (openGraph ω).Walk x.val y.val, ∀ v ∈ W.support, v ∈ Subtype.val '' S := by
  obtain ⟨hx', hy', ⟨p⟩⟩ := hS x hx y hy
  let φ : ((componentGraph C).induce S) →g openGraph ω := ⟨fun q => q.val.val, fun h => h⟩
  refine ⟨p.map φ, fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
  obtain ⟨q, -, rfl⟩ := hv
  exact ⟨q.val, q.property, rfl⟩

/-! ### Assembly -/

/-- The open graph restricted to the complement of `X`. -/
def offGraph (ω : Configuration 2) (X : Finset (Vertex 2)) : SimpleGraph (Vertex 2) where
  Adj a b := (openGraph ω).Adj a b ∧ a ∉ X ∧ b ∉ X
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

theorem reachable_offGraph {X : Finset (Vertex 2)} :
    ∀ {a b : Vertex 2} (W : (openGraph ω).Walk a b),
      (∀ v ∈ W.support, v ∈ (↑X : Set (Vertex 2))ᶜ) → (offGraph ω X).Reachable a b
  | _, _, .nil, _ => SimpleGraph.Reachable.refl _
  | _, _, .cons h p, hW => by
    have h1 := hW _ (List.mem_cons_self ..)
    have h2 := hW _ (List.mem_cons_of_mem _ p.start_mem_support)
    exact (SimpleGraph.Adj.reachable (G := offGraph ω X) ⟨h, h1, h2⟩).trans
      (reachable_offGraph p fun v hv => hW v (List.mem_cons_of_mem _ hv))

theorem open_of_walk {η : PlanarCarrier → Bool} :
    ∀ {z₁ z₂ : PlanarCarrier} (_ : (Rigidity.Steps.Section5.siteOpenGraph η).Walk z₁ z₂),
      η z₁ = true → η z₂ = true
  | _, _, .nil, h => h
  | _, _, .cons h p, _ => open_of_walk p h.2.2

theorem bounds_of_abs_sub_mul_le {a t y M r : ℤ} (ha : 1 ≤ a) (hy : |y| ≤ M)
    (h : |y - a * t| ≤ r) : -(M + r) ≤ t ∧ t ≤ M + r := by
  have h1 := abs_le.1 hy
  have h2 := abs_le.1 h
  rcases le_or_gt 0 t with ht | ht
  · have : t ≤ a * t := by nlinarith
    constructor <;> linarith
  · have : a * t ≤ t := by nlinarith
    constructor <;> linarith

end Kesten

open Kesten Rigidity.Section5 Rigidity.Steps.Section5 in
/-- **Step `step:5.21-renorm-paths`, cut form**: for `R ≥ 800 (C_f + 2)² + 10`, if the
renormalized site `z` lies in an infinite open cluster of the renormalized process of size `R`
and `x ∈ (2R + 1) z + Q_R`, then for every finite connected `S ⊆ 𝒞_∞` containing `x` of diameter
at least `R` and every set `X` of at most `C_f` vertices of `𝒞_∞`, some infinite path of `𝒞_∞`
starts in `S` and avoids `X`. -/
theorem kestenChannelCutStep : KestenChannelCutStep := by
  intro Cf
  refine ⟨800 * (Cf + 2) ^ 2 + 10, fun R hR ω z hz x hx h S _ hSc hxS hdiam X hX => ?_⟩
  obtain ⟨hr, hw, hm, hm1⟩ := params hR
  set r := 11 * R / 10 with hr_def
  set m := R / 10 with hm_def
  set X' : Finset (Vertex 2) := X.image Subtype.val with hX'_def
  have hX' : X'.card ≤ Cf := Finset.card_image_le.trans hX
  have hvg : ∀ z', renormField R ω z' = true → IsVeryGood ω (renormCentre R z') r :=
    fun z' h' => of_decide_eq_true h'
  have hN : X'.card < (2 * r + 1) / chanWidth r := by
    obtain ⟨j₀, -, hblock⟩ := exists_overlap_block (Cf := Cf) hr hw hm
    have := (hblock (j₀ + Cf) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)).1
    omega
  obtain ⟨x₀, hx₀S, rfl⟩ := hxS
  have hxc : ∀ i, |x₀.val i - renormCentre R z i| ≤ R := hx
  -- a walk of `S` from `x` to its first exit from `x + Q_{m - 1}`
  obtain ⟨_, ⟨y₁, hy₁S, rfl⟩, k, hk⟩ := exists_far_of_diam (x := x₀.val)
    (TS := Subtype.val '' S) (by
      obtain ⟨y, hy, y', hy', h'⟩ := hdiam
      exact ⟨y.val, ⟨y, hy, rfl⟩, y'.val, ⟨y', hy', rfl⟩, h'⟩)
  obtain ⟨W, hW⟩ := exists_walk_of_isConnectedSet hSc hx₀S hy₁S
  obtain ⟨v, u, hvu, hPu, huW, W', hW'⟩ :=
    exists_walk_exit (P := fun v => ∃ k, (m : ℤ) ≤ |v k - x₀.val k|) W (by
      rintro ⟨k, hk⟩
      simp only [sub_self, abs_zero] at hk
      omega) ⟨k, hk⟩
  have hW'b : ∀ y ∈ W'.support, ∀ i, |y i - x₀.val i| < m := by
    intro y hy i
    have := (hW' y hy).2
    simp only [not_exists, not_le] at this
    exact this i
  have hub : ∀ i, |u i - x₀.val i| ≤ m := by
    intro i
    have h1 := abs_le.1 (abs_sub_le_one_of_adj hvu i)
    have h2 := abs_lt.1 (hW'b v W'.end_mem_support i)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  set Q := W'.concat hvu
  have hQ : ∀ y ∈ Q.support, y ∈ Subtype.val '' S ∧ y ∈ cubeAt (renormCentre R z) r := by
    intro y hy
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · refine ⟨hW _ (hW' y hy).1, fun i => ?_⟩
      have h1 := abs_lt.1 (hW'b y hy i)
      have h2 := abs_le.1 (hxc i)
      exact abs_le.2 ⟨by omega, by omega⟩
    · refine ⟨hW _ huW, fun i => ?_⟩
      have h1 := abs_le.1 (hub i)
      have h2 := abs_le.1 (hxc i)
      exact abs_le.2 ⟨by omega, by omega⟩
  obtain ⟨k', hk'⟩ := hPu
  have hub' := abs_le.1 (hub k')
  have hxk := abs_le.1 (hxc k')
  have hc0 := hvg z hz.1
  obtain ⟨s₀, hs₀S, hs₀⟩ : ∃ s₀ ∈ Subtype.val '' S, Reached ω X' (renormCentre R z) r s₀ := by
    rcases le_or_gt 0 (u k' - x₀.val k') with hpos | hneg
    · rw [abs_of_nonneg hpos] at hk'
      exact exists_reached_of_crossing Q hQ (k := k') (by omega) (by omega) (by omega) hc0 hw hm
        hX' hN
    · rw [abs_of_neg hneg] at hk'
      exact exists_reached_of_crossing Q.reverse (fun y hy => hQ y (by
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy)) (k := k') (by omega)
        (by omega) (by omega) hc0 hw hm hX' hN
  -- propagation along the renormalized cluster of `z`
  have e0 : ∀ z' : ℤ × ℤ, renormCentre R z' 0 = (2 * R + 1) * z'.1 := fun _ => rfl
  have e1 : ∀ z' : ℤ × ℤ, renormCentre R z' 1 = (2 * R + 1) * z'.2 := fun _ => rfl
  have hstep : ∀ z₁ z₂, (siteOpenGraph (renormField R ω)).Adj z₁ z₂ →
      Reached ω X' (renormCentre R z₁) r s₀ → Reached ω X' (renormCentre R z₂) r s₀ := by
    intro z₁ z₂ hadj h1
    obtain ⟨hd, hη1, hη2⟩ := hadj
    have hv1 := hvg z₁ hη1
    have hv2 := hvg z₂ hη2
    refine Reached.of_linked hv2 hw hN ?_ h1
    have hcases : (z₂.1 = z₁.1 + 1 ∧ z₂.2 = z₁.2) ∨ (z₁.1 = z₂.1 + 1 ∧ z₂.2 = z₁.2) ∨
        (z₂.2 = z₁.2 + 1 ∧ z₂.1 = z₁.1) ∨ (z₁.2 = z₂.2 + 1 ∧ z₂.1 = z₁.1) := by
      rcases abs_cases (z₁.1 - z₂.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (z₁.2 - z₂.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact linked_of_neighbours hr hw hm hX' hv1 hv2
        (Or.inl ⟨by rw [e0, e0, ha]; ring, by rw [e1, e1, hb]⟩)
    · exact (linked_of_neighbours hr hw hm hX' hv2 hv1
        (Or.inl ⟨by rw [e0, e0, ha]; ring, by rw [e1, e1, hb]⟩)).symm
    · exact linked_of_neighbours hr hw hm hX' hv1 hv2
        (Or.inr ⟨by rw [e1, e1, ha]; ring, by rw [e0, e0, hb]⟩)
    · exact (linked_of_neighbours hr hw hm hX' hv2 hv1
        (Or.inr ⟨by rw [e1, e1, ha]; ring, by rw [e0, e0, hb]⟩)).symm
  have hall : ∀ z₁ z₂ (p : (siteOpenGraph (renormField R ω)).Walk z₁ z₂),
      Reached ω X' (renormCentre R z₁) r s₀ → Reached ω X' (renormCentre R z₂) r s₀ := by
    intro z₁ z₂ p
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun h1 => ih (hstep _ _ hadj h1)
  -- infinitely many vertices are joined to `s₀` off `X`
  have hinf : {w | ReachIn ω (↑X')ᶜ s₀ w}.Infinite := by
    intro hfin
    obtain ⟨M, hM⟩ := (hfin.image fun v => |v 0| + |v 1|).bddAbove
    refine hz.2 (((Set.finite_Icc (-(M + r)) (M + r)).prod
      (Set.finite_Icc (-(M + r)) (M + r))).subset fun z' hz' => ?_)
    obtain ⟨p⟩ := hz'
    have hη := open_of_walk p hz.1
    obtain ⟨j, hj, y, hy⟩ := exists_unhit_channel (hvg z' hη).2.1 X'
      (Finset.range ((2 * r + 1) / chanWidth r)) (fun j hj => Finset.mem_range.1 hj) hw
      (by rwa [Finset.card_range])
    have hreach := hall z z' p hs₀ j (Finset.mem_range.1 hj) y (Or.inl hy)
    obtain ⟨_, WH, hWH, -, -⟩ := hy
    have hyc := (hWH y WH.start_mem_support).1.1
    have hyM : |y 0| + |y 1| ≤ M := hM ⟨y, hreach, rfl⟩
    have hy0 : |y 0| ≤ M := by linarith [abs_nonneg (y 1)]
    have hy1 : |y 1| ≤ M := by linarith [abs_nonneg (y 0)]
    have ha : (1 : ℤ) ≤ 2 * R + 1 := by omega
    have b0 := bounds_of_abs_sub_mul_le (t := z'.1) (r := r) ha hy0 (hyc 0)
    have b1 := bounds_of_abs_sub_mul_le (t := z'.2) (r := r) ha hy1 (hyc 1)
    exact Set.mem_prod.2 ⟨Set.mem_Icc.2 b0, Set.mem_Icc.2 b1⟩
  -- König's lemma
  have hfinG : ∀ v, ((offGraph ω X').neighborSet v).Finite := fun v =>
    ((openGraph ω).neighborSet v).toFinite.subset fun _ hu => hu.1
  obtain ⟨γ, hinj, hadj, h0⟩ := Menger.exists_ray_of_infinite hfinG (v := s₀)
    (Set.Infinite.mono (fun w hw => by
      obtain ⟨W, hW⟩ := hw
      exact reachable_offGraph W hW) hinf)
  obtain ⟨s, hsS, rfl⟩ := hs₀S
  have hreachγ : ∀ n, (openGraph ω).Reachable s.val (γ n) := by
    intro n
    induction n with
    | zero => exact h0.symm ▸ SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (hadj n).1.reachable
  have hmem : ∀ n, γ n ∈ uniqueInfiniteComponent h := fun n =>
    (SimpleGraph.ConnectedComponent.sound (hreachγ n)).symm.trans s.property
  refine ⟨fun n => ⟨γ n, hmem n⟩, ⟨fun a b hab => hinj (congrArg Subtype.val hab),
    fun n => (hadj n).1, fun n hn => (hadj n).2.1 (Finset.mem_image_of_mem _ hn)⟩, ?_⟩
  have : (⟨γ 0, hmem 0⟩ : uniqueInfiniteComponent h) = s := Subtype.ext h0
  show (⟨γ 0, hmem 0⟩ : uniqueInfiniteComponent h) ∈ S
  rw [this]
  exact hsS

end Rigidity.Proofs.Section5
