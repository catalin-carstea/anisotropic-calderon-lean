import C3PartialJets
import Calderon.ActualRadiusTwoGreenL2Coefficient
import Calderon.CollaboratorUCPIdentityOct17
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry

theorem v015_original_kernel_joint_regular : OriginalKernelJointRegularityGoal :=
  Geometry.original_kernel_joint_regular
theorem v015_normal_packet_cover_exists : NativeNormalPacketCoverGoal :=
  Geometry.normal_packet_cover_exists
theorem v015_initial_cross_product : InitialCrossProductGoal := Geometry.initial_cross_product

section C3Grid
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- Two points in the same floor cell of mesh `1/a` are at distance `< 3/a`. -/
theorem floorCell_norm_lt (ρ a : ℝ) (ha : 0 < a) (x y : R3)
    (hx : ∀ j, 0 ≤ (x j + ρ) * a) (hy : ∀ j, 0 ≤ (y j + ρ) * a)
    (hxy : ∀ j, ⌊(x j + ρ) * a⌋₊ = ⌊(y j + ρ) * a⌋₊) : ‖x - y‖ < 3 / a := by
  have hc : ∀ j, ((x j - y j) * a) ^ 2 < 1 := by
    intro j
    have h1 := Nat.lt_floor_add_one ((x j + ρ) * a)
    have h2 := Nat.lt_floor_add_one ((y j + ρ) * a)
    have h3 := Nat.floor_le (hx j)
    have h4 := Nat.floor_le (hy j)
    rw [hxy j] at h1 h3
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]
    constructor <;> nlinarith
  have hsq : ‖x - y‖ ^ 2 * a ^ 2 < 3 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    nlinarith
  have h3a : (3 / a) ^ 2 * a ^ 2 = 9 := by
    field_simp
    norm_num
  have hlt : ‖x - y‖ ^ 2 < (3 / a) ^ 2 := by
    by_contra h
    push_neg at h
    have := mul_le_mul_of_nonneg_right h (sq_nonneg a)
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-- C3-D4 grid: the actual Cartesian floor grid of mesh `1/a` on `[-r, r)^3`, cut down to `S`,
with empty cells excluded (so no case split on `S = ∅`). Centres are actual points of `S`. -/
theorem exists_floor_grid (S K0 : Set R3) (hS : MeasurableSet S) (hSK0 : S ⊆ K0) (r : ℕ)
    (hr : ∀ x ∈ K0, ∀ j, |x j| < (r : ℝ)) (a : ℕ) (hapos : (0 : ℝ) < a) :
    ∃ (N : ℕ) (Q : Fin N → Set R3) (c : Fin N → R3),
      (∀ i, MeasurableSet (Q i)) ∧ Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      S ⊆ ⋃ i, Q i ∧ (∀ i, c i ∈ S) ∧ (∀ i, ∀ x ∈ Q i, ‖x - c i‖ < 3 / (a : ℝ)) ∧
      N ≤ (2 * r * a) ^ 3 := by
  classical
  let fl : R3 → Fin 3 → ℕ := fun x j => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊
  let n : ℕ := 2 * r * a
  let Qz : (Fin 3 → ℕ) → Set R3 := fun z => S ∩ {x | fl x = z}
  let T : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset fun _ : Fin 3 => Finset.range n).filter fun z => (Qz z).Nonempty
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hne : ∀ i, (Qz (e i : Fin 3 → ℕ)).Nonempty := fun i => (Finset.mem_filter.mp (e i).2).2
  let Q : Fin T.card → Set R3 := fun i => Qz (e i : Fin 3 → ℕ)
  let c : Fin T.card → R3 := fun i => (hne i).some
  have hpos_coord : ∀ x ∈ K0, ∀ j, 0 ≤ (x j + (r : ℝ)) * (a : ℝ) := by
    intro x hx j
    have h1 := hr x hx j
    rw [abs_lt] at h1
    exact mul_nonneg (by linarith) hapos.le
  have hcQ : ∀ i, c i ∈ Q i := fun i => (hne i).some_mem
  refine ⟨T.card, Q, c, ?_, ?_, ?_, fun i => (hcQ i).1, ?_, ?_⟩
  · intro i
    refine hS.inter ?_
    have hflm : ∀ j : Fin 3, Measurable fun x : R3 => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊ := fun j =>
      ((((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).add_const _).mul_const
        _).nat_floor
    have hset : {x : R3 | fl x = (e i : Fin 3 → ℕ)} =
        ⋂ j, (fun x : R3 => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊) ⁻¹' {(e i : Fin 3 → ℕ) j} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, mem_preimage, mem_singleton_iff, fl, funext_iff]
    show MeasurableSet {x : R3 | fl x = (e i : Fin 3 → ℕ)}
    rw [hset]
    exact MeasurableSet.iInter fun j => hflm j (measurableSet_singleton _)
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    have h1 : fl x = (e i : Fin 3 → ℕ) := hxi.2
    have h2 : fl x = (e j : Fin 3 → ℕ) := hxj.2
    exact e.injective (Subtype.ext (h1.symm.trans h2))
  · intro x hxS
    have hxK := hSK0 hxS
    have hzT : fl x ∈ T := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ⟨x, hxS, rfl⟩⟩
      refine Finset.mem_range.mpr ((Nat.floor_lt (hpos_coord x hxK j)).mpr ?_)
      have h1 := hr x hxK j
      rw [abs_lt] at h1
      have h2 : (x j + (r : ℝ)) * (a : ℝ) < (2 * r : ℝ) * a :=
        mul_lt_mul_of_pos_right (by linarith) hapos
      have h3 : ((n : ℕ) : ℝ) = (2 * r : ℝ) * a := by simp only [n]; push_cast; ring
      rw [h3]
      exact h2
    refine mem_iUnion.mpr ⟨e.symm ⟨fl x, hzT⟩, ?_⟩
    show x ∈ Qz (e (e.symm ⟨fl x, hzT⟩) : Fin 3 → ℕ)
    rw [Equiv.apply_symm_apply]
    exact ⟨hxS, rfl⟩
  · intro i x hx
    have h1 : fl x = (e i : Fin 3 → ℕ) := hx.2
    have h2 : fl (c i) = (e i : Fin 3 → ℕ) := (hcQ i).2
    exact floorCell_norm_lt (r : ℝ) (a : ℝ) hapos x (c i) (hpos_coord x (hSK0 hx.1))
      (hpos_coord (c i) (hSK0 (hcQ i).1)) (fun j => congrFun (h1.trans h2.symm) j)
  · calc T.card ≤ (Fintype.piFinset fun _ : Fin 3 => Finset.range n).card :=
          Finset.card_filter_le _ _
      _ = n ^ 3 := by
          rw [Fintype.card_piFinset]
          simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- C3-D4 arithmetic: resolutions above `⌈3/d⌉₊ + 1` have mesh `3/a ≤ d`. -/
theorem resolution_room (d : ℝ) (hd : 0 < d) (a : ℕ) (ha : ⌈3 / d⌉₊ + 1 ≤ a) :
    (1 : ℝ) ≤ a ∧ 3 / (a : ℝ) ≤ d := by
  have h2 : (⌈3 / d⌉₊ : ℝ) + 1 ≤ a := by exact_mod_cast ha
  have h1 : 3 / d ≤ (⌈3 / d⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : (0 : ℝ) ≤ (⌈3 / d⌉₊ : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ a := by linarith
  refine ⟨ha1, ?_⟩
  have hapos : (0 : ℝ) < a := by linarith
  have h3 : 3 / d < a := by linarith
  rw [div_lt_iff₀ hd] at h3
  rw [div_le_iff₀ hapos]
  linarith

/-- C3-D4 arithmetic: the cubic rank count. -/
theorem counted_rank_le (N' r a σ : ℕ) (hT : N' ≤ (2 * r * a) ^ 3) (x : ℕ) (hx : x ≤ N' * σ) :
    x ≤ 8 * r ^ 3 * σ * a ^ 3 := by
  have h1 : N' * σ ≤ (2 * r * a) ^ 3 * σ := Nat.mul_le_mul_right σ hT
  have h2 : (2 * r * a) ^ 3 * σ = 8 * r ^ 3 * σ * a ^ 3 := by ring
  exact hx.trans (h1.trans h2.le)

/-- C3-D4 arithmetic: the error rate `L(3/a)^(s+1)·a^s ≤ L·3^(s+1)` for `a ≥ 1`. -/
theorem counted_error_le (L : ℝ) (hL : 0 ≤ L) (a : ℕ) (ha1 : (1 : ℝ) ≤ a) (s : ℕ) (E : ℝ)
    (hE0 : 0 ≤ E) (hE : E ≤ L * (3 / (a : ℝ)) ^ (s + 1)) :
    E * (a : ℝ) ^ s ≤ L * 3 ^ (s + 1) := by
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha1
  have hid : (3 / (a : ℝ)) ^ (s + 1) * (a : ℝ) ^ s = 3 ^ (s + 1) / a := by
    rw [div_pow, pow_succ (a : ℝ) s, div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos (pow_pos hapos s) hapos).ne' hapos.ne']
    ring
  have hpow : (0 : ℝ) ≤ (a : ℝ) ^ s := pow_nonneg hapos.le s
  calc E * (a : ℝ) ^ s ≤ L * (3 / (a : ℝ)) ^ (s + 1) * (a : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hE hpow
    _ = L * (3 ^ (s + 1) / a) := by rw [mul_assoc, hid]
    _ ≤ L * 3 ^ (s + 1) :=
        mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg (by norm_num) _) ha1) hL

/-- The counted-grid construction factored through an arbitrary continuous linear map.
The concrete native Taylor theorem supplies `hP`; this is not a new endpoint premise. -/
theorem counted_approx_of_cell_taylor {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : E →L[ℝ] F) (S K0 : Set R3) (hS : MeasurableSet S)
    (hSK0 : S ⊆ K0) (hK0 : IsCompact K0) (d : ℝ) (hd : 0 < d) (s : ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ (N : ℕ) (Q : Fin N → Set R3) (c : Fin N → R3) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ cthickening d K0) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ cthickening d K0) →
      ∃ P : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
          N * ∑ k ∈ Finset.range (s + 1), 3 ^ k ∧
        ‖R - P‖ ≤ L * δ ^ (s + 1)) :
    ∃ (B : ℝ) (N A0 : ℕ), ∀ a : ℕ, A0 ≤ a →
      ∃ P : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * a ^ 3 ∧
        ‖R - P‖ * (a : ℝ) ^ s ≤ B := by
  classical
  obtain ⟨ρ0, hρ0⟩ := hK0.isBounded.subset_closedBall (0 : R3)
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, (r : ℝ) = (⌈ρ0⌉₊ : ℝ) + 1 := ⟨⌈ρ0⌉₊ + 1, by push_cast; rfl⟩
  have hr : ∀ x ∈ K0, ∀ j, |x j| < (r : ℝ) := by
    intro x hx j
    have h1 : ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
    have h2 : ‖x‖ ≤ ρ0 := mem_closedBall_zero_iff.mp (hρ0 hx)
    have h3 : ρ0 ≤ ⌈ρ0⌉₊ := Nat.le_ceil ρ0
    rw [Real.norm_eq_abs] at h1
    rw [hrdef]
    linarith
  refine ⟨L * 3 ^ (s + 1), 8 * r ^ 3 * ∑ k ∈ Finset.range (s + 1), 3 ^ k, ⌈3 / d⌉₊ + 1, ?_⟩
  intro a ha
  obtain ⟨ha1, h3d⟩ := resolution_room d hd a ha
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha1
  obtain ⟨N', Q, c, hQ, hdisj, hcover, hcS, hlt, hT⟩ :=
    exists_floor_grid S K0 hS hSK0 r hr a hapos
  have hgeom : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ 3 / (a : ℝ) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ cthickening d K0 := fun i x hx =>
    ball_cell_geom K0 d (3 / (a : ℝ)) h3d (c i) (hSK0 (hcS i)) x
      (by rw [mem_ball, dist_eq_norm]; exact hlt i x hx)
  obtain ⟨P, hPfin, hPrank, hPerr⟩ := hP N' Q c (3 / (a : ℝ)) (div_nonneg (by norm_num) hapos.le)
    hQ hdisj hcover (fun i => self_subset_cthickening K0 (hSK0 (hcS i))) hgeom
  exact ⟨P, hPfin, counted_rank_le N' r a _ hT _ hPrank,
    counted_error_le L hL a ha1 s _ (norm_nonneg _) hPerr⟩

/-- C3-D4: one constant `B`, rank coefficient `N` and threshold `A0`, chosen first; then at
every natural resolution `a ≥ A0` an actual cellwise Taylor operator on a Cartesian grid, with
an explicit finite-range witness, counted rank `≤ N·a³` and `‖R − P‖·a^s ≤ B`. -/
theorem harmonicRestrict_counted_approx (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : MeasurableSet S) (K0 : Set R3) (hK0 : IsCompact K0)
    (hSK0 : S ⊆ K0) (hK0D : K0 ⊆ D) (s : ℕ) :
    ∃ (B : ℝ) (N A0 : ℕ), ∀ a : ℕ, A0 ≤ a →
      ∃ P : harmonicSub D hD A hA →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict S),
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * a ^ 3 ∧
        ‖harmonicRestrict D hD A hA S (hSK0.trans hK0D) - P‖ * (a : ℝ) ^ s ≤ B := by
  obtain ⟨d, hd, hdD⟩ := hK0.exists_cthickening_subset_open hD hK0D
  obtain ⟨L, hL, hP⟩ := exists_cell_taylor_finite_rank D hD A hA hpos S hS (hSK0.trans hK0D)
    ((measure_mono hSK0).trans_lt hK0.measure_lt_top).ne (cthickening d K0) hK0.cthickening
    hdD s
  exact counted_approx_of_cell_taylor
    (harmonicRestrict D hD A hA S (hSK0.trans hK0D)) S K0 hS hSK0 hK0 d hd s L hL hP

/-- C3-D6c (actual): every positive power of the actual singular values of the native
restriction is summable, over the actual Sigma index type. -/
theorem harmonicRestrict_summable_rpow (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : MeasurableSet S) (K0 : Set R3) (hK0 : IsCompact K0)
    (hSK0 : S ⊆ K0) (hK0D : K0 ⊆ D)
    {ι : Type*} (w : ι → harmonicSub D hD A hA) (hw : Orthonormal ℝ w) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i) (hμR : ∀ i, μ i ≤ ‖harmonicRestrict D hD A hA S (hSK0.trans hK0D)‖)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w i))
        (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w j)) = if i = j then μ i ^ 2 else 0)
    (β : ℝ) (hβ : 0 < β) : Summable fun i => μ i ^ β := by
  set s : ℕ := ⌊3 / β⌋₊ + 1 with hsdef
  have hsβ : 3 < (s : ℝ) * β := by
    have h1 : 3 / β < (⌊3 / β⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (s : ℝ) = (⌊3 / β⌋₊ : ℝ) + 1 := by rw [hsdef]; push_cast; ring
    rw [h2]
    rw [div_lt_iff₀ hβ] at h1
    linarith
  obtain ⟨B, N, A0, happrox⟩ :=
    harmonicRestrict_counted_approx D hD A hA hpos S hS K0 hK0 hSK0 hK0D s
  exact summable_rpow_of_counted_approx _ w hw μ hμ
    (‖harmonicRestrict D hD A hA S (hSK0.trans hK0D)‖ + 1) (by positivity)
    (fun i => (hμR i).trans (le_add_of_nonneg_right zero_le_one)) hgram s B N A0 happrox β hβ hsβ

/-- Preserve one given spectral system while adjoining norm-one normalization
and summability. The native caller proves both supplied contracts. -/
theorem exists_summable_spectral_data_of_norm_le_one {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (hspec : ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ ‖R‖) ∧
      (∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i) ∧
      ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (hsum : ∀ {ι : Type} (w : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      (∀ i, 0 < μ i) → (∀ i, μ i ≤ ‖R‖) →
      (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) →
      ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
      (∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i) ∧
      (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
      ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β := by
  obtain ⟨ι, w, μ, hμ, hμR, heigen, hgram⟩ := hspec
  exact ⟨ι, w, μ, hμ, (fun i => (hμR i).trans hR), heigen, hgram,
    hsum w μ hμ hμR hgram⟩

/-- The SAME actual singular system has the manuscript normalization `0 < μ ≤ 1`
and every positive power summable. All witnesses come from the native restriction. -/
theorem harmonicRestrict_summable_spectral_data
    (D : Set R3) (hD : IsOpen D) (hconn : IsConnected D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : IsOpen S) (hSne : S.Nonempty) (K0 : Set R3) (hK0 : IsCompact K0)
    (hSK0 : S ⊆ K0) (hK0D : K0 ⊆ D) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D hD A hA)) (μ : ι → ℝ),
      (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
      (∀ i, (ContinuousLinearMap.adjoint (harmonicRestrict D hD A hA S (hSK0.trans hK0D)) ∘L
          harmonicRestrict D hD A hA S (hSK0.trans hK0D)) (w i) = μ i ^ 2 • w i) ∧
      (∀ i j, inner ℝ (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w i))
          (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w j)) =
        if i = j then μ i ^ 2 else 0) ∧
      ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β := by
  exact exists_summable_spectral_data_of_norm_le_one
    (harmonicRestrict D hD A hA S (hSK0.trans hK0D))
    (harmonicRestrict_norm_le_one D hD A hA S (hSK0.trans hK0D))
    (harmonicRestrict_spectral_data D hD hconn A hA hpos S hS hSne K0 hK0 hSK0 hK0D)
    (fun w μ hμ hμR hgram β hβ =>
      harmonicRestrict_summable_rpow D hD A hA hpos S hS.measurableSet K0 hK0 hSK0 hK0D
        w w.orthonormal μ hμ hμR hgram β hβ)

end C3Grid

/-! ### C3-D7a: the cross-series coefficient system of the actual singular data

Source: 03-product-continuation.tex, Lemma `cross:series`, (cross:singular-values),
(cross:coefficient-extension) and the summand bound. Geometry-free layers first; the actual layer
uses the proved power summability of the native restriction. Nothing is assumed. -/
section C3CrossCoefficients
open scoped ENNReal Matrix.Norms.Elementwise

/-- C3-D7a.1: the normalized images `μ_i⁻¹ R w_i` of a Gram system are orthonormal. -/
theorem orthonormal_normalized_image {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) :
    Orthonormal ℝ fun i => (μ i)⁻¹ • R (w i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [real_inner_smul_left, real_inner_smul_right, hgram]
  by_cases h : i = j
  · subst h
    have h0 : μ i ≠ 0 := (hμ i).ne'
    rw [if_pos rfl, if_pos rfl, ← mul_assoc, ← mul_inv, ← sq, inv_mul_cancel₀ (pow_ne_zero 2 h0)]
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- C3-D7a.2: Bessel for the slice coefficients against the normalized images. -/
theorem normalized_coeff_bessel {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) (G : F) :
    Summable (fun i => (inner ℝ ((μ i)⁻¹ • R (w i)) G) ^ 2) ∧
      ∑' i, (inner ℝ ((μ i)⁻¹ • R (w i)) G) ^ 2 ≤ ‖G‖ ^ 2 := by
  have hv := orthonormal_normalized_image R w μ hμ hgram
  have h1 := hv.inner_products_summable (x := G)
  have h2 := hv.tsum_inner_products_le (x := G)
  simp only [Real.norm_eq_abs, sq_abs] at h1 h2
  exact ⟨h1, h2⟩

/-- C3-D7a.2′: the extended coefficient `b_i = μ_i⁻² ⟪R w_i, G⟫` of
(cross:coefficient-extension) is bounded by `μ_i⁻¹ ‖G‖`. -/
theorem extended_coeff_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) (G : F) (i : ι) :
    |(μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G| ≤ (μ i)⁻¹ * ‖G‖ := by
  have hv := orthonormal_normalized_image R w μ hμ hgram
  have hn : ‖(μ i)⁻¹ • R (w i)‖ = 1 := hv.1 i
  have h1 : |inner ℝ ((μ i)⁻¹ • R (w i)) G| ≤ ‖G‖ := by
    calc |inner ℝ ((μ i)⁻¹ • R (w i)) G| ≤ ‖(μ i)⁻¹ • R (w i)‖ * ‖G‖ :=
          abs_real_inner_le_norm _ _
      _ = ‖G‖ := by rw [hn, one_mul]
  have hinv : 0 < (μ i)⁻¹ := inv_pos.mpr (hμ i)
  have heq : (μ i ^ 2)⁻¹ * inner ℝ (R (w i)) G =
      (μ i)⁻¹ * inner ℝ ((μ i)⁻¹ • R (w i)) G := by
    rw [real_inner_smul_left, ← mul_assoc, ← mul_inv, ← sq]
  rw [heq, abs_mul, abs_of_pos hinv]
  exact mul_le_mul_of_nonneg_left h1 hinv.le

/-- C3-D7a.3 (actual): any Banach-valued family dominated by a positive power of the ACTUAL
singular values of the native restriction is summable (the summand bound `CMμ^(γ₁+γ₂−1)`). -/
theorem harmonicRestrict_summable_of_norm_le_rpow (D : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A D) (hpos : ∀ x ∈ D, (A x).PosDef)
    (S : Set R3) (hS : MeasurableSet S) (K0 : Set R3) (hK0 : IsCompact K0)
    (hSK0 : S ⊆ K0) (hK0D : K0 ⊆ D)
    {ι : Type*} (w : ι → harmonicSub D hD A hA) (hw : Orthonormal ℝ w) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i) (hμR : ∀ i, μ i ≤ ‖harmonicRestrict D hD A hA S (hSK0.trans hK0D)‖)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w i))
        (harmonicRestrict D hD A hA S (hSK0.trans hK0D) (w j)) = if i = j then μ i ^ 2 else 0)
    {X : Type*} [NormedAddCommGroup X] [CompleteSpace X] (f : ι → X) (K γ : ℝ) (hγ : 0 < γ)
    (hf : ∀ i, ‖f i‖ ≤ K * μ i ^ γ) : Summable f :=
  ((harmonicRestrict_summable_rpow D hD A hA hpos S hS K0 hK0 hSK0 hK0D w hw μ hμ hμR hgram γ
    hγ).mul_left K).of_norm_bounded hf

end C3CrossCoefficients

/-! ### C3-D8: the actual coefficient `y`-smoothness and `y`-PDE

Source: 03-product-continuation.tex, (cross:coefficient-extension), "the integral solves
`L₂ b = 0`". Dominators are derived from the actual compact partial-jet bounds; the second
operator is passed under the integral through its explicit second-order expansion. -/
section C3CoefficientPDE
open MeasureTheory

/-- C3-D8a: second-order expansion of the native divergence-form operator. -/
theorem divCoeffGrad_expand (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (y : R3)
    (hA : ∀ i j, DifferentiableAt ℝ (fun z => A z i j) y)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) y) :
    divCoeffGrad A u y = ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z => A z i j) y (EuclideanSpace.single i 1) *
          fderiv ℝ u y (EuclideanSpace.single j 1) +
        A y i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)) := by
  unfold divCoeffGrad
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : ∀ j : Fin 3, DifferentiableAt ℝ
      (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) y :=
    fun j => hu.clm_apply (differentiableAt_const _)
  have hm : ∀ j : Fin 3, DifferentiableAt ℝ
      (fun z => A z i j * fderiv ℝ u z (EuclideanSpace.single j 1)) y :=
    fun j => (hA i j).fun_mul (hd j)
  have hsum := fderiv_fun_sum (u := Finset.univ) (fun j _ => hm j)
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (hA i j) (hd j), fderiv_clm_apply hu (differentiableAt_const _)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add]
  ring

/-- C3-D8b: the native divergence operator passes under a weighted parameter integral,
given the two derivative identities and integrability of the scalar integrands. -/
theorem divCoeffGrad_integral {α : Type*} [MeasurableSpace α] (m : Measure α)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (y : R3)
    (hA : ∀ i j, DifferentiableAt ℝ (fun z => A z i j) y)
    (T : R3 → ℝ) (H : α → R3 → ℝ) (q : α → ℝ)
    (hT : DifferentiableAt ℝ (fderiv ℝ T) y)
    (hH : ∀ᵐ x ∂m, DifferentiableAt ℝ (fderiv ℝ (H x)) y)
    (h1 : ∀ v, fderiv ℝ T y v = ∫ x, q x * fderiv ℝ (H x) y v ∂m)
    (h2 : ∀ v w, fderiv ℝ (fderiv ℝ T) y v w =
      ∫ x, q x * fderiv ℝ (fderiv ℝ (H x)) y v w ∂m)
    (hi1 : ∀ v, Integrable (fun x => q x * fderiv ℝ (H x) y v) m)
    (hi2 : ∀ v w, Integrable (fun x => q x * fderiv ℝ (fderiv ℝ (H x)) y v w) m) :
    divCoeffGrad A T y = ∫ x, q x * divCoeffGrad A (H x) y ∂m := by
  have hterm : ∀ i j : Fin 3, Integrable (fun x =>
      fderiv ℝ (fun z => A z i j) y (EuclideanSpace.single i 1) *
          (q x * fderiv ℝ (H x) y (EuclideanSpace.single j 1)) +
        A y i j * (q x * fderiv ℝ (fderiv ℝ (H x)) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1))) m :=
    fun i j => ((hi1 _).const_mul _).add ((hi2 _ _).const_mul _)
  have hR : (fun x => q x * divCoeffGrad A (H x) y) =ᵐ[m] fun x => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z => A z i j) y (EuclideanSpace.single i 1) *
          (q x * fderiv ℝ (H x) y (EuclideanSpace.single j 1)) +
        A y i j * (q x * fderiv ℝ (fderiv ℝ (H x)) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1))) := by
    filter_upwards [hH] with x hx
    rw [divCoeffGrad_expand A (H x) y hA hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [integral_congr_ae hR, divCoeffGrad_expand A T y hA hT,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hterm i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add ((hi1 _).const_mul _) ((hi2 _ _).const_mul _), integral_const_mul,
    integral_const_mul, h1, h2]

/-- C3-D8c: derived all-order dominators for the ACTUAL initial kernel on a compact product
room, and the resulting smooth parameter integral with its first/second derivative formulas. -/
theorem initialKernel_rowIntegral_data (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ initialCross S lam)
    (q : R3 → ℝ) (hq : MemLp q 2 ((volume : Measure R3).restrict U)) :
    ContDiffOn ℝ ∞ (fun y => ∫ x, initialKernel S lam (x,y) * q x
        ∂((volume : Measure R3).restrict U)) V ∧
    (∀ y ∈ V, ∀ v : R3, fderiv ℝ (fun y => ∫ x, initialKernel S lam (x,y) * q x
        ∂((volume : Measure R3).restrict U)) y v =
      ∫ x, q x * fderiv ℝ (fun y => initialKernel S lam (x,y)) y v
        ∂((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v w : R3, fderiv ℝ (fderiv ℝ (fun y => ∫ x, initialKernel S lam (x,y) * q x
        ∂((volume : Measure R3).restrict U))) y v w =
      ∫ x, q x * fderiv ℝ (fderiv ℝ (fun y => initialKernel S lam (x,y))) y v w
        ∂((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v : R3, Integrable (fun x =>
      q x * fderiv ℝ (fun y => initialKernel S lam (x,y)) y v)
        ((volume : Measure R3).restrict U)) ∧
    (∀ y ∈ V, ∀ v w : R3, Integrable (fun x =>
      q x * fderiv ℝ (fderiv ℝ (fun y => initialKernel S lam (x,y))) y v w)
        ((volume : Measure R3).restrict U)) := by
  set m : Measure R3 := (volume : Measure R3).restrict U with hm
  set F := initialKernel S lam with hFdef
  have hΩ := Geometry.initialCross_isOpen S lam
  have hF := Geometry.initialKernel_contDiffOn S lam hlam
  haveI : IsFiniteMeasure m :=
    isFiniteMeasure_restrict.mpr ((measure_mono hUK).trans_lt hK.measure_lt_top).ne
  have hq1 : Integrable q m := hq.integrable (by norm_num)
  choose B _hB0 hB using fun n : ℕ =>
    exists_bound_partialSecondJet n F (initialCross S lam) hΩ hF K J hK hJ hcross
  have hmem : ∀ x ∈ U, ∀ y ∈ V, (x,y) ∈ initialCross S lam :=
    fun x hx y hy => hcross ⟨hUK hx, hVJ hy⟩
  have hRow : ∀ᵐ x ∂m, ContDiffOn ℝ ∞ (fun y => F (x,y)) V := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hmem x hx y hy)
  have hmeas : ∀ n : ℕ, ∀ y ∈ V, AEStronglyMeasurable
      (fun x => q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y) m := by
    intro n y hy
    have hc : ContinuousOn (fun x => partialSecondJet n F (x,y)) U :=
      (continuousOn_partialSecondJet n F _ hΩ hF).comp
        (continuousOn_id.prodMk continuousOn_const) (fun x hx => hmem x hx y hy)
    exact hq.aestronglyMeasurable.smul (hc.aestronglyMeasurable hU.measurableSet)
  have hBound : ∀ n : ℕ, ∀ᵐ x ∂m, ∀ y ∈ V,
      ‖q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y‖ ≤ B n * |q x| := by
    intro n
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx y hy
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB n x (hUK hx) y (hVJ hy)) (abs_nonneg _)
  have hbInt : ∀ n : ℕ, Integrable (fun x => B n * |q x|) m :=
    fun n => hq1.abs.const_mul (B n)
  have hInt : ∀ (n : ℕ) (y : R3), y ∈ V →
      Integrable (fun x => q x • iteratedFDeriv ℝ n (fun y => F (x,y)) y) m := by
    intro n y hy
    refine Integrable.mono' (hbInt n) (hmeas n y hy) ?_
    filter_upwards [hBound n] with x hx using hx y hy
  have hmain := ExteriorSource.contDiffOn_integral_and_fderiv_of_dominated_iteratedFDeriv
    m V hV (fun x y => F (x,y)) q hRow hInt (fun n x => B n * |q x|) hbInt hBound
  obtain ⟨hs, hd1, hd2⟩ := hmain
  refine ⟨hs, hd1, hd2, ?_, ?_⟩
  · intro y hy v
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => R3) ℝ
      (fun _ => v)).integrable_comp (hInt 1 y hy)
    refine h.congr (Eventually.of_forall fun x => ?_)
    change (q x • iteratedFDeriv ℝ 1 (fun y => F (x,y)) y) (fun _ => v) = _
    rw [ContinuousMultilinearMap.smul_apply, iteratedFDeriv_one_apply, smul_eq_mul]
  · intro y hy v w
    have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => R3) ℝ
      ![v, w]).integrable_comp (hInt 2 y hy)
    refine h.congr (Eventually.of_forall fun x => ?_)
    change (q x • iteratedFDeriv ℝ 2 (fun y => F (x,y)) y) ![v, w] = _
    rw [ContinuousMultilinearMap.smul_apply, iteratedFDeriv_two_apply, smul_eq_mul]
    rfl

/-- The SAME second principal coefficient as the native normalized second operator. -/
theorem contDiff_dilatedSecondPrincipal (S : KnownSideSourceData) (lam : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i j) :=
  (contDiff_principalCoefficient_entry S.g2 S.g2_admissible i j).comp
    (contDiff_id.const_smul lam)

/-- C3-D8d: the actual parameter integral of the initial kernel solves the literal native
normalized second equation on the whole open `y`-room. -/
theorem initialKernel_rowIntegral_secondPDE (S : KnownSideSourceData) (L lam : ℝ)
    (hlam : 0 < lam)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ initialCross S lam)
    (q : R3 → ℝ) (hq : MemLp q 2 ((volume : Measure R3).restrict U)) :
    ContDiffOn ℝ ∞ (fun y => ∫ x, initialKernel S lam (x,y) * q x
        ∂((volume : Measure R3).restrict U)) V ∧
    ∀ y ∈ V, normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => ∫ x,
      initialKernel S lam (x,y) * q x ∂((volume : Measure R3).restrict U)) y = 0 := by
  obtain ⟨hs, hd1, hd2, hi1, hi2⟩ :=
    initialKernel_rowIntegral_data S lam hlam U V K J hU hV hK hJ hUK hVJ hcross q hq
  refine ⟨hs, fun y hy => ?_⟩
  have hA : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun z => principalCoefficient (dilatedMetric S.g2 lam) z i j) y :=
    fun i j => (contDiff_dilatedSecondPrincipal S lam i j).differentiable (by simp) y
  have hT : DifferentiableAt ℝ (fderiv ℝ (fun y => ∫ x, initialKernel S lam (x,y) * q x
      ∂((volume : Measure R3).restrict U))) y :=
    ((hs.contDiffAt (hV.mem_nhds hy)).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hH : ∀ᵐ x ∂((volume : Measure R3).restrict U),
      DifferentiableAt ℝ (fderiv ℝ (fun y => initialKernel S lam (x,y))) y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hrow : ContDiffOn ℝ ∞ (fun y => initialKernel S lam (x,y)) V :=
      (Geometry.initialKernel_contDiffOn S lam hlam).comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => hcross ⟨hUK hx, hVJ hy⟩)
    exact ((hrow.contDiffAt (hV.mem_nhds hy)).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hzero : ∀ᵐ x ∂((volume : Measure R3).restrict U),
      normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => initialKernel S lam (x,y)) y = 0 := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (Geometry.initial_cross_product S L lam hlam).2.1.2.2 (x,y)
      (hcross ⟨hUK hx, hVJ hy⟩)
  have hI := divCoeffGrad_integral ((volume : Measure R3).restrict U)
    (principalCoefficient (dilatedMetric S.g2 lam)) y hA _
    (fun x y => initialKernel S lam (x,y)) q hT hH (hd1 y hy) (hd2 y hy) (hi1 y hy) (hi2 y hy)
  rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad,
    hI, ← integral_const_mul]
  have hz : (fun x => normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,y) *
      (vol (dilatedMetric S.g2 lam) y)⁻¹ *
      (q x * divCoeffGrad (principalCoefficient (dilatedMetric S.g2 lam))
        (fun y => initialKernel S lam (x,y)) y)) =ᵐ[(volume : Measure R3).restrict U]
      fun _ => (0 : ℝ) := by
    filter_upwards [hzero] with x hx
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv,
      coordinateFluxDivergence_eq_divCoeffGrad] at hx
    calc _ = q x * (normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,y) *
          (vol (dilatedMetric S.g2 lam) y)⁻¹ *
          divCoeffGrad (principalCoefficient (dilatedMetric S.g2 lam))
            (fun y => initialKernel S lam (x,y)) y) := by ring
      _ = 0 := by rw [hx, mul_zero]
  rw [integral_congr_ae hz, integral_zero]

/-- C3-D8e: the ACTUAL extended coefficient `bᵢ(y) = μᵢ⁻² ∫_U F(x,y) (R wᵢ)(x) dx`
of (cross:coefficient-extension), with any L2 weight on `U` (in the caller, the SAME native
restricted singular vector). -/
def initialCoefficient (S : KnownSideSourceData) (lam : ℝ) (U : Set R3) (μi : ℝ)
    (q : R3 → ℝ) (y : R3) : ℝ :=
  (μi ^ 2)⁻¹ * ∫ x, initialKernel S lam (x,y) * q x ∂((volume : Measure R3).restrict U)

theorem initialCoefficient_secondPDE (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ initialCross S lam)
    (μi : ℝ) (q : R3 → ℝ) (hq : MemLp q 2 ((volume : Measure R3).restrict U)) :
    ContDiffOn ℝ ∞ (initialCoefficient S lam U μi q) V ∧
    ∀ y ∈ V, normalizedSecondLaplacian S.g1 S.g2 L lam
      (initialCoefficient S lam U μi q) y = 0 := by
  have heq : initialCoefficient S lam U μi q = fun y => ∫ x, initialKernel S lam (x,y) *
      ((μi ^ 2)⁻¹ * q x) ∂((volume : Measure R3).restrict U) := by
    funext y
    rw [initialCoefficient, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [heq]
  exact initialKernel_rowIntegral_secondPDE S L lam hlam U V K J hU hV hK hJ hUK hVJ hcross
    _ (hq.const_mul _)

end C3CoefficientPDE

/-! ### C3-D9: the actual finite cross sums are literal product solutions

Source: 03-product-continuation.tex, Lemma `cross:series`, the partial sums of
`F(x,y) = ∑ⱼ wⱼ(x) bⱼ(y)`. The `x`-factors are the SAME native smooth representatives of the
SAME singular basis; the `y`-factors are the C3-D8 coefficients. No convergence is claimed. -/
section C3CrossPartialSums
open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- C3-D9a: finite linear combinations commute with the native divergence operator. -/
theorem divCoeffGrad_finset_sum {ι : Type*} (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (x : R3)
    (hA : DifferentiableAt ℝ A x) (s : Finset ι) (c : ι → ℝ) (u : ι → R3 → ℝ)
    (hu : ∀ i ∈ s, ContDiffAt ℝ 2 (u i) x) :
    divCoeffGrad A (fun t => ∑ i ∈ s, c i * u i t) x =
      ∑ i ∈ s, c i * divCoeffGrad A (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [divCoeffGrad]
  | @insert i s hi ih =>
    have hui : ContDiffAt ℝ 2 (u i) x := hu i (Finset.mem_insert_self i s)
    have hus : ∀ j ∈ s, ContDiffAt ℝ 2 (u j) x :=
      fun j hj => hu j (Finset.mem_insert_of_mem hj)
    have hFs : ContDiffAt ℝ 2 (fun t => ∑ j ∈ s, c j * u j t) x :=
      ContDiffAt.sum fun j hj => contDiffAt_const.mul (hus j hj)
    simp only [Finset.sum_insert hi]
    change divCoeffGrad A ((c i) • u i + (fun t => ∑ j ∈ s, c j * u j t)) x = _
    rw [Regularity.Jets.divCoeffGrad_add (u := (c i) • u i)
        (v := fun t => ∑ j ∈ s, c j * u j t) hA (hui.const_smul (c i)) hFs,
      Regularity.Jets.divCoeffGrad_smul (c i) hA hui, ih hus]

theorem contDiff_dilatedSecondPrincipalMatrix (S : KnownSideSourceData) (lam : ℝ) :
    ContDiff ℝ ∞ (principalCoefficient (dilatedMetric S.g2 lam)) := by
  change ContDiff ℝ ∞ (fun x => principalCoefficient S.g2 (lam • x))
  exact (contDiff_principalCoefficient S.g2 S.g2_admissible).comp
    (lam • ContinuousLinearMap.id ℝ R3).contDiff

/-- C3-D9b: a finite cross sum `∑ Wᵢ(x) bᵢ(y)` with first-equation `x`-factors on `D` and
literal-second-equation `y`-factors on `V` is a literal product solution on `D ×ˢ V`. -/
theorem crossSum_productSolution (S : KnownSideSourceData) (L lam : ℝ)
    {ι : Type*} (s : Finset ι) (W b : ι → R3 → ℝ) (D V : Set R3)
    (hD : IsOpen D) (hV : IsOpen V)
    (hW : ∀ i, ContDiffOn ℝ ∞ (W i) D)
    (hWP : ∀ i, ∀ x ∈ D, divCoeffGrad (dilatedFirstPrincipal S lam) (W i) x = 0)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) V)
    (hbP : ∀ i, ∀ y ∈ V, normalizedSecondLaplacian S.g1 S.g2 L lam (b i) y = 0) :
    ProductSolutionOn S L lam (fun v => ∑ i ∈ s, W i v.1 * b i v.2) (D ×ˢ V) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ContDiffOn.sum fun i _ =>
      ((hW i).comp contDiffOn_fst fun v hv => hv.1).mul
        ((hb i).comp contDiffOn_snd fun v hv => hv.2)
  · rintro v ⟨hx, -⟩
    show coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x))
      (fun x => ∑ i ∈ s, W i x * b i v.2)) v.1 = 0
    have hA1 : DifferentiableAt ℝ (principalCoefficient (fun x => S.g1 (lam • x))) v.1 :=
      (contDiff_dilatedFirstPrincipal S lam).differentiable (by simp) v.1
    have hfun : (fun x => ∑ i ∈ s, W i x * b i v.2) = fun x => ∑ i ∈ s, b i v.2 * W i x := by
      funext x
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [coordinateFluxDivergence_eq_divCoeffGrad, hfun,
      divCoeffGrad_finset_sum _ _ hA1 s (fun i => b i v.2) W
        (fun i _ => ((hW i).contDiffAt (hD.mem_nhds hx)).of_le (by simp))]
    exact Finset.sum_eq_zero fun i _ => by
      have h := hWP i v.1 hx
      rw [dilatedFirstPrincipal] at h
      rw [h, mul_zero]
  · rintro v ⟨-, hy⟩
    show normalizedSecondLaplacian S.g1 S.g2 L lam (fun y => ∑ i ∈ s, W i v.1 * b i y) v.2 = 0
    have hA2 : DifferentiableAt ℝ (principalCoefficient (dilatedMetric S.g2 lam)) v.2 :=
      (contDiff_dilatedSecondPrincipalMatrix S lam).differentiable (by simp) v.2
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv, coordinateFluxDivergence_eq_divCoeffGrad,
      divCoeffGrad_finset_sum _ _ hA2 s (fun i => W i v.1) b
        (fun i _ => ((hb i).contDiffAt (hV.mem_nhds hy)).of_le (by simp)), Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h := hbP i v.2 hy
    rw [Geometry.normalizedSecondLaplacian_eq_mul_fluxDiv,
      coordinateFluxDivergence_eq_divCoeffGrad] at h
    calc _ = W i v.1 * (normalizedSecondLaplacianScalarJoint S.g1 S.g2 L (lam,v.2) *
          (vol (dilatedMetric S.g2 lam) v.2)⁻¹ *
          divCoeffGrad (principalCoefficient (dilatedMetric S.g2 lam)) (b i) v.2) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- C3-D9c (actual): the partial sums of the cross series built from the SAME native harmonic
singular vectors `wᵢ` (smooth representatives on `D`) and their ACTUAL extended coefficients
`bᵢ(y) = μᵢ⁻² ∫_U F(x,y) (R wᵢ)(x) dx` are literal product solutions on `D ×ˢ V`. -/
theorem actualCrossPartialSum_productSolution (S : KnownSideSourceData) (L lam : ℝ)
    (hlam : 0 < lam) (D : Set R3) (hD : IsOpen D)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J) (hUD : U ⊆ D)
    (hcross : K ×ˢ J ⊆ initialCross S lam) {ι : Type*}
    (w : ι → harmonicSub D hD (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)
    (μ : ι → ℝ) (s : Finset ι) :
    ProductSolutionOn S L lam (fun v => ∑ i ∈ s,
      harmonicRep D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn
        (fun x _ => principalCoefficient_posDef S.g1 S.g1_admissible (lam • x)) (w i) v.1 *
      initialCoefficient S lam U (μ i)
        (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn U hUD (w i)) v.2) (D ×ˢ V) := by
  refine crossSum_productSolution S L lam s _ _ D V hD hV
    (fun i => (harmonicRep_spec D hD _ _ _ (w i)).1)
    (fun i => (harmonicRep_spec D hD _ _ _ (w i)).2.2)
    (fun i => (initialCoefficient_secondPDE S L lam hlam U V K J hU hV hK hJ hUK hVJ hcross
      (μ i) _ (Lp.memLp _)).1)
    (fun i => (initialCoefficient_secondPDE S L lam hlam U V K J hU hV hK hJ hUK hVJ hcross
      (μ i) _ (Lp.memLp _)).2)

end C3CrossPartialSums

/-! ### C3-D10/D11: the L2 tensor summands of the cross series

Source: 03-product-continuation.tex, Lemma `cross:series`: "the series converges absolutely in
`L²(O₁×O₂)`: its summands are bounded by `CMμⱼ^(γ₁+γ₂−1)`". D10 is the exact product-norm
identity `‖w ⊗ b‖ = ‖w‖‖b‖`. D11 is only the CONSUMER of the C4 interpolation output bounds,
which remain OPEN; it is not used as a premise of the endpoint. -/
section C3CrossTensor
open MeasureTheory

/-- The square integral of a real L2 class is its squared norm. -/
theorem integral_sq_eq_norm_sq {α : Type*} [MeasurableSpace α] {m : Measure α}
    (u : Lp ℝ 2 m) : ∫ x, (u x) ^ 2 ∂m = ‖u‖ ^ 2 := by
  calc ∫ x, (u x) ^ 2 ∂m = ∫ x, inner ℝ (u x) (u x) ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs, sq_abs] using
          (real_inner_self_eq_norm_sq (u q)).symm)
    _ = inner ℝ u u := (L2.inner_def u u).symm
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

/-- C3-D10a: the product of two real L2 classes is L2 on the product measure. -/
theorem tensor_memLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (m.prod n) := by
  have hf2 : Integrable (fun x => (f x) ^ 2) m := (Lp.memLp f).integrable_sq
  have hg2 : Integrable (fun y => (g y) ^ 2) n := (Lp.memLp g).integrable_sq
  have hmeas : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2) (m.prod n) :=
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
      ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  have hsq : (fun z : α × β => (f z.1 * g z.2) ^ 2) = fun z => (f z.1) ^ 2 * (g z.2) ^ 2 := by
    funext z
    ring
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  rw [hsq]
  exact hf2.mul_prod hg2

/-- C3-D10b: the actual tensor class `f ⊗ g ∈ L²(m × n)`. -/
def tensorLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    Lp ℝ 2 (m.prod n) :=
  (tensor_memLp f g).toLp _

theorem tensorLp_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    (tensorLp f g : α × β → ℝ) =ᵐ[m.prod n] fun z => f z.1 * g z.2 :=
  (tensor_memLp f g).coeFn_toLp

/-- C3-D10c: the exact product-norm identity `‖f ⊗ g‖ = ‖f‖ ‖g‖` (Fubini–Tonelli). -/
theorem norm_tensorLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    ‖tensorLp f g‖ = ‖f‖ * ‖g‖ := by
  have h2 : ∫ z, ((tensorLp f g : Lp ℝ 2 (m.prod n)) z) ^ 2 ∂(m.prod n) =
      ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
    calc ∫ z, ((tensorLp f g : Lp ℝ 2 (m.prod n)) z) ^ 2 ∂(m.prod n)
          = ∫ z, (f z.1) ^ 2 * (g z.2) ^ 2 ∂(m.prod n) := by
            apply integral_congr_ae
            filter_upwards [tensorLp_ae f g] with z hz
            rw [hz]
            ring
      _ = (∫ x, (f x) ^ 2 ∂m) * ∫ y, (g y) ^ 2 ∂n := by
            exact integral_prod_mul (L := ℝ) (fun x => (f x) ^ 2) (fun y => (g y) ^ 2)
      _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by rw [integral_sq_eq_norm_sq, integral_sq_eq_norm_sq]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, ← h2, integral_sq_eq_norm_sq]

/-- C3-D11 (consumer of the OPEN C4 output): if the SAME singular values satisfy the
interpolation-output bounds `‖fᵢ‖ ≤ C μᵢ^γ₁` and `‖gᵢ‖ ≤ C' μᵢ^(γ₂−1)`, then the tensor
summands are summable in `L²` whenever `∑ μᵢ^(γ₁+γ₂−1)` converges (as it does for the actual
native restriction, `harmonicRestrict_summable_rpow`, once `γ₁+γ₂>1`). -/
theorem tensor_summable_of_rpow_bounds {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (C C' γ₁ γ₂ : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * μ i ^ γ₁) (hg : ∀ i, ‖g i‖ ≤ C' * μ i ^ (γ₂ - 1))
    (hsum : Summable fun i => μ i ^ (γ₁ + γ₂ - 1)) :
    Summable fun i => tensorLp (f i) (g i) := by
  refine (hsum.mul_left (C * C')).of_norm_bounded fun i => ?_
  rw [norm_tensorLp]
  have hpow : μ i ^ (γ₁ + γ₂ - 1) = μ i ^ γ₁ * μ i ^ (γ₂ - 1) := by
    rw [← Real.rpow_add (hμ i)]
    ring_nf
  calc ‖f i‖ * ‖g i‖ ≤ (C * μ i ^ γ₁) * (C' * μ i ^ (γ₂ - 1)) :=
        mul_le_mul (hf i) (hg i) (norm_nonneg _)
          (mul_nonneg hC (Real.rpow_nonneg (hμ i).le _))
    _ = C * C' * μ i ^ (γ₁ + γ₂ - 1) := by rw [hpow]; ring

/-- C3-D10d: a finite sum of tensor classes is a.e. the pointwise finite cross sum, the form
consumed by the native finite-product L2 limit theorem (gap G3). -/
theorem tensorLp_finset_sum_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) :
    ((∑ i ∈ s, tensorLp (f i) (g i) : Lp ℝ 2 (m.prod n)) : α × β → ℝ) =ᵐ[m.prod n]
      fun z => ∑ i ∈ s, f i z.1 * g i z.2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := m.prod n)] with z hz
    rw [hz, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (tensorLp (f i) (g i)) (∑ j ∈ s, tensorLp (f j) (g j)),
      tensorLp_ae (f i) (g i), ih] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]

/-- C3-D10e: an arbitrary-index `HasSum` yields a genuine Nat-indexed sequence of actual finite
partial sums converging to the same limit (no enumeration of the index type is imposed). -/
theorem exists_finset_seq_tendsto_of_hasSum {ι E : Type*} [NormedAddCommGroup E]
    (v : ι → E) (S : E) (h : HasSum v S) :
    ∃ s : ℕ → Finset ι, Tendsto (fun k => ∑ i ∈ s k, v i) atTop (𝓝 S) := by
  have hk : ∀ k : ℕ, ∃ t : Finset ι, dist (∑ i ∈ t, v i) S < 1 / ((k : ℝ) + 1) := fun k =>
    (Filter.Tendsto.eventually h (Metric.ball_mem_nhds S (by positivity))).exists
  choose s hs using hk
  refine ⟨s, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun k => dist_nonneg) (fun k => (hs k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end C3CrossTensor

/-!
## C4 (G1) closed sub-steps: exponential balancing and the strict exponent

Source: 03-product-continuation.tex, Prop. `cross:criterion`, paragraph "Placing the cross and
obtaining interpolation", display (cross:exponent) and the sentence "Values of the balancing
parameter below tau_0 are covered by increasing the constant". These are steps (d) and (e) of
G1 in REPORT.md. The weighted three-level Carleman inequality (steps (a)-(c)) is NOT proved
here; `strictHeight_interpolation_of_weighted` only consumes it, and is not G1 itself.
-/
section C4Balancing

/-- The source concave height profile `phi(s) = s - kappa s^2`. -/
def strictHeight (κ s : ℝ) : ℝ := s - κ * s ^ 2

/-- G1(d): exponential balancing. If `A <= D` and for every `tau >= tau0`
`A <= C (exp(-a tau) D + exp(b tau) S)`, then
`A <= (2C + exp(a tau0)) S^(a/(a+b)) D^(b/(a+b))`. All cases `S = 0`, `D = 0` included. -/
theorem exp_balance {a b C τ0 A S D : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → A ≤ C * (Real.exp (-(a * τ)) * D + Real.exp (b * τ) * S)) :
    A ≤ (2 * C + Real.exp (a * τ0)) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
  have hab : 0 < a + b := add_pos ha hb
  have hD : 0 ≤ D := hA.trans hAD
  have hK : 0 ≤ 2 * C + Real.exp (a * τ0) := by positivity
  have hRHS : 0 ≤ (2 * C + Real.exp (a * τ0)) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
    positivity
  rcases hD.eq_or_lt with hD0 | hDpos
  · subst hD0
    linarith
  rcases hS.eq_or_lt with hS0 | hSpos
  · subst hS0
    have hlim : Tendsto (fun τ : ℝ => C * (Real.exp (-(a * τ)) * D + Real.exp (b * τ) * 0))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun τ : ℝ => Real.exp (-(a * τ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (Filter.Tendsto.const_mul_atTop ha tendsto_id)
      have h2 := (h1.mul_const D).const_mul C
      simpa using h2
    have hA0 : A ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨τ0, h⟩)
    linarith
  -- both positive
  have hSne : S ≠ 0 := hSpos.ne'
  have hDne : D ≠ 0 := hDpos.ne'
  have hX : S ^ (a / (a + b)) * D ^ (b / (a + b)) =
      Real.exp (Real.log S * (a / (a + b)) + Real.log D * (b / (a + b))) := by
    rw [Real.rpow_def_of_pos hSpos, Real.rpow_def_of_pos hDpos, ← Real.exp_add]
  have hXpos : 0 ≤ S ^ (a / (a + b)) * D ^ (b / (a + b)) := by positivity
  set t : ℝ := Real.log (D / S) / (a + b) with ht_def
  have hlogDS : Real.log (D / S) = Real.log D - Real.log S := Real.log_div hDne hSne
  by_cases ht : τ0 ≤ t
  · have h1 := h t ht
    have e1 : Real.exp (-(a * t)) * D = S ^ (a / (a + b)) * D ^ (b / (a + b)) := by
      rw [hX, ← Real.exp_log hDpos, ← Real.exp_add, Real.log_exp]
      congr 1
      rw [ht_def, hlogDS]
      field_simp
      ring
    have e2 : Real.exp (b * t) * S = S ^ (a / (a + b)) * D ^ (b / (a + b)) := by
      rw [hX]
      conv_lhs => rw [← Real.exp_log hSpos]
      rw [← Real.exp_add]
      congr 1
      rw [ht_def, hlogDS]
      field_simp
      ring
    rw [e1, e2] at h1
    have hexp : 0 ≤ Real.exp (a * τ0) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
      positivity
    nlinarith
  · push_neg at ht
    -- below the threshold: `D < exp((a+b) tau0) S`
    have hlt : Real.log D < (a + b) * τ0 + Real.log S := by
      have : Real.log (D / S) < (a + b) * τ0 := by
        rw [ht_def] at ht
        have := (div_lt_iff₀ hab).1 ht
        linarith
      linarith
    have hDexp : D = Real.exp (Real.log D * (a / (a + b)) + Real.log D * (b / (a + b))) := by
      rw [← mul_add, ← add_div, div_self hab.ne', mul_one, Real.exp_log hDpos]
    have hga : 0 < a / (a + b) := div_pos ha hab
    have hle : D ≤ Real.exp (a * τ0) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
      rw [hX, ← Real.exp_add]
      conv_lhs => rw [hDexp]
      apply Real.exp_le_exp.2
      have h3 : Real.log D * (a / (a + b)) ≤ ((a + b) * τ0 + Real.log S) * (a / (a + b)) :=
        mul_le_mul_of_nonneg_right hlt.le hga.le
      have h4 : ((a + b) * τ0 + Real.log S) * (a / (a + b)) =
          a * τ0 + Real.log S * (a / (a + b)) := by
        field_simp
      linarith
    have h2C : 0 ≤ 2 * C * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by positivity
    nlinarith

/-- G1(e): positivity of the bottom gap and the denominator for the source levels
`-l+3e < -e < l+3e`, under the source smallness `kappa l <= 1/4`, `4e < kappa l^2`. -/
theorem strictHeight_gaps {κ l e : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) :
    κ * e < 1 / 64 ∧
    strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e) = 2 * l * (1 - 6 * (κ * e)) ∧
    2 * (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) -
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) =
      2 * κ * l ^ 2 - 8 * e + 16 * κ * e ^ 2 ∧
    (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) -
        (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) =
      l - κ * l * l - 6 * (l * (κ * e)) - 8 * (e * (κ * e)) + 4 * e := by
  have hκl0 : 0 < κ * l := mul_pos hκ hl
  have hsq : κ * l * (κ * l) ≤ κ * l * (1 / 4) := mul_le_mul_of_nonneg_left hκl hκl0.le
  have h4 : κ * (4 * e) < κ * (κ * l ^ 2) := mul_lt_mul_of_pos_left he4 hκ
  refine ⟨by nlinarith, ?_, ?_, ?_⟩ <;> · unfold strictHeight; ring

/-- G1(e): the source exponent (cross:exponent) lies strictly between `1/2` and `1`. -/
theorem strictExponent_bounds {κ l e : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) :
    0 < strictHeight κ (-e) - strictHeight κ (-l + 3 * e) ∧
    0 < strictHeight κ (l + 3 * e) - strictHeight κ (-e) ∧
    1 / 2 < (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) ∧
    (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) < 1 := by
  obtain ⟨h1, hDn, h2N, hDN⟩ := strictHeight_gaps hκ hl hκl he he4
  have hl1 : κ * l * l ≤ 1 / 4 * l := mul_le_mul_of_nonneg_right hκl hl.le
  have hl2 : l * (κ * e) < l * (1 / 64) := mul_lt_mul_of_pos_left h1 hl
  have hl3 : e * (κ * e) ≤ e * (1 / 64) := mul_le_mul_of_nonneg_left h1.le he
  have hDpos : 0 < strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e) := by
    rw [hDn]; nlinarith
  have hkee : 0 ≤ κ * e ^ 2 := by positivity
  have hgap : 0 < l - κ * l * l - 6 * (l * (κ * e)) - 8 * (e * (κ * e)) + 4 * e := by
    nlinarith
  have hN : 0 < strictHeight κ (-e) - strictHeight κ (-l + 3 * e) := by nlinarith
  refine ⟨hN, ?_, ?_, ?_⟩
  · have : strictHeight κ (l + 3 * e) - strictHeight κ (-e) =
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) -
          (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) := by ring
    rw [this, hDN]; exact hgap
  · rw [lt_div_iff₀ hDpos]; nlinarith
  · rw [div_lt_one hDpos]; nlinarith

/-- G1(e): at `e = 0` the exponent is exactly `1/2 + kappa l / 2` (the source remark). -/
theorem strictExponent_at_zero {κ l : ℝ} (hl : 0 < l) :
    (strictHeight κ (-0) - strictHeight κ (-l + 3 * 0)) /
        (strictHeight κ (l + 3 * 0) - strictHeight κ (-l + 3 * 0)) = 1 / 2 + κ * l / 2 := by
  unfold strictHeight
  have : (l + 3 * 0 - κ * (l + 3 * 0) ^ 2 - (-l + 3 * 0 - κ * (-l + 3 * 0) ^ 2)) = 2 * l := by
    ring
  rw [this]
  field_simp
  ring

/-- G1(d)+(e) consumer: from the three-level weighted inequality produced by steps (a)-(c)
(NOT proved here) at heights `phi(-e)`, `phi(-l+3e)`, `phi(l+3e)`, together with `A <= D`, the
interpolation `A <= C' S^g D^(1-g)` holds with the source exponent `g` of (cross:exponent),
`1/2 < g < 1`. This is a consumer of the Carleman input, not a proof of G1. -/
theorem strictHeight_interpolation_of_weighted {κ l e C τ0 A S D : ℝ} (hκ : 0 < κ)
    (hl : 0 < l) (hκl : κ * l ≤ 1 / 4) (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → Real.exp (τ * strictHeight κ (-e)) * A ≤
      C * (Real.exp (τ * strictHeight κ (-l + 3 * e)) * D +
        Real.exp (τ * strictHeight κ (l + 3 * e)) * S)) :
    ∃ C' : ℝ, 0 < C' ∧
      A ≤ C' * (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) := by
  obtain ⟨ha, hb, -, -⟩ := strictExponent_bounds hκ hl hκl he he4
  set p0 := strictHeight κ (-e)
  set pD := strictHeight κ (-l + 3 * e)
  set pS := strictHeight κ (l + 3 * e)
  have hbal := exp_balance (a := p0 - pD) (b := pS - p0) (C := C) (τ0 := τ0) ha hb hC hA hS hAD
    (by
      intro τ hτ
      have h1 := h τ hτ
      have hE : 0 < Real.exp (τ * p0) := Real.exp_pos _
      have eD : Real.exp (τ * pD) = Real.exp (τ * p0) * Real.exp (-((p0 - pD) * τ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have eS : Real.exp (τ * pS) = Real.exp (τ * p0) * Real.exp ((pS - p0) * τ) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [eD, eS] at h1
      have h2 : Real.exp (τ * p0) * A ≤ Real.exp (τ * p0) *
          (C * (Real.exp (-((p0 - pD) * τ)) * D + Real.exp ((pS - p0) * τ) * S)) := by
        linarith
      exact le_of_mul_le_mul_left h2 hE)
  have hsum : p0 - pD + (pS - p0) = pS - pD := by ring
  rw [hsum] at hbal
  have hg : (pS - p0) / (pS - pD) = 1 - (p0 - pD) / (pS - pD) := by
    have hne : pS - pD ≠ 0 := by
      have := add_pos ha hb; rw [hsum] at this; exact this.ne'
    field_simp
    ring
  rw [hg] at hbal
  exact ⟨2 * C + Real.exp ((p0 - pD) * τ0), by positivity, hbal⟩

/-- G2 exponent bookkeeping (basis arm): observed norm `mu`, large norm `1` gives `C' mu^g`. -/
theorem interp_basis_bound {C' g μ A : ℝ} (h : A ≤ C' * (μ ^ g * (1 : ℝ) ^ (1 - g))) :
    A ≤ C' * μ ^ g := by
  simpa [Real.one_rpow] using h

/-- G2 exponent bookkeeping (coefficient arm): observed norm `<= M`, large norm `<= M/mu`
gives `C' M mu^(g-1)` (the unnormalized `b_i` exponent `g-1`, source convention). -/
theorem interp_coeff_bound {C' g μ M Sb Db A : ℝ} (hμ : 0 < μ) (hM : 0 ≤ M) (hC : 0 ≤ C')
    (hS0 : 0 ≤ Sb) (hSb : Sb ≤ M) (hD0 : 0 ≤ Db) (hDb : Db ≤ M / μ) (hg0 : 0 ≤ g)
    (hg1 : g ≤ 1) (h : A ≤ C' * (Sb ^ g * Db ^ (1 - g))) :
    A ≤ C' * M * μ ^ (g - 1) := by
  have h1 : Sb ^ g ≤ M ^ g := Real.rpow_le_rpow hS0 hSb hg0
  have h2 : Db ^ (1 - g) ≤ (M / μ) ^ (1 - g) := Real.rpow_le_rpow hD0 hDb (by linarith)
  have h3 : M ^ g * (M / μ) ^ (1 - g) = M * μ ^ (g - 1) := by
    rw [Real.div_rpow hM hμ.le, mul_div_assoc', ← Real.rpow_add' hM (by norm_num),
      show g + (1 - g) = 1 by ring, Real.rpow_one, show g - 1 = -(1 - g) by ring,
      Real.rpow_neg hμ.le, div_eq_mul_inv]
  have h4 : Sb ^ g * Db ^ (1 - g) ≤ M ^ g * (M / μ) ^ (1 - g) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc A ≤ C' * (Sb ^ g * Db ^ (1 - g)) := h
    _ ≤ C' * (M ^ g * (M / μ) ^ (1 - g)) := mul_le_mul_of_nonneg_left h4 hC
    _ = C' * M * μ ^ (g - 1) := by rw [h3]; ring

/-- `mu * mu^(g-1) = mu^g`: the normalized coefficient `mu_i b_i` carries exponent `g`. -/
theorem mul_rpow_sub_one {μ g : ℝ} (hμ : 0 < μ) : μ * μ ^ (g - 1) = μ ^ g := by
  calc μ * μ ^ (g - 1) = μ ^ (1 : ℝ) * μ ^ (g - 1) := by rw [Real.rpow_one]
    _ = μ ^ (1 + (g - 1)) := (Real.rpow_add hμ _ _).symm
    _ = μ ^ g := by congr 1; ring

end C4Balancing

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-!
## C4 (G1(a)) strict-weight Carleman: saved squares and the signed shift

Source: 03-product-continuation.tex lines 189-254 (two squared parts, REAL signed shift `m`,
normal-square absorption). Expansion: REPORT.md section 1, items T1-T5, written before this code.
Generic layer of the existing `CollaboratorUCPIdentityOct17` (`identity1`, `identity2`,
`conj_identity`), Euclidean `volume`. The phase is NEVER changed; `m` has no sign condition.
-/
namespace OAI.AnisotropicCalderon.StrictWeightCarleman
open MeasureTheory
open scoped ContDiff

section SavedSquares
variable {a : Fin 3 → Fin 3 → R3 → ℝ} {X : Fin 3 → R3 → ℝ} {q θ v : R3 → ℝ}

/-- T1: the exact integrated commutator identity RETAINING the squares, for every real `κ`
and every (signed) smooth auxiliary `θ`:
`∫(S+B)² = ∫Qfun + ∫(B² + (1-κ)S² + κ(S+θv)²)`. -/
theorem integral_sq_saved_eq (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hX : ∀ j, ContDiff ℝ ∞ (X j)) (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ)
    (hv : ContDiff ℝ ∞ v) (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v) (κ : ℝ) :
    Integrable (Qfun a X q θ κ v) ∧
    Integrable (fun x => Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
        κ * (Sop a q v x + θ x * v x) ^ 2) ∧
    ∫ x, (Sop a q v x + Bop X v x) ^ 2 = (∫ x, Qfun a X q θ κ v x) +
      ∫ x, (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
        κ * (Sop a q v x + θ x * v x) ^ 2) := by
  set G : Fin 3 → R3 → ℝ := fun i x => F1 a X q v i x + κ * F2 a θ v i x with hG
  have hGs : ∀ i, ContDiff ℝ ∞ (G i) := fun i =>
    (contDiff_F1 ha hX hq hθ hv i).add (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i))
  have hGc : ∀ i, HasCompactSupport (G i) := hasCompactSupport_F ha hX hq hθ hv hvc κ
  set H : R3 → ℝ := fun x => 2 * Sop a q v x * Bop X v x - 2 * κ * θ x * v x * Sop a q v x -
    κ * θ x ^ 2 * (v x * v x) with hH
  have hHQ : ∀ x, H x = Qfun a X q θ κ v x + ∑ i, pd i (G i) x := by
    intro x
    have e1 := identity1 ha hsymm hX hq hv x
    have e2 := identity2 ha hsymm hq hθ hv x
    have hpdG : ∀ i, pd i (G i) x = pd i (F1 a X q v i) x + κ * pd i (F2 a θ v i) x := by
      intro i
      simp only [hG]
      rw [pd_add (contDiff_F1 ha hX hq hθ hv i)
        (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i)),
        pd_const_mul _ (contDiff_F2 ha hX hq hθ hv i)]
    simp only [hpdG, Finset.sum_add_distrib, ← Finset.mul_sum, hH, Qfun]
    linear_combination e1 + κ * e2
  have hS := contDiff_Sop (q := q) ha hX hq hθ hv
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hHi : Integrable H := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [hH, Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · simp only [hH]; fun_prop
  have hRi : Integrable (fun x => Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · fun_prop
  have hdi : ∀ i, Integrable (pd i (G i)) := fun i =>
    integrable_of_contDiff_hasCompactSupport (contDiff_pd (hGs i)) (hasCompactSupport_pd (hGc i))
  have hQeq : Qfun a X q θ κ v = fun x => H x - ∑ i, pd i (G i) x := by
    funext x; rw [hHQ x]; ring
  have hQi : Integrable (Qfun a X q θ κ v) := by
    rw [hQeq]; exact hHi.sub (integrable_finsetSum _ fun i _ => hdi i)
  have hint : ∫ x, H x = ∫ x, Qfun a X q θ κ v x := by
    have : ∫ x, ∑ i, pd i (G i) x = 0 := by
      rw [integral_finsetSum _ fun i _ => hdi i]
      simp [integral_pd_eq_zero (hGs _) (hGc _)]
    rw [hQeq, integral_sub hHi (integrable_finsetSum _ fun i _ => hdi i), this, sub_zero]
  refine ⟨hQi, hRi, ?_⟩
  have hpt : (fun x => (Sop a q v x + Bop X v x) ^ 2) = fun x => H x +
      (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 + κ * (Sop a q v x + θ x * v x) ^ 2) := by
    funext x; simp only [hH]; ring
  rw [hpt, integral_add hHi hRi, hint]

/-- T1 (retained `B²`): for `0 ≤ κ ≤ 1`, `∫(Qfun + B²) ≤ ∫(S+B)²`. -/
theorem integral_Qfun_add_Bop_sq_le (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hX : ∀ j, ContDiff ℝ ∞ (X j)) (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ)
    (hv : ContDiff ℝ ∞ v) (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Integrable (fun x => Qfun a X q θ κ v x + Bop X v x ^ 2) ∧
    ∫ x, (Qfun a X q θ κ v x + Bop X v x ^ 2) ≤ ∫ x, (Sop a q v x + Bop X v x) ^ 2 := by
  obtain ⟨hQi, hRi, heq⟩ := integral_sq_saved_eq ha hX hq hθ hv hsymm hvc κ
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hBi : Integrable (fun x => Bop X v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx; simp [Bop_vanish ha hX hq hθ hv hx]
    · fun_prop
  refine ⟨hQi.add hBi, ?_⟩
  rw [heq, integral_add hQi hBi]
  have hmono : ∫ x, Bop X v x ^ 2 ≤ ∫ x, (Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2) := by
    apply integral_mono hBi hRi
    intro x
    have h1 : 0 ≤ (1 - κ) * Sop a q v x ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0 ≤ κ * (Sop a q v x + θ x * v x) ^ 2 := mul_nonneg hκ0 (sq_nonneg _)
    show Bop X v x ^ 2 ≤ Bop X v x ^ 2 + (1 - κ) * Sop a q v x ^ 2 +
      κ * (Sop a q v x + θ x * v x) ^ 2
    linarith
  linarith

end SavedSquares

section SignedShift
variable {a : Fin 3 → Fin 3 → R3 → ℝ}

theorem divV_const_mul (τ : ℝ) {W : Fin 3 → R3 → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : R3) :
    divV (fun j y => τ * W j y) x = τ * divV W x := by
  unfold divV
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => pd_const_mul τ (hW j) x

theorem Lop_const_mul (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : R3) :
    Lop a (fun y => τ * f y) x = τ * Lop a f x := by
  have h1 : ∀ i, (fun z => ∑ k, a i k z * pd k (fun y => τ * f y) z) =
      fun z => τ * ∑ k, a i k z * pd k f z := by
    intro i; funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_const_mul τ hf]; ring
  have h2 : ∀ i, ContDiff ℝ ∞ (fun z => ∑ k, a i k z * pd k f z) := by
    intro i
    have : ∀ k, ContDiff ℝ ∞ (fun y => a i k y) := fun k => ha i k
    fun_prop
  unfold Lop
  simp only [h1]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => pd_const_mul τ (h2 i) x

theorem Lop_const (c : ℝ) (x : R3) : Lop a (fun _ => c) x = 0 := by
  simp [Lop, pd_const]

theorem Mgrad_const_mul (τ : ℝ) {W : Fin 3 → R3 → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : R3)
    (ξ : Fin 3 → ℝ) :
    Mgrad a (fun j y => τ * W j y) x ξ = τ * Mgrad a W x ξ := by
  have h : ∀ i j, pd i (fun y => τ * W j y) x = τ * pd i (W j) x :=
    fun i j => pd_const_mul τ (hW j) x
  simp only [Mgrad, h, Fin.sum_univ_three]
  ring

theorem mzero_const_mul (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ : ℝ) {W : Fin 3 → R3 → ℝ}
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {N : R3 → ℝ} (hN : ContDiff ℝ ∞ N) (x : R3) :
    mzero a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) x =
      τ ^ 3 * (2 * ∑ j, W j x * pd j N x) - τ * Lop a (divV W) x := by
  have hd : divV (fun j y => τ * W j y) = fun y => τ * divV W y :=
    funext (divV_const_mul τ hW)
  have hpN : ∀ j, pd j (fun y => τ ^ 2 * N y) x = τ ^ 2 * pd j N x :=
    fun j => pd_const_mul _ hN x
  unfold mzero
  rw [hd, Lop_const_mul ha τ (contDiff_divV hW)]
  simp only [hpN, Fin.sum_univ_three]
  ring

/-- T2: the skew part for the unchanged phase, `Bτ v = -τ(2 W·∇v + (div W) v)`. -/
theorem Bop_const_mul (τ : ℝ) {W : Fin 3 → R3 → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (v : R3 → ℝ) (x : R3) :
    Bop (fun j y => τ * W j y) v x = -τ * (2 * ∑ j, W j x * pd j v x + divV W x * v x) := by
  unfold Bop
  rw [divV_const_mul τ hW x]
  simp only [Fin.sum_univ_three]
  ring

/-- T2: the exact signed-shift integrand: `X = τW`, `q = τ²N`, auxiliary `θ ≡ 4mτ`
(`m` any REAL), `κ = 1/2`. The `-8m²τ²` is the completion cost. -/
theorem Qfun_signed_shift (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ m : ℝ) {W : Fin 3 → R3 → ℝ}
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {N : R3 → ℝ} (hN : ContDiff ℝ ∞ N) (v : R3 → ℝ) (x : R3) :
    Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ) (1 / 2) v x =
      τ * (Mgrad a W x (grad v x) + 4 * m * quad a x (grad v x)) +
      (τ ^ 3 * (2 * ∑ j, W j x * pd j N x - 4 * m * N x) - 8 * m ^ 2 * τ ^ 2 -
        τ * Lop a (divV W) x) * (v x * v x) := by
  unfold Qfun
  rw [Mgrad_const_mul τ hW, mzero_const_mul ha τ hW hN, Lop_const]
  ring

/-- The unchanged-phase gradient field `W = a ∇ϑ`. -/
def phaseField (a : Fin 3 → Fin 3 → R3 → ℝ) (ϑ : R3 → ℝ) (j : Fin 3) (y : R3) : ℝ :=
  ∑ k, a j k y * pd k ϑ y

/-- The unchanged-phase squared gradient `N = a(∇ϑ,∇ϑ)`. -/
def phaseNorm (a : Fin 3 → Fin 3 → R3 → ℝ) (ϑ : R3 → ℝ) (y : R3) : ℝ :=
  ∑ i, ∑ k, a i k y * pd i ϑ y * pd k ϑ y

theorem contDiff_phaseField (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {ϑ : R3 → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) (j : Fin 3) : ContDiff ℝ ∞ (phaseField a ϑ j) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold phaseField; fun_prop

theorem contDiff_phaseNorm (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {ϑ : R3 → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) : ContDiff ℝ ∞ (phaseNorm a ϑ) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold phaseNorm; fun_prop

/-- T3: conjugation by the UNCHANGED phase `τϑ` (existing `conj_identity`, `Φ = τϑ`). -/
theorem conj_unchanged_phase (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hsymm : ∀ i k, a i k = a k i)
    {ϑ v : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (hv : ContDiff ℝ ∞ v) (τ : ℝ) (x : R3) :
    Lop a (fun y => Real.exp (-(τ * ϑ y)) * v y) x =
      Real.exp (-(τ * ϑ x)) * (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y) v x +
        Bop (fun j y => τ * phaseField a ϑ j y) v x) := by
  have hΦ : ContDiff ℝ ∞ (fun y => τ * ϑ y) := contDiff_const.mul hϑ
  have hp : ∀ k y, pd k (fun y => τ * ϑ y) y = τ * pd k ϑ y := fun k y => pd_const_mul τ hϑ y
  have e1 : (fun y => ∑ i, ∑ k, a i k y * pd i (fun y => τ * ϑ y) y *
      pd k (fun y => τ * ϑ y) y) = fun y => τ ^ 2 * phaseNorm a ϑ y := by
    funext y
    unfold phaseNorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hp, hp]; ring
  have e2 : (fun j y => ∑ k, a j k y * pd k (fun y => τ * ϑ y) y) =
      fun j y => τ * phaseField a ϑ j y := by
    funext j y
    unfold phaseField
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hp]; ring
  have h := conj_identity ha hsymm hΦ hv x
  rw [e1, e2] at h
  exact h

/-- T4: pointwise signed-shift absorption of the rank-one normal loss through the RETAINED
`B²` (pure real algebra; `m` of either sign). -/
theorem signed_shift_pointwise {α β D R0 d0 m τ Mq Gr w d R Z B v : ℝ}
    (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : α * Gr ≤ Mq + D * w ^ 2) (hZ : β ≤ Z) (hR : |R| ≤ R0) (hd : |d| ≤ d0)
    (hB : B = -τ * (2 * w + d * v))
    (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * Gr + β / 2 * τ ^ 3 * (v * v) ≤
      τ * Mq + (τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R) * (v * v) + B ^ 2 := by
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ1
  have hV : 0 ≤ v * v := mul_self_nonneg v
  have h1 : τ * (α * Gr) ≤ τ * (Mq + D * w ^ 2) := mul_le_mul_of_nonneg_left hcoef hτ0.le
  -- normal square from the skew part
  have h2w : 2 * τ * w = -B - τ * d * v := by rw [hB]; ring
  have hd2 : d ^ 2 ≤ d0 ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le hd) (le_of_abs_le hd)
    exact this
  have hw4 : 4 * τ ^ 2 * w ^ 2 ≤ 2 * B ^ 2 + 2 * τ ^ 2 * d0 ^ 2 * (v * v) := by
    have e : 4 * τ ^ 2 * w ^ 2 = (B + τ * d * v) ^ 2 := by
      have : (2 * τ * w) ^ 2 = (-B - τ * d * v) ^ 2 := by rw [h2w]
      nlinarith [this]
    have hdd : τ ^ 2 * d ^ 2 * (v * v) ≤ τ ^ 2 * d0 ^ 2 * (v * v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (sq_nonneg τ)) hV
    nlinarith [sq_nonneg (B - τ * d * v)]
  have h2 : τ * D * w ^ 2 ≤ B ^ 2 / 2 + D * τ * d0 ^ 2 * (v * v) / 2 := by
    have hmul : D * (4 * τ ^ 2 * w ^ 2) ≤ D * (2 * B ^ 2 + 2 * τ ^ 2 * d0 ^ 2 * (v * v)) :=
      mul_le_mul_of_nonneg_left hw4 hD
    have hDB : D * B ^ 2 ≤ τ * B ^ 2 := mul_le_mul_of_nonneg_right hτD (sq_nonneg B)
    have key : τ * (τ * D * w ^ 2) ≤ τ * (B ^ 2 / 2 + D * τ * d0 ^ 2 * (v * v) / 2) := by
      nlinarith
    exact le_of_mul_le_mul_left key hτ0
  -- mass coefficient
  have hZ3 : τ ^ 3 * β ≤ τ ^ 3 * Z := mul_le_mul_of_nonneg_left hZ (by positivity)
  have hRR : τ * R ≤ τ * R0 := mul_le_mul_of_nonneg_left (le_of_abs_le hR) hτ0.le
  have hm2 : 32 * m ^ 2 * τ ^ 2 ≤ β * τ * τ ^ 2 :=
    mul_le_mul_of_nonneg_right hτm (sq_nonneg τ)
  have hβτ : β * τ ≤ β * τ * τ := by
    have : 0 ≤ β * τ := by positivity
    nlinarith
  have hR2 : 4 * (R0 + D * d0 ^ 2 / 2) * τ ≤ β * τ * τ * τ :=
    mul_le_mul_of_nonneg_right (hτR.trans hβτ) hτ0.le
  have hc : β / 2 * τ ^ 3 ≤
      τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R - D * τ * d0 ^ 2 / 2 := by
    nlinarith
  have h3V : β / 2 * τ ^ 3 * (v * v) ≤
      (τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R - D * τ * d0 ^ 2 / 2) * (v * v) :=
    mul_le_mul_of_nonneg_right hc hV
  nlinarith [sq_nonneg B]

/-- T5 (v-form): integrated signed-shift estimate with the retained `B²`, for compactly
supported smooth `v`, from POINTWISE coefficient bounds on a set `K ⊇ tsupport v`.
The coefficient bounds are intermediate targets (T6 derives them from strictness);
they are not endpoint premises. -/
theorem principal_estimate_of_coefficient_bounds (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {W : Fin 3 → R3 → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j))
    {N : R3 → ℝ} (hN : ContDiff ℝ ∞ N) {v : R3 → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (K : Set R3) (hsupp : tsupport v ⊆ K)
    (m α β D R0 d0 : ℝ) (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, α * ∑ i, ξ i ^ 2 ≤
      Mgrad a W x ξ + 4 * m * quad a x ξ + D * (∑ j, W j x * ξ j) ^ 2)
    (hZ : ∀ x ∈ K, β ≤ 2 * ∑ j, W j x * pd j N x - 4 * m * N x)
    (hR : ∀ x ∈ K, |Lop a (divV W) x| ≤ R0)
    (hd : ∀ x ∈ K, |divV W x| ≤ d0)
    (τ : ℝ) (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * (∫ x, ∑ i, pd i v x ^ 2) + β / 2 * τ ^ 3 * (∫ x, v x ^ 2) ≤
      ∫ x, (Sop a (fun y => τ ^ 2 * N y) v x + Bop (fun j y => τ * W j y) v x) ^ 2 := by
  have hX : ∀ j, ContDiff ℝ ∞ (fun y => τ * W j y) := fun j => contDiff_const.mul (hW j)
  have hq : ContDiff ℝ ∞ (fun y => τ ^ 2 * N y) := contDiff_const.mul hN
  have hθc : ContDiff ℝ ∞ (fun _ : R3 => 4 * m * τ) := contDiff_const
  obtain ⟨hI, hle⟩ := integral_Qfun_add_Bop_sq_le (X := fun j y => τ * W j y)
    (θ := fun _ => 4 * m * τ) ha hX hq hθc hv hsymm hvc (κ := 1 / 2) (by norm_num) (by norm_num)
  have hG : Integrable (fun x => ∑ i, pd i v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [(vanish_outside hx).2.1]
    · fun_prop
  have hV : Integrable (fun x => v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    · fun_prop
  have hpt : ∀ x, α * τ * ∑ i, pd i v x ^ 2 + β / 2 * τ ^ 3 * v x ^ 2 ≤
      Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ) (1 / 2) v x +
        Bop (fun j y => τ * W j y) v x ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport v
    · have hxK := hsupp hx
      rw [Qfun_signed_shift ha τ m hW hN v x]
      have hc := hcoef x hxK (grad v x)
      have key := signed_shift_pointwise (Gr := ∑ i, pd i v x ^ 2)
        (w := ∑ j, W j x * pd j v x) (d := divV W x) (v := v x) (R := Lop a (divV W) x)
        (Z := 2 * ∑ j, W j x * pd j N x - 4 * m * N x)
        (Mq := Mgrad a W x (grad v x) + 4 * m * quad a x (grad v x))
        (B := Bop (fun j y => τ * W j y) v x) hβ hD hc (hZ x hxK) (hR x hxK) (hd x hxK)
        (Bop_const_mul τ hW v x) hτ1 hτD hτm hτR
      linarith [key]
    · obtain ⟨h0, h1, -⟩ := vanish_outside hx
      have hB0 := Bop_vanish ha hX hq hθc hv hx
      have hQ0 : Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ)
          (1 / 2) v x = 0 := by
        simp [Qfun, Mgrad, quad, grad, h0, h1]
      rw [hQ0, hB0]
      simp [h0, h1]
  have hL : Integrable (fun x => α * τ * ∑ i, pd i v x ^ 2 + β / 2 * τ ^ 3 * v x ^ 2) :=
    (hG.const_mul _).add (hV.const_mul _)
  have hmono := integral_mono hL hI (fun x => hpt x)
  rw [integral_add (hG.const_mul _) (hV.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- T3+T5: the strict-weight principal estimate for the UNCHANGED phase `ϑ`, in conjugated
form `v = exp(τϑ) w`, against `exp(2τϑ) (div(a∇w))²`, from the pointwise coefficient bounds of
the actual phase fields `W = a∇ϑ`, `N = a(∇ϑ,∇ϑ)` on `K ⊇ tsupport w`; `m` any real. -/
theorem unchanged_phase_estimate_of_coefficient_bounds (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ w : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (K : Set R3) (hK : tsupport w ⊆ K)
    (m α β D R0 d0 : ℝ) (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, α * ∑ i, ξ i ^ 2 ≤
      Mgrad a (phaseField a ϑ) x ξ + 4 * m * quad a x ξ +
        D * (∑ j, phaseField a ϑ j x * ξ j) ^ 2)
    (hZ : ∀ x ∈ K, β ≤ 2 * ∑ j, phaseField a ϑ j x * pd j (phaseNorm a ϑ) x -
      4 * m * phaseNorm a ϑ x)
    (hR : ∀ x ∈ K, |Lop a (divV (phaseField a ϑ)) x| ≤ R0)
    (hd : ∀ x ∈ K, |divV (phaseField a ϑ) x| ≤ d0)
    (τ : ℝ) (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
      β / 2 * τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
      ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  have hv : ContDiff ℝ ∞ (fun y => Real.exp (τ * ϑ y) * w y) := by fun_prop
  have hvc : HasCompactSupport (fun y => Real.exp (τ * ϑ y) * w y) :=
    HasCompactSupport.mul_left (f := fun y => Real.exp (τ * ϑ y)) hwc
  have hsupp : tsupport (fun y => Real.exp (τ * ϑ y) * w y) ⊆ K :=
    (tsupport_mul_subset_right (f := fun y => Real.exp (τ * ϑ y))).trans hK
  have h := principal_estimate_of_coefficient_bounds ha hsymm (contDiff_phaseField ha hϑ)
    (contDiff_phaseNorm ha hϑ) hv hvc K hsupp m α β D R0 d0 hβ hD hcoef hZ hR hd τ hτ1 hτD
    hτm hτR
  have hconj : ∀ x, (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y)
      (fun y => Real.exp (τ * ϑ y) * w y) x +
      Bop (fun j y => τ * phaseField a ϑ j y) (fun y => Real.exp (τ * ϑ y) * w y) x) ^ 2 =
      Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
    intro x
    have h1 := conj_unchanged_phase ha hsymm hϑ hv τ x
    have hvw : (fun y => Real.exp (-(τ * ϑ y)) * (Real.exp (τ * ϑ y) * w y)) = w := by
      funext y
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hvw] at h1
    have e : Real.exp (2 * (τ * ϑ x)) * Real.exp (-(τ * ϑ x)) ^ 2 = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add,
        show 2 * (τ * ϑ x) + (-(τ * ϑ x) + -(τ * ϑ x)) = 0 by ring, Real.exp_zero]
    rw [h1, mul_pow, ← mul_assoc, e, one_mul]
  have hint : (∫ x, (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y)
      (fun y => Real.exp (τ * ϑ y) * w y) x +
      Bop (fun j y => τ * phaseField a ϑ j y) (fun y => Real.exp (τ * ϑ y) * w y) x) ^ 2) =
      ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 :=
    congrArg (fun f : R3 → ℝ => ∫ x, f x) (funext hconj)
  exact h.trans hint.le

end SignedShift

section StrictMargins

/-- Sup-norm to Euclidean sum of squares on `Fin 3 → ℝ`. -/
theorem sum_sq_le_three_norm_sq (ξ : Fin 3 → ℝ) : ∑ i, ξ i ^ 2 ≤ 3 * ‖ξ‖ ^ 2 := by
  have h : ∀ i, ξ i ^ 2 ≤ ‖ξ‖ ^ 2 := by
    intro i
    have h1 : ‖ξ i‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ i
    rw [Real.norm_eq_abs] at h1
    calc ξ i ^ 2 = |ξ i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  simp only [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_lower_on_compact {K : Set R3} (hK : IsCompact K) {f : R3 → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ K, β ≤ f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h hf
  exact ⟨f x0, hpos x0 hx0, fun x hx => hmin hx⟩

/-- T6a: uniform rank-one (Finsler) coercivity by compactness. Tangential positivity of a
continuous quadratic family on the kernel of a continuous linear family gives ONE `D ≥ 0`
and ONE `α > 0` with `α Σξᵢ² ≤ Q + Dℓ²` on all of `K`. No sign condition on `Q` itself. -/
theorem uniform_rank_one_coercivity {K : Set R3} (hK : IsCompact K)
    (Q ℓ : R3 → (Fin 3 → ℝ) → ℝ)
    (hQc : Continuous (fun p : R3 × (Fin 3 → ℝ) => Q p.1 p.2))
    (hℓc : Continuous (fun p : R3 × (Fin 3 → ℝ) => ℓ p.1 p.2))
    (hQh : ∀ x (c : ℝ) ξ, Q x (c • ξ) = c ^ 2 * Q x ξ)
    (hℓh : ∀ x (c : ℝ) ξ, ℓ x (c • ξ) = c * ℓ x ξ)
    (hpos : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ℓ x ξ = 0 → 0 < Q x ξ) :
    ∃ D α : ℝ, 0 ≤ D ∧ 0 < α ∧ ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ,
      α * ∑ i, ξ i ^ 2 ≤ Q x ξ + D * ℓ x ξ ^ 2 := by
  set S : Set (Fin 3 → ℝ) := Metric.sphere 0 1 with hSdef
  set T : Set (R3 × (Fin 3 → ℝ)) := K ×ˢ S with hTdef
  have hT : IsCompact T := hK.prod (isCompact_sphere 0 1)
  set F : ℕ → R3 × (Fin 3 → ℝ) → ℝ := fun n p => Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 with hF
  have hFc : ∀ n, Continuous (F n) := fun n => hQc.add (continuous_const.mul (hℓc.pow 2))
  set C : ℕ → Set (R3 × (Fin 3 → ℝ)) := fun n => T ∩ F n ⁻¹' Set.Iic 0 with hC
  have hCcl : ∀ n, IsClosed (C n) := fun n =>
    hT.isClosed.inter (isClosed_Iic.preimage (hFc n))
  have hCc : ∀ n, IsCompact (C n) := fun n => hT.of_isClosed_subset (hCcl n) Set.inter_subset_left
  have hmono : ∀ n n', n ≤ n' → C n' ⊆ C n := by
    intro n n' hnn p hp
    refine ⟨hp.1, ?_⟩
    have h1 : F n' p ≤ 0 := hp.2
    have h2 : F n p ≤ F n' p := by
      simp only [hF]
      have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
      nlinarith [sq_nonneg (ℓ p.1 p.2)]
    exact le_trans h2 h1
  have hempty : ∃ n, C n = ∅ := by
    by_contra hne
    push_neg at hne
    have hdir : Directed (· ⊇ ·) C := fun n n' =>
      ⟨max n n', hmono n _ (le_max_left _ _), hmono n' _ (le_max_right _ _)⟩
    obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir
      (fun n => hne n) hCc hCcl
    rw [Set.mem_iInter] at hp
    have hpT : p ∈ T := (hp 0).1
    have hle : ∀ n : ℕ, Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 ≤ 0 := fun n => (hp n).2
    have hℓ0 : ℓ p.1 p.2 = 0 := by
      by_contra hℓ
      have hsq : 0 < ℓ p.1 p.2 ^ 2 := by positivity
      obtain ⟨n, hn⟩ := exists_nat_gt (-Q p.1 p.2 / ℓ p.1 p.2 ^ 2)
      have h1 := hle n
      rw [div_lt_iff₀ hsq] at hn
      linarith
    have hξ : p.2 ≠ 0 := by
      intro h0
      have h1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hpT.2
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hQ := hpos p.1 hpT.1 p.2 hξ hℓ0
    have h0 := hle 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h0
    linarith
  obtain ⟨n, hn⟩ := hempty
  have hFpos : ∀ p ∈ T, 0 < F n p := by
    intro p hp
    by_contra h
    push_neg at h
    have : p ∈ C n := ⟨hp, h⟩
    rw [hn] at this
    exact this
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨n, 1, Nat.cast_nonneg n, one_pos, by simp [hK0]⟩
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hTne : T.Nonempty := hKne.prod hSne
  obtain ⟨p0, hp0, hmin⟩ := hT.exists_isMinOn hTne (hFc n).continuousOn
  have hα0 : 0 < F n p0 := hFpos p0 hp0
  have hα3 : 0 < F n p0 / 3 := div_pos hα0 (by norm_num)
  refine ⟨n, F n p0 / 3, Nat.cast_nonneg n, hα3, ?_⟩
  intro x hx ξ
  have hQ0 : Q x 0 = 0 := by
    have := hQh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  have hℓ0 : ℓ x 0 = 0 := by
    have := hℓh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  by_cases hξ : ξ = 0
  · subst hξ
    simp [hQ0, hℓ0]
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set η : Fin 3 → ℝ := ‖ξ‖⁻¹ • ξ with hη
  have hηS : (x, η) ∈ T := by
    refine ⟨hx, ?_⟩
    show η ∈ Metric.sphere (0 : Fin 3 → ℝ) 1
    rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hmin' : F n p0 ≤ F n (x, η) := hmin hηS
  have hξη : ξ = ‖ξ‖ • η := by
    rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hFξ : Q x ξ + (n : ℝ) * ℓ x ξ ^ 2 = ‖ξ‖ ^ 2 * F n (x, η) := by
    conv_lhs => rw [hξη, hQh, hℓh]
    simp only [hF]
    ring
  have h3 := sum_sq_le_three_norm_sq ξ
  have hfin : F n p0 / 3 * ∑ i, ξ i ^ 2 ≤ F n p0 * ‖ξ‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hα3.le
    linarith
  have hfin2 : F n p0 * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * F n (x, η) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  rw [hFξ]
  linarith

variable {a : Fin 3 → Fin 3 → R3 → ℝ}

theorem contDiff_Lop (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Lop a f) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold Lop; fun_prop

/-- T6: the coordinate strict-weight Carleman estimate for the UNCHANGED phase `ϑ` on a compact
`K`. Hypotheses are exactly the signed-`m` coordinate strict pseudo-convexity of `ϑ` on `K`
(tangential: shifted `Mgrad` positive on `ker (W·)`; normal: `Z > 0`); `m` is any real. The
constants `C, τ0` are chosen BEFORE `τ` and `w`. -/
theorem strict_weight_carleman_of_coordinate_strictness (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    {K : Set R3} (hK : IsCompact K) (m : ℝ)
    (htan : ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j x * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) x ξ + 4 * m * quad a x ξ)
    (hnor : ∀ x ∈ K, 0 < 2 * ∑ j, phaseField a ϑ j x * pd j (phaseNorm a ϑ) x -
      4 * m * phaseNorm a ϑ x) :
    ∃ C τ0 : ℝ, 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  set W := phaseField a ϑ with hWdef
  set N := phaseNorm a ϑ with hNdef
  have hW : ∀ j, ContDiff ℝ ∞ (W j) := contDiff_phaseField ha hϑ
  have hN : ContDiff ℝ ∞ N := contDiff_phaseNorm ha hϑ
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (pd j (a i k)) := fun j i k => (contDiff_pd (ha i k)).continuous
  have hWc : ∀ j, Continuous (W j) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (pd i (W j)) := fun i j => (contDiff_pd (hW j)).continuous
  have hQc : Continuous (fun p : R3 × (Fin 3 → ℝ) =>
      Mgrad a W p.1 p.2 + 4 * m * quad a p.1 p.2) := by
    simp only [Mgrad, quad, Fin.sum_univ_three]
    fun_prop
  have hℓc : Continuous (fun p : R3 × (Fin 3 → ℝ) => ∑ j, W j p.1 * p.2 j) := by
    simp only [Fin.sum_univ_three]
    fun_prop
  obtain ⟨D, α, hD, hα, hcoef⟩ := uniform_rank_one_coercivity hK
    (fun x ξ => Mgrad a W x ξ + 4 * m * quad a x ξ) (fun x ξ => ∑ j, W j x * ξ j) hQc hℓc
    (by
      intro x c ξ
      simp only [Mgrad, quad, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      ring)
    (by
      intro x c ξ
      simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      ring)
    htan
  have hZc : ContinuousOn (fun x => 2 * ∑ j, W j x * pd j N x - 4 * m * N x) K := by
    have : ∀ j, Continuous (pd j N) := fun j => (contDiff_pd hN).continuous
    have : Continuous N := hN.continuous
    refine Continuous.continuousOn ?_
    simp only [Fin.sum_univ_three]
    fun_prop
  obtain ⟨β, hβ, hZ⟩ := exists_pos_lower_on_compact hK hZc hnor
  obtain ⟨R0, hR⟩ := hK.exists_bound_of_continuousOn
    (contDiff_Lop ha (contDiff_divV hW)).continuous.continuousOn
  obtain ⟨d0, hd⟩ := hK.exists_bound_of_continuousOn (contDiff_divV hW).continuous.continuousOn
  set c : ℝ := min α (β / 2) with hcdef
  have hc : 0 < c := lt_min hα (half_pos hβ)
  refine ⟨1 / c, max (max 1 D) (max (32 * m ^ 2 / β) (4 * (R0 + D * d0 ^ 2 / 2) / β)),
    one_div_pos.mpr hc, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro τ hτ w hw hwc hK'
  have hτ1 : 1 ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτD : D ≤ τ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have hτm : 32 * m ^ 2 ≤ β * τ := by
    have h1 : 32 * m ^ 2 / β ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
    rw [div_le_iff₀ hβ] at h1
    linarith
  have hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ := by
    have h1 : 4 * (R0 + D * d0 ^ 2 / 2) / β ≤ τ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
    rw [div_le_iff₀ hβ] at h1
    linarith
  have h := unchanged_phase_estimate_of_coefficient_bounds ha hsymm hϑ hw hwc K hK' m α β D R0
    d0 hβ hD hcoef hZ (fun x hx => by simpa [Real.norm_eq_abs] using hR x hx)
    (fun x hx => by simpa [Real.norm_eq_abs] using hd x hx) τ hτ1 hτD hτm hτR
  have hG0 : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV0 : 0 ≤ ∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hτ0 : 0 ≤ τ := by linarith
  have e1 : c * (τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2)) ≤
      α * τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hτ0) hG0
  have e2 : c * (τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2)) ≤
      β / 2 * τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hτ0 3)) hV0
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith

theorem Mgrad_smul (W : Fin 3 → R3 → ℝ) (x : R3) (c : ℝ) (ξ : Fin 3 → ℝ) :
    Mgrad a W x (c • ξ) = c ^ 2 * Mgrad a W x ξ := by
  simp only [Mgrad, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring

theorem quad_smul (x : R3) (c : ℝ) (ξ : Fin 3 → ℝ) : quad a x (c • ξ) = c ^ 2 * quad a x ξ := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring

theorem lin_smul (W : Fin 3 → R3 → ℝ) (x : R3) (c : ℝ) (ξ : Fin 3 → ℝ) :
    ∑ j, W j x * (c • ξ) j = c * ∑ j, W j x * ξ j := by
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring

theorem sum_sq_pos_of_ne_zero {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0) : 0 < ∑ i, ξ i ^ 2 := by
  by_contra hle
  push_neg at hle
  apply hξ
  funext i
  have hi : ξ i ^ 2 ≤ 0 := by
    have := Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun j _ => sq_nonneg (ξ j))
      (Finset.mem_univ i)
    linarith
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hi (sq_nonneg _))

/-- T9: from coordinate source strictness at ONE point `p` (tangential Hessian plus normal
Hessian value `h` positive on `ker (W(p)·)`, `N(p) > 0`), CONSTRUCT a real shift `m` (either
sign), a closed ball around `p`, and the strict-weight Carleman constants, chosen before `τ`
and `w`. -/
theorem local_strict_weight_carleman_of_point_strictness (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  set W := phaseField a ϑ with hWdef
  set N := phaseNorm a ϑ with hNdef
  set h : ℝ := (∑ j, W j p * pd j N p) / (2 * N p) with hhdef
  have hW : ∀ j, ContDiff ℝ ∞ (W j) := contDiff_phaseField ha hϑ
  have hNs : ContDiff ℝ ∞ N := contDiff_phaseNorm ha hϑ
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (pd j (a i k)) := fun j i k => (contDiff_pd (ha i k)).continuous
  have hWc : ∀ j, Continuous (W j) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (pd i (W j)) := fun i j => (contDiff_pd (hW j)).continuous
  have hNc : Continuous N := hNs.continuous
  have hdNc : ∀ j, Continuous (pd j N) := fun j => (contDiff_pd hNs).continuous
  -- the compact tangential unit set at `p`
  set Sg : Set (Fin 3 → ℝ) := Metric.sphere 0 1 ∩ {ξ | ∑ j, W j p * ξ j = 0} with hSg
  have hSgc : IsCompact Sg := (isCompact_sphere 0 1).inter_right
    (isClosed_eq (by simp only [Fin.sum_univ_three]; fun_prop) continuous_const)
  have hfc : Continuous (fun ξ : Fin 3 → ℝ => Mgrad a W p ξ + 4 * h * quad a p ξ) := by
    simp only [Mgrad, quad, Fin.sum_univ_three]; fun_prop
  have hqc : Continuous (fun ξ : Fin 3 → ℝ => quad a p ξ) := by
    simp only [quad, Fin.sum_univ_three]; fun_prop
  obtain ⟨μ, hμ, hμf⟩ : ∃ μ : ℝ, 0 < μ ∧ ∀ ξ ∈ Sg, μ ≤ Mgrad a W p ξ + 4 * h * quad a p ξ := by
    rcases Sg.eq_empty_or_nonempty with h0 | hne
    · exact ⟨1, one_pos, by simp [h0]⟩
    obtain ⟨ξ0, hξ0, hmin⟩ := hSgc.exists_isMinOn hne hfc.continuousOn
    refine ⟨_, hstrict ξ0 ?_ hξ0.2, fun ξ hξ => hmin hξ⟩
    intro h0
    have h1 : ‖ξ0‖ = 1 := mem_sphere_zero_iff_norm.mp hξ0.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨B, hB⟩ := hSgc.exists_bound_of_continuousOn hqc.continuousOn
  set Λ : ℝ := max B 1 with hΛ
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛne : Λ ≠ 0 := hΛpos.ne'
  have hc0 : 0 < μ / (2 * Λ) := div_pos hμ (mul_pos two_pos hΛpos)
  set m : ℝ := h - μ / (8 * Λ) with hm
  -- tangential positivity at `p` for the constructed signed `m`
  have htanp : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, W j p * ξ j = 0 →
      0 < Mgrad a W p ξ + 4 * m * quad a p ξ := by
    intro ξ hξ hker
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set η : Fin 3 → ℝ := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Sg := by
      refine ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      · show ∑ j, W j p * η j = 0
        rw [hη, lin_smul, hker, mul_zero]
    have h1 := hμf η hηS
    have h2 : quad a p η ≤ Λ := by
      have := hB η hηS
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hη' : 0 < Mgrad a W p η + 4 * m * quad a p η := by
      have e : Mgrad a W p η + 4 * m * quad a p η =
          (Mgrad a W p η + 4 * h * quad a p η) - μ / (2 * Λ) * quad a p η := by
        rw [hm]; ring
      have h3 : μ / (2 * Λ) * quad a p η ≤ μ / (2 * Λ) * Λ :=
        mul_le_mul_of_nonneg_left h2 hc0.le
      have h4 : μ / (2 * Λ) * Λ = μ / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right μ 2 hΛne
      rw [e]; linarith
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hξη, Mgrad_smul, quad_smul]
    have : 0 < ‖ξ‖ ^ 2 := by positivity
    nlinarith
  -- normal margin at `p`
  have hZp : 0 < 2 * ∑ j, W j p * pd j N p - 4 * m * N p := by
    have e : 2 * ∑ j, W j p * pd j N p - 4 * m * N p = μ / (2 * Λ) * N p := by
      have hNne : N p ≠ 0 := hN.ne'
      have hsN : (∑ j, W j p * pd j N p) / (2 * N p) * N p = (∑ j, W j p * pd j N p) / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right _ 2 hNne
      rw [hm, hhdef]
      linear_combination (-4) * hsN
    rw [e]; exact mul_pos hc0 hN
  -- uniform rank-one coercivity at the point
  have hQc : Continuous (fun q : R3 × (Fin 3 → ℝ) =>
      Mgrad a W q.1 q.2 + 4 * m * quad a q.1 q.2) := by
    simp only [Mgrad, quad, Fin.sum_univ_three]; fun_prop
  have hℓc : Continuous (fun q : R3 × (Fin 3 → ℝ) => ∑ j, W j q.1 * q.2 j) := by
    simp only [Fin.sum_univ_three]; fun_prop
  obtain ⟨D, α, hD, hα, hcoef⟩ := uniform_rank_one_coercivity isCompact_singleton
    (fun x ξ => Mgrad a W x ξ + 4 * m * quad a x ξ) (fun x ξ => ∑ j, W j x * ξ j) hQc hℓc
    (fun x c ξ => by simp only [Mgrad_smul, quad_smul]; ring)
    (fun x c ξ => lin_smul W x c ξ)
    (fun x hx ξ hξ hker => by
      rw [Set.mem_singleton_iff.mp hx] at hker ⊢
      exact htanp ξ hξ hker)
  -- persistence near `p` (tube lemma over the compact unit sphere)
  have hFc : Continuous (fun q : R3 × (Fin 3 → ℝ) =>
      Mgrad a W q.1 q.2 + 4 * m * quad a q.1 q.2 + D * (∑ j, W j q.1 * q.2 j) ^ 2) :=
    hQc.add (continuous_const.mul (hℓc.pow 2))
  have hev : ∀ᶠ x in nhds p, ∀ ξ ∈ Metric.sphere (0 : Fin 3 → ℝ) 1,
      0 < Mgrad a W x ξ + 4 * m * quad a x ξ + D * (∑ j, W j x * ξ j) ^ 2 := by
    apply (isCompact_sphere (0 : Fin 3 → ℝ) 1).eventually_forall_of_forall_eventually
    intro ξ0 hξ0
    have hne : ξ0 ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hξ0
      exact zero_ne_one hξ0
    have hpos0 : 0 < Mgrad a W p ξ0 + 4 * m * quad a p ξ0 + D * (∑ j, W j p * ξ0 j) ^ 2 := by
      have h1 : α * ∑ i, ξ0 i ^ 2 ≤ Mgrad a W p ξ0 + 4 * m * quad a p ξ0 +
          D * (∑ j, W j p * ξ0 j) ^ 2 := hcoef p (Set.mem_singleton p) ξ0
      have h2 := mul_pos hα (sum_sq_pos_of_ne_zero hne)
      linarith
    exact (hFc.continuousAt (x := (p, ξ0))).eventually (lt_mem_nhds hpos0)
  have hZc : Continuous (fun x => 2 * ∑ j, W j x * pd j N x - 4 * m * N x) := by
    simp only [Fin.sum_univ_three]; fun_prop
  have hZev : ∀ᶠ x in nhds p, 0 < 2 * ∑ j, W j x * pd j N x - 4 * m * N x :=
    (hZc.continuousAt (x := p)).eventually (lt_mem_nhds hZp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hZev)
  have hK : ∀ x ∈ Metric.closedBall p (ε / 2), dist x p < ε := fun x hx =>
    lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (half_lt_self hε)
  have htanK : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 →
      ∑ j, W j x * ξ j = 0 → 0 < Mgrad a W x ξ + 4 * m * quad a x ξ := by
    intro x hx ξ hξ hker
    have hx' := (hball (hK x hx)).1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set η : Fin 3 → ℝ := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Metric.sphere (0 : Fin 3 → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hkerη : ∑ j, W j x * η j = 0 := by rw [hη, lin_smul, hker, mul_zero]
    have h1 := hx' η hηS
    rw [hkerη] at h1
    have hη' : 0 < Mgrad a W x η + 4 * m * quad a x η := by nlinarith
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hξη, Mgrad_smul, quad_smul]
    have : 0 < ‖ξ‖ ^ 2 := by positivity
    nlinarith
  have hnorK : ∀ x ∈ Metric.closedBall p (ε / 2),
      0 < 2 * ∑ j, W j x * pd j N x - 4 * m * N x := fun x hx => (hball (hK x hx)).2
  obtain ⟨C, τ0, hC, hτ0, hest⟩ := strict_weight_carleman_of_coordinate_strictness ha hsymm hϑ
    (isCompact_closedBall p (ε / 2)) m htanK hnorK
  exact ⟨m, ε / 2, C, τ0, half_pos hε, hC, hτ0, hest⟩

/-- J3.a: the phase field of a scalar-rescaled coefficient. -/
theorem phaseField_smul_coeff {ρ ϑ : R3 → ℝ} (j : Fin 3) (y : R3) :
    phaseField (fun i k z => ρ z * a i k z) ϑ j y = ρ y * phaseField a ϑ j y := by
  simp only [phaseField, Fin.sum_univ_three]; ring

/-- J3.a: the phase norm of a scalar-rescaled coefficient. -/
theorem phaseNorm_smul_coeff {ρ ϑ : R3 → ℝ} (y : R3) :
    phaseNorm (fun i k z => ρ z * a i k z) ϑ y = ρ y * phaseNorm a ϑ y := by
  simp only [phaseNorm, Fin.sum_univ_three]; ring

/-- J3.a: the quadratic form of a scalar-rescaled coefficient. -/
theorem quad_smul_coeff {ρ : R3 → ℝ} (x : R3) (ξ : Fin 3 → ℝ) :
    quad (fun i k z => ρ z * a i k z) x ξ = ρ x * quad a x ξ := by
  simp only [quad, Fin.sum_univ_three]; ring

/-- J3.b: exact `Mgrad` rescaling for `a' = ρa`, `W' = ρW` (any smooth `W`). -/
theorem Mgrad_smul_coeff {ρ : R3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {W : Fin 3 → R3 → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : R3) (ξ : Fin 3 → ℝ) :
    Mgrad (fun i k z => ρ z * a i k z) (fun j y => ρ y * W j y) x ξ =
      ρ x ^ 2 * Mgrad a W x ξ +
      4 * ρ x * (∑ i, ∑ l, a i l x * ξ l * pd i ρ x) * (∑ j, W j x * ξ j) -
      2 * ρ x * (∑ j, W j x * pd j ρ x) * quad a x ξ := by
  have h1 : ∀ i j, pd i (fun y => ρ y * W j y) x = pd i ρ x * W j x + ρ x * pd i (W j) x :=
    fun i j => pd_mul hρ (hW j) x
  have h2 : ∀ j i k, pd j (fun z => ρ z * a i k z) x =
      pd j ρ x * a i k x + ρ x * pd j (a i k) x :=
    fun j i k => pd_mul hρ (ha i k) x
  simp only [Mgrad, quad, h1, h2, Fin.sum_univ_three]
  ring

/-- J3.d: the T9 point criterion transports EXACTLY from `a` to `b = ρa` for a smooth `ρ` with
`ρ(p) > 0` (the `∓2ρ(W·∇ρ)Q` terms cancel; the mixed term dies on the kernel). Phase unchanged,
no sign condition on `h` or `∇ρ`. -/
theorem point_strictness_smul {b a : Fin 3 → Fin 3 → R3 → ℝ} {ρ ϑ : R3 → ℝ}
    (hb : ∀ i k z, b i k z = ρ z * a i k z) (hρ : ContDiff ℝ ∞ ρ)
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hϑ : ContDiff ℝ ∞ ϑ) (p : R3) (hρp : 0 < ρ p)
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    0 < phaseNorm b ϑ p ∧
    ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField b ϑ j p * ξ j = 0 →
      0 < Mgrad b (phaseField b ϑ) p ξ +
        4 * ((∑ j, phaseField b ϑ j p * pd j (phaseNorm b ϑ) p) / (2 * phaseNorm b ϑ p)) *
          quad b p ξ := by
  have hb' : b = fun i k z => ρ z * a i k z :=
    funext fun i => funext fun k => funext fun z => hb i k z
  subst hb'
  have hW : ∀ j, ContDiff ℝ ∞ (phaseField a ϑ j) := contDiff_phaseField ha hϑ
  have hNs : ContDiff ℝ ∞ (phaseNorm a ϑ) := contDiff_phaseNorm ha hϑ
  have hF : phaseField (fun i k z => ρ z * a i k z) ϑ = fun j y => ρ y * phaseField a ϑ j y :=
    funext fun j => funext fun y => phaseField_smul_coeff j y
  have hNN : phaseNorm (fun i k z => ρ z * a i k z) ϑ = fun y => ρ y * phaseNorm a ϑ y :=
    funext fun y => phaseNorm_smul_coeff y
  simp only [hF, hNN]
  refine ⟨mul_pos hρp hN, fun ξ hξ hker => ?_⟩
  have hker0 : ∑ j, phaseField a ϑ j p * ξ j = 0 := by
    have e : ∑ j, ρ p * phaseField a ϑ j p * ξ j = ρ p * ∑ j, phaseField a ϑ j p * ξ j := by
      simp only [Fin.sum_univ_three]; ring
    rw [e] at hker
    exact (mul_eq_zero.mp hker).resolve_left hρp.ne'
  have hpN : ∀ j, pd j (fun y => ρ y * phaseNorm a ϑ y) p =
      pd j ρ p * phaseNorm a ϑ p + ρ p * pd j (phaseNorm a ϑ) p :=
    fun j => pd_mul hρ hNs p
  rw [Mgrad_smul_coeff hρ ha hW, quad_smul_coeff, hker0]
  simp only [hpN]
  have h0 := hstrict ξ hξ hker0
  have hNne : phaseNorm a ϑ p ≠ 0 := hN.ne'
  have hρne : ρ p ≠ 0 := hρp.ne'
  have e : (∑ j, ρ p * phaseField a ϑ j p *
      (pd j ρ p * phaseNorm a ϑ p + ρ p * pd j (phaseNorm a ϑ) p)) /
      (2 * (ρ p * phaseNorm a ϑ p)) =
      (∑ j, phaseField a ϑ j p * pd j ρ p) / 2 +
      ρ p * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) := by
    simp only [Fin.sum_univ_three]
    field_simp
    ring
  rw [e]
  have e2 : ρ p ^ 2 * Mgrad a (phaseField a ϑ) p ξ +
      4 * ρ p * (∑ i, ∑ l, a i l p * ξ l * pd i ρ p) * 0 -
      2 * ρ p * (∑ j, phaseField a ϑ j p * pd j ρ p) * quad a p ξ +
      4 * ((∑ j, phaseField a ϑ j p * pd j ρ p) / 2 +
        ρ p * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p))) *
        (ρ p * quad a p ξ) =
      ρ p ^ 2 * (Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) := by ring
  rw [e2]
  exact mul_pos (pow_pos hρp 2) h0

end StrictMargins

section MetricHessianCoordinates
variable {A G : Fin 3 → Fin 3 → R3 → ℝ} {ϑ : R3 → ℝ}

/-- J1: the coordinate metric Hessian `∂_i∂_jϑ − Σ_k Γ^k_ij ∂_kϑ`, with the Christoffel symbols
`Γ^k_ij = ½ Σ_l A_kl (∂_i G_jl + ∂_j G_il − ∂_l G_ij)` of `G` and its inverse `A`. -/
def christoffelHess (G A : Fin 3 → Fin 3 → R3 → ℝ) (ϑ : R3 → ℝ) (x : R3) (i j : Fin 3) : ℝ :=
  pd i (pd j ϑ) x - ∑ k, (∑ l, (1 / 2) * A k l x *
    (pd i (G j l) x + pd j (G i l) x - pd l (G i j) x)) * pd k ϑ x

/-- J1.2: the same Hessian through the phase field `W = A∇ϑ` (`A` symmetric). -/
theorem christoffelHess_eq (hsymm : ∀ i k, A i k = A k i) (x : R3) (i j : Fin 3) :
    christoffelHess G A ϑ x i j = pd i (pd j ϑ) x - (1 / 2) * ∑ l, phaseField A ϑ l x *
      (pd i (G j l) x + pd j (G i l) x - pd l (G i j) x) := by
  have h10 : ∀ y, A 1 0 y = A 0 1 y := fun y => congrFun (hsymm 1 0) y
  have h20 : ∀ y, A 2 0 y = A 0 2 y := fun y => congrFun (hsymm 2 0) y
  have h21 : ∀ y, A 2 1 y = A 1 2 y := fun y => congrFun (hsymm 2 1) y
  simp only [christoffelHess, phaseField, Fin.sum_univ_three, h10, h20, h21]
  ring

theorem pd_phaseField (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ) (i j : Fin 3)
    (x : R3) :
    pd i (phaseField A ϑ j) x =
      ∑ k, (pd i (A j k) x * pd k ϑ x + A j k x * pd i (pd k ϑ) x) := by
  show pd i (fun y => ∑ k, A j k y * pd k ϑ y) x = _
  rw [pd_sum (fun k => (hA j k).mul (contDiff_pd hϑ))]
  exact Finset.sum_congr rfl fun k _ => pd_mul (hA j k) (contDiff_pd hϑ) x

/-- J1.1: derivative of the phase field under the inverse differentiation rule at `x`. -/
theorem pd_phaseField_inverse (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (x : R3) (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (i j : Fin 3) :
    pd i (phaseField A ϑ j) x = ∑ k, A j k x * pd i (pd k ϑ) x -
      ∑ s, A j s x * ∑ t, pd i (G s t) x * phaseField A ϑ t x := by
  rw [pd_phaseField hA hϑ]
  simp only [hinvd, phaseField, Fin.sum_univ_three]
  ring

/-- J1.4a: derivative of the phase norm under the inverse differentiation rule at `x`. -/
theorem pd_phaseNorm_inverse (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : R3)
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (j : Fin 3) :
    pd j (phaseNorm A ϑ) x = 2 * ∑ i, phaseField A ϑ i x * pd j (pd i ϑ) x -
      ∑ s, ∑ t, phaseField A ϑ s x * phaseField A ϑ t x * pd j (G s t) x := by
  have hf : ∀ i k, ContDiff ℝ ∞ (fun y => A i k y * pd i ϑ y * pd k ϑ y) := fun i k =>
    ((hA i k).mul (contDiff_pd hϑ)).mul (contDiff_pd hϑ)
  have e1 : pd j (phaseNorm A ϑ) x = ∑ i, ∑ k, (pd j (A i k) x * pd i ϑ x * pd k ϑ x +
      A i k x * pd j (pd i ϑ) x * pd k ϑ x + A i k x * pd i ϑ x * pd j (pd k ϑ) x) := by
    show pd j (fun y => ∑ i, ∑ k, A i k y * pd i ϑ y * pd k ϑ y) x = _
    rw [pd_sum (fun i => ContDiff.sum fun k _ => hf i k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_sum (fun k => hf i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul ((hA i k).mul (contDiff_pd hϑ)) (contDiff_pd hϑ), pd_mul (hA i k) (contDiff_pd hϑ)]
    ring
  have h10 : ∀ y, A 1 0 y = A 0 1 y := fun y => congrFun (hsymm 1 0) y
  have h20 : ∀ y, A 2 0 y = A 0 2 y := fun y => congrFun (hsymm 2 0) y
  have h21 : ∀ y, A 2 1 y = A 1 2 y := fun y => congrFun (hsymm 2 1) y
  rw [e1]
  simp only [hinvd, phaseField, Fin.sum_univ_three, h10, h20, h21]
  ring

/-- J1.4: `W·∇N = 2 H(W,W)` for the actual coordinate metric Hessian. -/
theorem phaseField_dot_pd_phaseNorm (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : R3)
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x) :
    ∑ j, phaseField A ϑ j x * pd j (phaseNorm A ϑ) x =
      2 * ∑ i, ∑ j, christoffelHess G A ϑ x i j * phaseField A ϑ i x * phaseField A ϑ j x := by
  simp only [pd_phaseNorm_inverse hA hϑ hsymm x hinvd, christoffelHess_eq hsymm]
  simp only [Fin.sum_univ_three]
  ring

set_option maxHeartbeats 1600000 in
/-- J1.3: `Mgrad(A, A∇ϑ)(ξ) = 4 H(Y,Y)` with `Y = Aξ`, for the actual coordinate metric Hessian. -/
theorem Mgrad_inverse_eq_hess (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : R3)
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (ξ Y : Fin 3 → ℝ) (hY : ∀ i, Y i = ∑ l, A i l x * ξ l) :
    Mgrad A (phaseField A ϑ) x ξ = 4 * ∑ i, ∑ j, christoffelHess G A ϑ x i j * Y i * Y j := by
  have h10 : ∀ y, A 1 0 y = A 0 1 y := fun y => congrFun (hsymm 1 0) y
  have h20 : ∀ y, A 2 0 y = A 0 2 y := fun y => congrFun (hsymm 2 0) y
  have h21 : ∀ y, A 2 1 y = A 1 2 y := fun y => congrFun (hsymm 2 1) y
  simp only [christoffelHess_eq hsymm, hY]
  simp only [Mgrad, pd_phaseField_inverse hA hϑ x hinvd, hinvd]
  simp only [Fin.sum_univ_three, h10, h20, h21]
  ring

theorem bil_div (M : Fin 3 → Fin 3 → ℝ) (u w : Fin 3 → ℝ) (s : ℝ) :
    ∑ i, ∑ j, M i j * (u i / s) * (w j / s) = (∑ i, ∑ j, M i j * u i * w j) / s ^ 2 := by
  simp only [Fin.sum_univ_three]; ring

theorem lin_div (M : Fin 3 → Fin 3 → ℝ) (u w : Fin 3 → ℝ) (s : ℝ) :
    ∑ i, ∑ j, M i j * u i * (w j / s) = (∑ i, ∑ j, M i j * u i * w j) / s := by
  simp only [Fin.sum_univ_three]; ring

/-- J2: source metric strictness at ONE point (unit form `H(e,e) + H(v,v) > 0` for every
`g`-unit `v ⊥_g W`, `H(e,e) = H(W,W)/N`), with `G(p)A(p) = I`, `G(p) > 0`, `∇ϑ(p) ≠ 0` and the
inverse differentiation rule at `p`, PROVES `N(p) > 0` and the T9 point criterion for `A`. -/
theorem point_criterion_of_metric_strictness (hA : ∀ i k, ContDiff ℝ ∞ (A i k))
    (hϑ : ContDiff ℝ ∞ ϑ) (hsymm : ∀ i k, A i k = A k i) (p : R3)
    (hinvd : ∀ r i j, pd r (A i j) p = -∑ s, ∑ t, A i s p * pd r (G s t) p * A t j p)
    (hGA : ∀ i k, ∑ j, G i j p * A j k p = if i = k then 1 else 0)
    (hGpos : ∀ v : Fin 3 → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, G i j p * v i * v j)
    (hdϑ : (fun k => pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, G i j p * v i * v j = 1 →
      ∑ i, ∑ j, G i j p * phaseField A ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, christoffelHess G A ϑ p i j * phaseField A ϑ i p * phaseField A ϑ j p) /
          phaseNorm A ϑ p + ∑ i, ∑ j, christoffelHess G A ϑ p i j * v i * v j) :
    0 < phaseNorm A ϑ p ∧
    ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField A ϑ j p * ξ j = 0 →
      0 < Mgrad A (phaseField A ϑ) p ξ +
        4 * ((∑ j, phaseField A ϑ j p * pd j (phaseNorm A ϑ) p) / (2 * phaseNorm A ϑ p)) *
          quad A p ξ := by
  -- `Y = Aξ` solves `GY = ξ`
  have hGY : ∀ ξ Y : Fin 3 → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) →
      ∀ i, ∑ j, G i j p * Y j = ξ i := by
    intro ξ Y hY i
    simp only [hY]
    have e : ∑ j, G i j p * ∑ l, A j l p * ξ l = ∑ l, (∑ j, G i j p * A j l p) * ξ l := by
      simp only [Fin.sum_univ_three]; ring
    rw [e]
    simp [hGA]
  have hgYY : ∀ ξ Y : Fin 3 → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) →
      ∑ i, ∑ j, G i j p * Y i * Y j = quad A p ξ := by
    intro ξ Y hY
    have e : ∑ i, ∑ j, G i j p * Y i * Y j = ∑ i, Y i * ∑ j, G i j p * Y j := by
      simp only [Fin.sum_univ_three]; ring
    rw [e]
    simp only [hGY ξ Y hY]
    simp only [hY, quad, Fin.sum_univ_three]
    ring
  have hYne : ∀ ξ Y : Fin 3 → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) → ξ ≠ 0 → Y ≠ 0 := by
    intro ξ Y hY hξ h0
    apply hξ
    funext i
    rw [← hGY ξ Y hY i, h0]
    simp
  have hQpos : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < quad A p ξ := by
    intro ξ hξ
    have hY : ∀ i, (fun i => ∑ l, A i l p * ξ l) i = ∑ l, A i l p * ξ l := fun i => rfl
    rw [← hgYY ξ _ hY]
    exact hGpos _ (hYne ξ _ hY hξ)
  have hN : 0 < phaseNorm A ϑ p := hQpos _ hdϑ
  refine ⟨hN, fun ξ hξ hker => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin 3 → ℝ, ∀ i, Y i = ∑ l, A i l p * ξ l := ⟨_, fun i => rfl⟩
  rw [Mgrad_inverse_eq_hess hA hϑ hsymm p hinvd ξ Y hY,
    phaseField_dot_pd_phaseNorm hA hϑ hsymm p hinvd]
  have hc : 0 < quad A p ξ := hQpos ξ hξ
  set c := quad A p ξ with hcdef
  set s := Real.sqrt c with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hc
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc.le
  have hvv : ∑ i, ∑ j, G i j p * (Y i / s) * (Y j / s) = 1 := by
    rw [bil_div (fun i j => G i j p) Y Y s, hgYY ξ Y hY, hs2]
    exact div_self hc.ne'
  have hWv : ∑ i, ∑ j, G i j p * phaseField A ϑ i p * (Y j / s) = 0 := by
    rw [lin_div (fun i j => G i j p) (fun i => phaseField A ϑ i p) Y s]
    have e : ∑ i, ∑ j, G i j p * phaseField A ϑ i p * Y j =
        ∑ i, phaseField A ϑ i p * ∑ j, G i j p * Y j := by
      simp only [Fin.sum_univ_three]; ring
    rw [e]
    simp only [hGY ξ Y hY]
    rw [hker, zero_div]
  have h := hsrc (fun i => Y i / s) hvv hWv
  rw [bil_div (fun i j => christoffelHess G A ϑ p i j) Y Y s, hs2] at h
  set HWW := ∑ i, ∑ j, christoffelHess G A ϑ p i j * phaseField A ϑ i p * phaseField A ϑ j p
  set HYY := ∑ i, ∑ j, christoffelHess G A ϑ p i j * Y i * Y j
  have e : 4 * HYY + 4 * (2 * HWW / (2 * phaseNorm A ϑ p)) * c =
      4 * c * (HWW / phaseNorm A ϑ p + HYY / c) := by
    field_simp
    ring
  rw [e]
  exact mul_pos (mul_pos four_pos hc) h

end MetricHessianCoordinates

section LocalPhase
variable {a : Fin 3 → Fin 3 → R3 → ℝ}

/-- P: T9 for a phase that is smooth only on an open `Ω ∋ p`. The phase is globalized by a bump
(`Θ = χϑ`, equal to `ϑ` on `ball p ρ`); the estimate is returned for the ORIGINAL `ϑ` on a ball
inside `Ω`. No global smoothness of `ϑ` is assumed. -/
theorem local_strict_weight_carleman_of_local_phase (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : R3 → ℝ} {Ω : Set R3} (hΩ : IsOpen Ω)
    (hϑ : ContDiffOn ℝ ∞ ϑ Ω) (p : R3) (hp : p ∈ Ω)
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ Metric.closedBall p r ⊆ Ω ∧
      ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ p hp
  set ρ : ℝ := ε / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  let χ : ContDiffBump p := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  set Θ : R3 → ℝ := fun y => χ y * ϑ y with hΘdef
  -- global smoothness of the bumped phase
  have hsub : tsupport Θ ⊆ Ω := by
    refine (tsupport_mul_subset_left (f := fun y => χ y) (g := ϑ)).trans ?_
    have h1 : tsupport (fun y => χ y) = Metric.closedBall p (2 * ρ) := χ.tsupport_eq
    rw [h1]
    exact (Metric.closedBall_subset_ball (by linarith : 2 * ρ < ε)).trans hεΩ
  have hΘΩ : ContDiffOn ℝ ∞ Θ Ω := (χ.contDiff (n := ⊤)).contDiffOn.mul hϑ
  have hΘ : ContDiff ℝ ∞ Θ := by
    refine contDiff_of_contDiffOn_union_of_isOpen hΘΩ (t := (tsupport Θ)ᶜ)
      ((contDiffOn_const (c := (0 : ℝ))).congr fun x hx => image_eq_zero_of_notMem_tsupport hx)
      ?_ hΩ (isClosed_tsupport Θ).isOpen_compl
    ext x; by_cases hx : x ∈ tsupport Θ
    · simp [hsub hx]
    · simp [hx]
  -- `Θ = ϑ` on the open ball, hence all jets agree there
  have hEq : ∀ y ∈ Metric.ball p ρ, Θ y = ϑ y := fun y hy => by
    have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    simp only [hΘdef, h1, one_mul]
  have hpd1 : ∀ k, ∀ y ∈ Metric.ball p ρ, pd k Θ y = pd k ϑ y := fun k y hy => by
    unfold pd
    rw [(Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy) hEq).fderiv_eq]
  have hWb : ∀ j, ∀ y ∈ Metric.ball p ρ, phaseField a Θ j y = phaseField a ϑ j y :=
    fun j y hy => by simp only [phaseField, hpd1 _ y hy]
  have hNb : ∀ y ∈ Metric.ball p ρ, phaseNorm a Θ y = phaseNorm a ϑ y :=
    fun y hy => by simp only [phaseNorm, hpd1 _ y hy]
  have hpb : p ∈ Metric.ball p ρ := Metric.mem_ball_self hρ
  have hnhds : Metric.ball p ρ ∈ nhds p := Metric.isOpen_ball.mem_nhds hpb
  have hdW : ∀ i j, pd i (phaseField a Θ j) p = pd i (phaseField a ϑ j) p := fun i j => by
    unfold pd
    rw [(Filter.eventuallyEq_of_mem hnhds (hWb j)).fderiv_eq]
  have hdN : ∀ j, pd j (phaseNorm a Θ) p = pd j (phaseNorm a ϑ) p := fun j => by
    unfold pd
    rw [(Filter.eventuallyEq_of_mem hnhds hNb).fderiv_eq]
  have hMg : ∀ ξ, Mgrad a (phaseField a Θ) p ξ = Mgrad a (phaseField a ϑ) p ξ := fun ξ => by
    simp only [Mgrad, hdW, hWb _ p hpb]
  have hNΘ : 0 < phaseNorm a Θ p := by rw [hNb p hpb]; exact hN
  have hstrictΘ : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a Θ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a Θ) p ξ +
        4 * ((∑ j, phaseField a Θ j p * pd j (phaseNorm a Θ) p) / (2 * phaseNorm a Θ p)) *
          quad a p ξ := by
    intro ξ hξ hker
    simp only [hWb _ p hpb] at hker
    rw [hMg]
    simp only [hWb _ p hpb, hdN, hNb p hpb]
    exact hstrict ξ hξ hker
  obtain ⟨m, r0, C, τ0, hr0, hC, hτ0, hest⟩ :=
    local_strict_weight_carleman_of_point_strictness ha hsymm hΘ p hNΘ hstrictΘ
  set r : ℝ := min r0 (ρ / 2) with hrdef
  have hr : 0 < r := lt_min hr0 (half_pos hρ)
  have hrball : Metric.closedBall p r ⊆ Metric.ball p ρ :=
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans
      (Metric.closedBall_subset_ball (half_lt_self hρ))
  have hrΩ : Metric.closedBall p r ⊆ Ω :=
    hrball.trans ((Metric.ball_subset_ball (by linarith : ρ ≤ ε)).trans hεΩ)
  refine ⟨m, r, C, τ0, hr, hC, hτ0, hrΩ, fun τ hτ w hw hwc hKw => ?_⟩
  have h := hest τ hτ w hw hwc
    (hKw.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)))
  have hoff : ∀ y, y ∉ Metric.ball p ρ → y ∉ tsupport w := fun y hy hyw => hy (hrball (hKw hyw))
  have hfun : (fun y => Real.exp (τ * Θ y) * w y) = (fun y => Real.exp (τ * ϑ y) * w y) := by
    funext y
    by_cases hy : y ∈ Metric.ball p ρ
    · rw [hEq y hy]
    · simp [image_eq_zero_of_notMem_tsupport (hoff y hy)]
  have hres : ∀ x, Real.exp (2 * (τ * Θ x)) * Lop a w x ^ 2 =
      Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
    intro x
    by_cases hx : x ∈ Metric.ball p ρ
    · rw [hEq x hx]
    · have h0 := Sop_vanish (a := a) (X := fun _ _ => 0) (q := fun _ => 0) (θ := fun _ => 0) ha
        (fun _ => contDiff_const) contDiff_const contDiff_const hw (hoff x hx)
      have hL : Lop a w x = 0 := by simpa [Sop] using h0
      simp [hL]
  have hmass : ∀ x, (Real.exp (τ * Θ x) * w x) ^ 2 = (Real.exp (τ * ϑ x) * w x) ^ 2 :=
    fun x => by rw [congrFun hfun x]
  simp only [hfun, hmass, hres] at h
  exact h

end LocalPhase

end OAI.AnisotropicCalderon.StrictWeightCarleman

