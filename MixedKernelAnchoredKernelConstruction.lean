import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelPropagationAndAnnularSeries
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

/-- BOTH FULL original lower crosses for the SAME current series of the ORIGINAL `initialKernel`.
Second: every `x ∈ O1` with `lam • x ∈ W`, by product UCP on a small ball `B ∋ x` times `O2`
seeded by the ENTIRE first expansion on `O1 × S2`. First: on the connected component of `O1`
containing the separator point `p`, which meets scaled `W` (`hmeet`), by product UCP on
`C × Y` seeded by the full second agreement. `T` is never used as all of `W`. -/
theorem currentCrossKernel_full_crosses (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (D1 : Set R3) (hD1 : IsOpen D1) (K1 : Set R3) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2conn : IsConnected O2) (hO2D2 : O2 ⊆ D2)
    (hS2 : IsOpen S2) (hO2S2 : (O2 ∩ S2).Nonempty)
    (hobs : K1 ×ˢ S2 ⊆ initialCross S lam) (hbox : O1 ×ˢ O2 ⊆ dilatedOffDiagonal S lam)
    (p : R3) (hp : p ∈ O1) (hmeet : ∀ U : Set R3, IsOpen U → p ∈ U → ∃ x ∈ U, lam • x ∈ S.W)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CurrentCrossSeriesOn (initialKernel S lam) S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2
      K1i K2i γ1 γ2 ι w μ) :
    ProductSolutionOn S L lam
      (currentCrossKernel (initialKernel S lam) S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ)
      (O1 ×ˢ O2) ∧
    EqOn (currentCrossKernel (initialKernel S lam) S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ)
      (initialKernel S lam) (O1 ×ˢ S2) ∧
    (∀ x ∈ O1, lam • x ∈ S.W → ∀ y ∈ O2,
      currentCrossKernel (initialKernel S lam) S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ (x,y) =
        dilatedKernel2 S lam (x,y)) ∧
    (∀ x ∈ connectedComponentIn O1 p, ∀ y ∈ O2, lam • y ∈ S.W →
      currentCrossKernel (initialKernel S lam) S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ (x,y) =
        dilatedKernel1 S lam (x,y)) := by
  obtain ⟨-, hSol, hlow1, hlow2⟩ := v021_initial_cross_product S L lam hlam
  obtain ⟨_, _, t, _, _, _, _, ht, _⟩ :=
    currentCrossSeries_actual_limit (initialKernel S lam) S L lam D1 hD1 O1 hO1D1 T hTD1
      D2 O2 S2 w μ h
  set G := currentCrossKernel (initialKernel S lam) S lam D1 hD1 O1 hO1 hO1D1 T hTD1 w μ
  have hG : ProductSolutionOn S L lam G (O1 ×ˢ O2) :=
    currentCrossKernel_productSolutionOn _ S L lam D1 hD1 O1 hO1 hO1D1 T hTD1
      D2 O2 S2 hO2 hO2D2 w μ h t ht
  have hfirst : EqOn G (initialKernel S lam) (O1 ×ˢ S2) :=
    currentCrossKernel_first_eqOn _ S L lam _ hSol D1 hD1 K1 hK1 hD1K1
      O1 hO1 hO1D1 T hTD1 S2 hobs w μ h.1
  obtain ⟨h2,h1⟩ := native_kernel_full_crosses S L lam hlam O1 hO1 O2 hO2 hO2conn
    S2 hS2 hO2S2 hbox p hp hmeet G hG hfirst
  exact ⟨hG,hfirst,h2,h1⟩

/-- ACTUAL annular seed: the SAME current series of the ORIGINAL `initialKernel` (Root's
compact first arm with `beta = gamma2`, retained rooms) is a smooth scalar solving BOTH literal
native PDEs on the open product `C × O2`, `C` the separator component of `O1`, with BOTH FULL
original lower-cross identities. `a, lam0` precede `L, lam, p, s`; `hJSW` remains the
same explicit observed-buffer input as in `initial_cross_series_annulus`. -/
theorem initial_full_cross_kernel_annulus (S : KnownSideSourceData) (Bp s1 : ℝ) (hBp : 0 ≤ Bp)
    (hs1 : 0 < s1) :
    ∃ a lam0 : ℝ, 0 < a ∧ 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ Bp →
      lam • p ∈ Metric.ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ s : ℝ, 0 < s → s ≤ s1 →
      (∀ y ∈ Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8),
        lam • y ∈ S.W) →
      ∃ (C : Set R3) (K : R3 × R3 → ℝ),
        IsOpen C ∧ IsConnected C ∧ p ∈ C ∧ C ⊆ Metric.ball p (s/4) ∧
        C ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ⊆ dilatedOffDiagonal S lam ∧
        ProductSolutionOn S L lam K (C ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}) ∧
        (∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}, lam • v.2 ∈ S.W →
          K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}, lam • v.1 ∈ S.W →
          K v = dilatedKernel2 S lam v) := by
  obtain ⟨a1, ha1, H1⟩ := native_first_known_side_compact_arm_near_one S
  obtain ⟨a2, ha2, H2⟩ := known_side_meets_open_at_separator S
  obtain ⟨lam0, hlam0, HR⟩ := exists_uniform_annulus_coordinateRoom S Bp s1 hBp hs1
  refine ⟨min a1 a2, lam0, lt_min ha1 ha2, hlam0, ?_⟩
  intro L lam hlam hle p hp hpa hp0 s hs hss hJSW
  have hpa1 : lam • p ∈ Metric.ball (0 : R3) a1 :=
    Metric.ball_subset_ball (min_le_left _ _) hpa
  have hpa2 : lam • p ∈ Metric.ball (0 : R3) a2 :=
    Metric.ball_subset_ball (min_le_right _ _) hpa
  obtain ⟨K2i, γ2, -, hγ2, hγ21, HB⟩ := secondCoefficientInterpolation_annulus S L lam p s hs
  obtain ⟨D, O, T, K1, KT, Kint, gamma, hD, hDc, hO, hpO, hOD, hT, hTne, hK1, hKT, hDK1, hTKT,
      hKTD, hK1b, hK1room, -, hKTW, hgam, -, hKint, HA⟩ :=
    H1 lam hlam p hpa1 hp0 (s/4) (by positivity) γ2 hγ2 hγ21.le
  obtain ⟨hΩ, hSol, -⟩ := v021_initial_cross_product S L lam hlam
  have hroom : ∀ y : R3, s/2 ≤ ‖y-p‖ → ‖y-p‖ ≤ 2*s → lam • y ∈ S.coordinateRoom :=
    fun y h1 h2 => HR lam hlam hle p hp s hss y h1 h2
  obtain ⟨hrow, hobs⟩ := initialCross_annulus_cross_data S lam p s (s/4) hs le_rfl hroom hJSW
    K1 KT hK1b (hKTD.trans hDK1) hK1room hKTW
  obtain ⟨hDo, -, hO2o, hO2c, -, hOK, hKD, hcirc⟩ := native_annulus_target_geometry p s hs
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms_sum (initialKernel S lam) S L lam
    (initialCross S lam) hΩ hSol D O T K1 KT
    {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s} {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
    {y : R3 | s/2 ≤ ‖y-p‖ ∧ ‖y-p‖ ≤ 2*s}
    (Metric.closedBall (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
    hD hDc hOD hT hTne hKT hTKT hKTD (hTKT.trans hKTD) hK1 hDK1 hDo (hOK.trans hKD)
    Metric.isOpen_ball (isCompact_native_closed_annulus p (s/2) (2*s))
    (fun y hy => ⟨hy.1.le, hy.2.le⟩) (isCompact_closedBall _ _) Metric.ball_subset_closedBall
    hrow hobs hKint (by linarith) HA HB
  have hobs' : K1 ×ˢ Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8) ⊆
      initialCross S lam :=
    (prod_mono subset_rfl Metric.ball_subset_closedBall).trans hobs
  have hOball : O ⊆ Metric.ball p (s/4) := (hOD.trans hDK1).trans hK1b
  have hbox : O ×ˢ {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ⊆ dilatedOffDiagonal S lam := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' : 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5 := hy
    have hxp : ‖x-p‖ < s/4 := by
      have hxb := hOball hx
      rwa [Metric.mem_ball, dist_eq_norm] at hxb
    refine ⟨hK1room x (hDK1 (hOD hx)), hroom y (by linarith [hy'.1]) (by linarith [hy'.2]), ?_⟩
    intro hxy
    have hxy' : x = y := hxy
    rw [hxy'] at hxp
    linarith [hy'.1]
  have hcp : ‖(p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))-p‖ = s := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    simp
  have hO2S2 : ({y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5} ∩
      Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8)).Nonempty :=
    ⟨p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ), hcirc _ hcp,
      Metric.mem_ball_self (by positivity)⟩
  obtain ⟨hG, -, h2, h1⟩ := currentCrossKernel_full_crosses S L lam hlam D hD K1 hK1 hDK1
    O hO hOD T (hTKT.trans hKTD) {y : R3 | s/2 < ‖y-p‖ ∧ ‖y-p‖ < 2*s}
    {y : R3 | 4*s/5 < ‖y-p‖ ∧ ‖y-p‖ < 6*s/5}
    (Metric.ball (p-s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/8))
    hO2o hO2c (hOK.trans hKD) Metric.isOpen_ball hO2S2
    hobs' hbox p hpO (fun U hU hpU => H2 lam hlam p hpa2 hp0 U hU hpU) w μ hser
  have hCO : connectedComponentIn O p ⊆ O := connectedComponentIn_subset O p
  refine ⟨connectedComponentIn O p, _, hO.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hpO, mem_connectedComponentIn hpO,
    hCO.trans hOball, (prod_mono hCO subset_rfl).trans hbox,
    productSolutionOn_mono hG (prod_mono hCO subset_rfl), ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩ hyW
    exact h1 x hx y hy hyW
  · rintro ⟨x, y⟩ ⟨hx, hy⟩ hxW
    exact h2 x (hCO hx) hxW y hy

/-- Anchored full-cross seed: ONE `lam0` before `L, lam, p, s`; centred at the ACTUAL original
separator anchor `q = p + t e₂`, the observed buffer in ORIGINAL `W` supplied by Root's uniform
near-plane lower buffers. No remaining internal input. -/
theorem initial_full_cross_kernel_anchor (S : KnownSideSourceData) (B s0 s1 : ℝ) (hB : 0 < B)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ p : R3, ‖p‖ ≤ B → p 2 = 0 →
      ∀ s ∈ Set.Icc s0 s1, ∃ t ∈ Set.Ioo (-(s0/4)) (s0/4),
        S.separating_function (lam • (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 ∧
      ∃ (C : Set R3) (K : R3 × R3 → ℝ),
        IsOpen C ∧ IsConnected C ∧ p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) ∈ C ∧
        C ⊆ Metric.ball (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) (s/4) ∧
        C ×ˢ {y : R3 | 4*s/5 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
          ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*s/5} ⊆
          dilatedOffDiagonal S lam ∧
        ProductSolutionOn S L lam K
          (C ×ˢ {y : R3 | 4*s/5 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
            ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*s/5}) ∧
        (∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
            ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*s/5},
          lam • v.2 ∈ S.W → K v = dilatedKernel1 S lam v) ∧
        (∀ v ∈ C ×ˢ {y : R3 | 4*s/5 < ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
            ‖y-(p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*s/5},
          lam • v.1 ∈ S.W → K v = dilatedKernel2 S lam v) := by
  obtain ⟨a, lamI, ha, hlamI, HI⟩ :=
    initial_full_cross_kernel_annulus S (B + s0/4) s1 (by positivity) (hs0.trans_le hss)
  obtain ⟨lamA, hlamA, HA⟩ :=
    exists_uniform_actual_separating_surface_anchors S B (s0/4) a hB (by positivity) ha
  obtain ⟨lamW, hlamW, HW⟩ :=
    exists_uniform_native_annulus_near_plane_lower_buffers S (B + s0/4) s0 s1 (by positivity)
      hs0 hss
  refine ⟨min lamI (min lamA lamW), lt_min hlamI (lt_min hlamA hlamW), ?_⟩
  intro L lam hlam hle p hp hp2 s hs
  have h1 : lam ≤ lamI := hle.trans (min_le_left _ _)
  have h2 : lam ≤ lamA := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : lam ≤ lamW := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨t, ht, htn, hta, ht0⟩ := HA lam hlam h2 p hp hp2
  have hqn : ‖p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ B + s0/4 := by
    have := norm_sub_norm_le (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p
    linarith
  have hq2 : (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 ≤ s0/4 := by
    have : (p + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) 2 = t := by simp [hp2]
    rw [this]
    exact ht.2.le
  exact ⟨t, ht, ht0, HI L lam hlam h1 _ hqn hta ht0 s (hs0.trans_le hs.1) hs.2
    (HW lam hlam h3 _ hqn hq2 s hs)⟩

/-- Compatible overlap UCP: two product solutions with BOTH original lower crosses agree on
every component of their common open domain that meets the original known cross. -/
theorem lowerCross_solutions_eqOn (S : KnownSideSourceData) (L lam : ℝ)
    {Ω : Set (R3 × R3)} (hΩ : IsOpen Ω) {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F Ω) (hG : ProductSolutionOn S L lam G Ω)
    (hF1 : ∀ v ∈ Ω, lam • v.2 ∈ S.W → F v = dilatedKernel1 S lam v)
    (hF2 : ∀ v ∈ Ω, lam • v.1 ∈ S.W → F v = dilatedKernel2 S lam v)
    (hG1 : ∀ v ∈ Ω, lam • v.2 ∈ S.W → G v = dilatedKernel1 S lam v)
    (hG2 : ∀ v ∈ Ω, lam • v.1 ∈ S.W → G v = dilatedKernel2 S lam v)
    (hmeet : ∀ z ∈ Ω, (connectedComponentIn Ω z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty) :
    EqOn F G Ω := by
  exact native_lowerCross_solutions_eqOn S L lam hΩ hF hG hF1 hF2 hG1 hG2 hmeet

/-- Common seed: pairwise-overlap components meeting the known cross glue the local
full-cross solutions into ONE literal product solution with BOTH original lower crosses. -/
theorem exists_common_lowerCross_kernel (S : KnownSideSourceData) (L lam : ℝ)
    {ι : Type*} (U : ι → Set (R3 × R3)) (hU : ∀ i, IsOpen (U i))
    (F : ι → R3 × R3 → ℝ) (hF : ∀ i, ProductSolutionOn S L lam (F i) (U i))
    (hF1 : ∀ i, ∀ v ∈ U i, lam • v.2 ∈ S.W → F i v = dilatedKernel1 S lam v)
    (hF2 : ∀ i, ∀ v ∈ U i, lam • v.1 ∈ S.W → F i v = dilatedKernel2 S lam v)
    (hmeet : ∀ i j, ∀ z ∈ U i ∩ U j, (connectedComponentIn (U i ∩ U j) z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty) :
    ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H (⋃ i, U i) ∧
      (∀ v ∈ ⋃ i, U i, lam • v.2 ∈ S.W → H v = dilatedKernel1 S lam v) ∧
      (∀ v ∈ ⋃ i, U i, lam • v.1 ∈ S.W → H v = dilatedKernel2 S lam v) ∧
      ∀ i, EqOn H (F i) (U i) := by
  exact exists_native_common_lowerCross_kernel S L lam U hU F hF hF1 hF2 hmeet

/-- Assembly of the ORIGINAL output structure from a compatible full-cross family. The two
coverage facts and the overlap-component condition are the explicit INTERNAL obligations that
remain (not original premises). -/
theorem constructedMixedKernel_of_lowerCross_family (S : KnownSideSourceData)
    (L lam delta Rstar bound separation : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    {ι : Type*} (U : ι → Set (R3 × R3)) (hU : ∀ i, IsOpen (U i))
    (hroom : ∀ i, U i ⊆ dilatedOffDiagonal S lam)
    (F : ι → R3 × R3 → ℝ) (hF : ∀ i, ProductSolutionOn S L lam (F i) (U i))
    (hF1 : ∀ i, ∀ v ∈ U i, lam • v.2 ∈ S.W → F i v = dilatedKernel1 S lam v)
    (hF2 : ∀ i, ∀ v ∈ U i, lam • v.1 ∈ S.W → F i v = dilatedKernel2 S lam v)
    (hmeet : ∀ i j, ∀ z ∈ U i ∩ U j, (connectedComponentIn (U i ∩ U j) z ∩
      {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W}).Nonempty)
    (hsphere : ∀ k, ∀ y ∈ cylinder ∩ (cover.packet k).centers, ∀ z ∈ sphere (0 : R3) 1,
      (packetEndpoint S L (cover.packet k) lam y (referenceRadius delta Rstar p L y) z, y) ∈
        ⋃ i, U i)
    (hfixed : fixedSeparationSet bound separation ⊆ ⋃ i, U i) :
    Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p cover) := by
  exact constructedMixedKernel_of_native_lowerCross_family S L lam delta Rstar bound separation p cover U hU hroom F hF hF1 hF2 hmeet hsphere hfixed

/-- The anchored full-cross seeds as ONE family indexed by all bounded plane points and scales,
with one `lam0` before `L, lam`: exactly the per-member hypotheses of
`constructedMixedKernel_of_lowerCross_family`; each member contains `{q} × O2(q,s)`. -/
theorem anchored_full_cross_family (S : KnownSideSourceData) (B s0 s1 : ℝ) (hB : 0 < B)
    (hs0 : 0 < s0) (hss : s0 ≤ s1) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∃ (U : {ps : R3 × ℝ // ‖ps.1‖ ≤ B ∧ ps.1 2 = 0 ∧ ps.2 ∈ Set.Icc s0 s1} → Set (R3 × R3))
        (F : {ps : R3 × ℝ // ‖ps.1‖ ≤ B ∧ ps.1 2 = 0 ∧ ps.2 ∈ Set.Icc s0 s1} → R3 × R3 → ℝ),
        (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ dilatedOffDiagonal S lam) ∧
        (∀ i, ProductSolutionOn S L lam (F i) (U i)) ∧
        (∀ i, ∀ v ∈ U i, lam • v.2 ∈ S.W → F i v = dilatedKernel1 S lam v) ∧
        (∀ i, ∀ v ∈ U i, lam • v.1 ∈ S.W → F i v = dilatedKernel2 S lam v) ∧
        ∀ i, ∃ t ∈ Set.Ioo (-(s0/4)) (s0/4),
          S.separating_function
            (lam • (i.1.1 + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) = 0 ∧
          ∀ y : R3, 4*i.1.2/5 < ‖y-(i.1.1 + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ →
            ‖y-(i.1.1 + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*i.1.2/5 →
            (i.1.1 + t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ), y) ∈ U i := by
  obtain ⟨lam0, hlam0, HA⟩ := initial_full_cross_kernel_anchor S B s0 s1 hB hs0 hss
  refine ⟨lam0, hlam0, fun L lam hlam hle => ?_⟩
  have H := fun i : {ps : R3 × ℝ // ‖ps.1‖ ≤ B ∧ ps.1 2 = 0 ∧ ps.2 ∈ Set.Icc s0 s1} =>
    HA L lam hlam hle i.1.1 i.2.1 i.2.2.1 i.1.2 i.2.2.2
  choose t ht hsep C K hC hCc hqC hCb hroom hsol h1 h2 using H
  refine ⟨fun i => C i ×ˢ {y : R3 | 4*i.1.2/5 <
      ‖y-(i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ ∧
      ‖y-(i.1.1 + t i • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))‖ < 6*i.1.2/5},
    K, fun i => (hC i).prod (isOpen_native_annulus _ _ _), hroom, hsol, h1, h2,
    fun i => ⟨t i, ht i, hsep i, fun y hy1 hy2 => ⟨hqC i, hy1, hy2⟩⟩⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
