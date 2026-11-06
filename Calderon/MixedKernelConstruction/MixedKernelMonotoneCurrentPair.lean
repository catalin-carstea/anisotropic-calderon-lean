import Calderon.MixedKernelConstruction.MixedKernelPhaseHeightRooms
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

/-- Same joint-criterion producer, with actual connected output/observation geometry derived. -/
theorem current_common_pair_from_product_hessian_monotone
    (S : KnownSideSourceData) (L lam : ℝ) (p1 p2 : R3)
    (U : Set (R3 × R3)) (hU : IsOpen U) (hpU : (p1,p2) ∈ U)
    (rho : R3 × R3 → ℝ) (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho (p1,p2) = 0)
    (hTest : ProductHessianStrictAt (fun x => S.g1 (lam • x))
      (fun y => S.g2 (lam • y)) p1 p2 rho)
    (F : R3 × R3 → ℝ)
    (hSol : ProductSolutionOn S L lam F {z | z ∈ U ∧ 0 < rho z}) :
    ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
      (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (K1i K2i γ1 γ2 : ℝ),
      CurrentNativePairFacts U rho p1 p2 D1 O1 T D2 O2 S2 K1i K2i γ1 γ2 ∧
      IsConnected O1 ∧ IsConnected O2 ∧ (O1 ∩ T).Nonempty ∧ (O2 ∩ S2).Nonempty ∧
      SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2 ∧
      FirstBasisArmOn S lam D1 O1 T K1i γ1 ∧
      ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ ∧
      ∃ (ell2 : R3 →L[ℝ] ℝ) (e2 : OpenPartialHomeomorph R3 (ℝ × ell2.ker)) (l eps R : ℝ),
        0 < eps ∧ 4 * eps < l ∧ 0 < R ∧
        O2 = e2.symm '' PhaseCoordinates.roomO l eps R ∧
        S2 = e2.symm '' (PhaseCoordinates.roomStop l eps R ∪ PhaseCoordinates.roomSlat l eps R) ∧
        PhaseCoordinates.closedD l eps R ⊆ e2.target ∧
        ∀ x ∈ O1, ∀ z ∈ Metric.ball (0 : ell2.ker) (R/2),
          MonotoneOn (fun t : ℝ => rho (x,e2.symm (t,z))) (Ioo (-eps) (l+3*eps/2)) := by
  have hgs1 : ∀ i j, ContDiff ℝ ∞ (fun x => S.g1 (lam • x) i j) :=
    fun i j => (S.g1_admissible.smooth i j).comp (contDiff_id.const_smul lam)
  have hgs2 : ∀ i j, ContDiff ℝ ∞ (fun y => S.g2 (lam • y) i j) :=
    fun i j => (S.g2_admissible.smooth i j).comp (contDiff_id.const_smul lam)
  obtain ⟨θ1, θ2, c, r, K, hθ1, hθ2, h01, h02, hFirst1, hFirst2, hd1, hd2,
      hsrc1, hsrc2, hc, hr, hK, hRoom, hgap, hside⟩ :=
    exists_native_product_strict_phases_smooth (fun x => S.g1 (lam • x))
      (fun y => S.g2 (lam • y)) hgs1 (fun x => S.g1_admissible.posDef (lam • x))
      hgs2 (fun y => S.g2_admissible.posDef (lam • y)) p1 p2 U hU hpU rho hrho hrho0 hTest
  obtain ⟨e1, he1, hcenter1, κ1, hκ1, H1⟩ :=
    native_first_basis_arm_prescribed_phase S lam hθ1 p1 h01 hd1 hsrc1 (r / 2) (half_pos hr)
  obtain ⟨e2, he2, hcenter2, κ2, hκ2, H2⟩ :=
    native_second_coefficient_arm_prescribed_phase S L lam hθ2 p2 h02 hd2 hsrc2 (r / 2) (half_pos hr)
  have hell2 : fderiv ℝ θ2 p2 ≠ 0 := by
    intro h
    apply hd2
    funext k
    simp only [pd, h, ContinuousLinearMap.zero_apply, Pi.zero_apply]
  have htarget1 : (0 : ℝ × (fderiv ℝ θ1 p1).ker) ∈ e1.target := by
    have hp := e1.map_source hcenter1.1
    rw [he1 p1, h01, sub_self, map_zero] at hp
    exact hp
  have htarget2 : (0 : ℝ × (fderiv ℝ θ2 p2).ker) ∈ e2.target := by
    have hp := e2.map_source hcenter2.1
    rw [he2 p2, h02, sub_self, map_zero] at hp
    exact hp
  have hInv2 := tangent_phase_chart_inverse_contDiffAt θ2 hθ2 p2 (fderiv ℝ θ2 p2)
    (hθ2.hasStrictFDerivAt (by simp)) hell2 h02 e2 hcenter2.1 he2
  obtain ⟨V,hVo,hVp,hV⟩ := exists_positive_second_chart_height_neighborhood rho θ2 p1 p2
    (fderiv ℝ θ2 p2) ((hrho.contDiffAt (hU.mem_nhds hpU)).of_le (by simp))
    ((hθ2.differentiable (by simp)) p2).hasFDerivAt hFirst2.symm e2 htarget2 hcenter2.2 he2 hInv2
  obtain ⟨ρ0,hρ0,hsmall⟩ := exists_chart_product_closedD_neighborhood e1 p1
    htarget1 hcenter1.2 V hVo hVp
  have hκ : 0 < min κ1 κ2 := lt_min hκ1 hκ2
  obtain ⟨ρ1, hρ1, G1⟩ := H1 (min κ1 κ2) hκ (min_le_left _ _)
  obtain ⟨ρ2, hρ2, G2⟩ := H2 (min κ1 κ2) hκ (min_le_right _ _)
  obtain ⟨l, ε, R, hε, hl5, hR, hlρ, hRρ, hκl, hεκ, hlR⟩ :=
    exists_slack_params hκ (lt_min (lt_min hρ1 hρ2) hρ0) (div_pos hc (by norm_num : (0 : ℝ) < 4))
  obtain ⟨⟨hl, hlρ1, hRρ1, hκ1', hε1, -⟩, -, -, -⟩ :=
    slack_params_mono hκ ((min_le_left (min ρ1 ρ2) ρ0).trans (min_le_left ρ1 ρ2)) (le_refl (c / 4))
      hε hl5 hR hlρ hRρ hκl hεκ hlR
  obtain ⟨⟨-, hlρ2, hRρ2, hκ2', hε2, -⟩, -, -, -⟩ :=
    slack_params_mono hκ ((min_le_left (min ρ1 ρ2) ρ0).trans (min_le_right ρ1 ρ2)) (le_refl (c / 4))
      hε hl5 hR hlρ hRρ hκl hεκ hlR
  obtain ⟨hloc1, hDt1, hDo1, hOD1, hSD1, hg11, hg12, K1i, hK1i, HA⟩ :=
    G1 l ε R hε hl hR hlρ1 hRρ1 hκ1' hε1
  obtain ⟨hloc2, hDt2, hDo2, hOD2, hSD2, hg21, hg22, K2i, hK2i, HB2⟩ :=
    G2 l ε R hε hl hR hlρ2 hRρ2 hκ2' hε2
  obtain ⟨hK1, hKT, hKTK1, hTKT, hD1K1⟩ := closedRooms_isCompact e1 hε hl hR hDt1
  obtain ⟨hJ2, hJS, hJSJ2, hS2JS, hD2J2⟩ := closedRooms_isCompact e2 hε hl hR hDt2
  obtain ⟨hconn1, hO1o, hTo, hTne, hKTD1⟩ := chart_room_facts e1 hε hl hR hDt1
  obtain ⟨hconn2, hO2o, hS2o, hS2ne, hJSD2⟩ := chart_room_facts e2 hε hl hR hDt2
  obtain ⟨hO1conn,hO1T⟩ := chart_output_connected_meets_observation e1 hε hl hR hDt1
  obtain ⟨hO2conn,hO2S⟩ := chart_output_connected_meets_observation e2 hε hl hR hDt2
  have hp1O := chart_room_contains_center e1 hcenter1.2 hε hl hR
  have hp2O := chart_room_contains_center e2 hcenter2.2 hε hl hR
  have hball : (e1.symm '' PhaseCoordinates.closedD l ε R) ×ˢ
      (e2.symm '' PhaseCoordinates.closedD l ε R) ⊆ Metric.closedBall (p1,p2) r :=
    product_closed_rooms_subset_closedBall
      (hloc1.trans ((Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall))
      (hloc2.trans ((Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall))
  have h2l : 2 * l ≤ c * R ^ 2 / 18 := by nlinarith
  obtain ⟨η, hη, hmargin⟩ := closed_native_cross_positive_margin e1 e2 he1 he2
    (fun v => Submodule.norm_orthogonalProjectionOnto_apply_le _ v)
    (fun v => Submodule.norm_orthogonalProjectionOnto_apply_le _ v)
    hc hε hl hR hK.le h2l hDt1 hDt2 rho
    (fun x hx y hy => by have h := hgap (x,y) (hball ⟨hx,hy⟩); linarith)
    (fun x hx y hy => hside (x,y) (hball ⟨hx,hy⟩))
  have hΩ : IsOpen {z : R3 × R3 | z ∈ U ∧ 0 < rho z} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact Filter.inter_mem (hU.mem_nhds hz.1)
      ((hrho.contDiffAt (hU.mem_nhds hz.1)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hz.2))
  have hrow : (e1.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R)) ×ˢ
      (e2.symm '' PhaseCoordinates.closedD l ε R) ⊆ {z | z ∈ U ∧ 0 < rho z} := by
    intro z hz
    exact ⟨hRoom (hball ⟨hKTK1 hz.1,hz.2⟩), hη.trans_le (hmargin z (Or.inr hz))⟩
  have hobs : (e1.symm '' PhaseCoordinates.closedD l ε R) ×ˢ
      (e2.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R)) ⊆
      {z | z ∈ U ∧ 0 < rho z} := by
    intro z hz
    exact ⟨hRoom (hball ⟨hz.1,hJSJ2 hz.2⟩), hη.trans_le (hmargin z (Or.inl hz))⟩
  have HB : SecondCoefficientInterpolationOn S L lam (e2.symm '' PhaseCoordinates.roomD l ε R)
      (e2.symm '' PhaseCoordinates.roomO l ε R)
      (e2.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) K2i
      ((strictHeight (min κ1 κ2) (-ε) - strictHeight (min κ1 κ2) (-l + 3 * ε)) /
        (strictHeight (min κ1 κ2) (l + 3 * ε) - strictHeight (min κ1 κ2) (-l + 3 * ε))) :=
    fun b hb hP bD bO bS h1 h2 h3 M μ hμ hM hS hD =>
      (HB2 b hb hP bD bO bS h1 h2 h3 M μ hμ hM hS hD).1
  obtain ⟨ι, w, μ, hser⟩ := current_cross_series_of_rooms F S L lam _ hΩ hSol
    _ _ _ _ _ _ _ _ _ _ hDo1 hconn1 hOD1 hTo hTne hKT hTKT hKTD1 hSD1 hK1 hD1K1
    hDo2 hOD2 hS2o hJ2 hD2J2 hJS hS2JS hrow hobs hK1i hg11 hg21 HA HB
  refine ⟨_, hDo1, _, hOD1, _, hSD1, _, _, _, K1i, K2i, _, _,
    ⟨hDo1, hconn1, hO1o, hp1O, hOD1, hTo, hTne, hSD1,
      hDo2, hconn2, hO2o, hp2O, hOD2, hS2o, hS2ne, hSD2,
      hK1i, hK2i, hg11, hg12, hg21, hg22,
      _, _, _, _, η, hK1, hKT, hJ2, hJS, hD1K1, hTKT, hKTD1, hD2J2, hS2JS, hJSD2,
      fun z hz => hRoom (hball hz), hη, hmargin⟩, hO1conn, hO2conn, hO1T, hO2S, HB, HA, ι, w, μ, hser,
      fderiv ℝ θ2 p2, e2, l, ε, R, hε, hl, hR, rfl, rfl, hDt2, ?_⟩
  intro x hx
  obtain ⟨u1,hu1,rfl⟩ := hx
  apply monotone_phase_height_on_roomO rho e2 (e1.symm u1) l ε R
  intro q hq
  have hu1D : u1 ∈ PhaseCoordinates.closedD l ε R :=
    PhaseCoordinates.roomD_subset_closedD
      (PhaseCoordinates.closedO_subset_roomD hε hl hR
        (PhaseCoordinates.roomO_subset_closedO hu1))
  have hqD : q ∈ PhaseCoordinates.closedD l ε R :=
    PhaseCoordinates.roomD_subset_closedD
      (PhaseCoordinates.closedO_subset_roomD hε hl hR
        (PhaseCoordinates.roomO_subset_closedO hq))
  exact hV _ (hsmall l ε R hε
    (by have hs := hlρ.trans (min_le_right (min ρ1 ρ2) ρ0); linarith)
    (by have hs := hRρ.trans (min_le_right (min ρ1 ρ2) ρ0); linarith) u1 hu1D q hqD)


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
