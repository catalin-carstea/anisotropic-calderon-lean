import MixedKernelCurrentCommonPair
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

/-- The actual output cylinder is connected and meets its actual observation collar. -/
theorem chart_output_connected_meets_observation {θ : R3 → ℝ} {p : R3}
    (e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker)) {l ε R : ℝ}
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target) :
    IsConnected (e.symm '' PhaseCoordinates.roomO l ε R) ∧
    ((e.symm '' PhaseCoordinates.roomO l ε R) ∩
      (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))).Nonempty := by
  have hOT : (PhaseCoordinates.roomO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    PhaseCoordinates.roomO_subset_closedO.trans
      ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
        (PhaseCoordinates.roomD_subset_closedD.trans hDt))
  have hconv : Convex ℝ (PhaseCoordinates.roomO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) :=
    (convex_Ioo _ _).prod (convex_ball _ _)
  have hne : (PhaseCoordinates.roomO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)).Nonempty :=
    ⟨(0,0),⟨⟨by linarith,by linarith⟩,Metric.mem_ball_self (half_pos hR)⟩⟩
  have htopO : ((l+ε,0) : ℝ × (fderiv ℝ θ p).ker) ∈ PhaseCoordinates.roomO l ε R :=
    ⟨⟨by linarith,by linarith⟩,Metric.mem_ball_self (half_pos hR)⟩
  have htopS : ((l+ε,0) : ℝ × (fderiv ℝ θ p).ker) ∈
      PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R :=
    Or.inl ⟨⟨by linarith,by linarith⟩,Metric.mem_ball_self (by positivity)⟩
  exact ⟨(hconv.isConnected hne).image _ (e.continuousOn_symm.mono hOT),
    ⟨e.symm (l+ε,0),mem_image_of_mem _ htopO,mem_image_of_mem _ htopS⟩⟩

/-- Existing product UCP propagates first-arm equality through the connected second room. -/
theorem native_product_eq_from_second_seed (S : KnownSideSourceData) (L lam : ℝ)
    (U1 U2 V V0 : Set R3) (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (hV : IsOpen V) (hVc : IsConnected V) (hV0 : IsOpen V0) (hV0ne : V0.Nonempty)
    (hV0V : V0 ⊆ V) (F G : R3 × R3 → ℝ)
    (hF : ProductSolutionOn S L lam F (U1 ×ˢ V))
    (hG : ProductSolutionOn S L lam G (U2 ×ˢ V))
    (heq : EqOn F G ((U1 ∩ U2) ×ˢ V0)) : EqOn F G ((U1 ∩ U2) ×ˢ V) := by
  intro z hz
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hU1.inter hU2) z.1 hz.1
  have hb1 : ball z.1 r ⊆ U1 := fun x hx => (hball hx).1
  have hb2 : ball z.1 r ⊆ U2 := fun x hx => (hball hx).2
  have hbn : (ball z.1 r).Nonempty := ⟨z.1,mem_ball_self hr⟩
  have hbc : IsConnected (ball z.1 r) := (convex_ball z.1 r).isConnected hbn
  have h := native_product_eq_of_eq_on_box S L lam isOpen_ball hbc hV hVc
    (productSolutionOn_mono hF (prod_mono hb1 subset_rfl))
    (productSolutionOn_mono hG (prod_mono hb2 subset_rfl))
    isOpen_ball hbn subset_rfl hV0 hV0ne hV0V
    (fun x hx y hy => heq ⟨hball hx,hy⟩)
  exact h z.1 (mem_ball_self hr) z.2 hz.2


/-- Same joint-criterion producer, with actual connected output/observation geometry derived. -/
theorem current_common_pair_from_product_hessian_connected
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
        CurrentCrossSeriesOn F S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  have hgs1 : ∀ i j, ContDiff ℝ ∞ (fun x => S.g1 (lam • x) i j) :=
    fun i j => (S.g1_admissible.smooth i j).comp (contDiff_id.const_smul lam)
  have hgs2 : ∀ i j, ContDiff ℝ ∞ (fun y => S.g2 (lam • y) i j) :=
    fun i j => (S.g2_admissible.smooth i j).comp (contDiff_id.const_smul lam)
  obtain ⟨θ1, θ2, c, r, K, hθ1, hθ2, h01, h02, -, -, hd1, hd2,
      hsrc1, hsrc2, hc, hr, hK, hRoom, hgap, hside⟩ :=
    exists_native_product_strict_phases_smooth (fun x => S.g1 (lam • x))
      (fun y => S.g2 (lam • y)) hgs1 (fun x => S.g1_admissible.posDef (lam • x))
      hgs2 (fun y => S.g2_admissible.posDef (lam • y)) p1 p2 U hU hpU rho hrho hrho0 hTest
  obtain ⟨e1, he1, hcenter1, κ1, hκ1, H1⟩ :=
    native_first_basis_arm_prescribed_phase S lam hθ1 p1 h01 hd1 hsrc1 (r / 2) (half_pos hr)
  obtain ⟨e2, he2, hcenter2, κ2, hκ2, H2⟩ :=
    native_second_coefficient_arm_prescribed_phase S L lam hθ2 p2 h02 hd2 hsrc2 (r / 2) (half_pos hr)
  have hκ : 0 < min κ1 κ2 := lt_min hκ1 hκ2
  obtain ⟨ρ1, hρ1, G1⟩ := H1 (min κ1 κ2) hκ (min_le_left _ _)
  obtain ⟨ρ2, hρ2, G2⟩ := H2 (min κ1 κ2) hκ (min_le_right _ _)
  obtain ⟨l, ε, R, hε, hl5, hR, hlρ, hRρ, hκl, hεκ, hlR⟩ :=
    exists_slack_params hκ (lt_min hρ1 hρ2) (div_pos hc (by norm_num : (0 : ℝ) < 4))
  obtain ⟨⟨hl, hlρ1, hRρ1, hκ1', hε1, -⟩, -, -, -⟩ :=
    slack_params_mono hκ (min_le_left ρ1 ρ2) (le_refl (c / 4))
      hε hl5 hR hlρ hRρ hκl hεκ hlR
  obtain ⟨⟨-, hlρ2, hRρ2, hκ2', hε2, -⟩, -, -, -⟩ :=
    slack_params_mono hκ (min_le_right ρ1 ρ2) (le_refl (c / 4))
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
      fun z hz => hRoom (hball hz), hη, hmargin⟩, hO1conn, hO2conn, hO1T, hO2S, HB, HA, ι, w, μ, hser⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
