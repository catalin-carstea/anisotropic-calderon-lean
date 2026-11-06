import MixedKernelCenteredRooms
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem native_first_basis_arm_prescribed_phase
    (S : KnownSideSourceData) (lam : ℝ) {θ : R3 → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (fun x => S.g1 (lam • x)) θ p) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      e.symm '' PhaseCoordinates.roomO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      1 / 2 < (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) ∧
      (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) < 1 ∧
      ∃ Kint : ℝ, 0 < Kint ∧
      FirstBasisArmOn S lam (e.symm '' PhaseCoordinates.roomD l ε R)
        (e.symm '' PhaseCoordinates.roomO l ε R)
        (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) Kint
        ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H1⟩ := native_room_interpolation_lp_op_loc_centered
    S.g1 S.g1_admissible lam hθ p h0 hdθ hsrc r0 hr0
    (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
    (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  exact ⟨hloc, hDt, hDo, hOD, hSD, hg1, hg2, Kint, hKint,
    first_basis_arm_on_of_room S lam _ _ _ HI⟩

theorem native_second_coefficient_arm_prescribed_phase
    (S : KnownSideSourceData) (L : ℝ) (lam : ℝ) {θ : R3 → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0)
    (hsrc : SrcStrict (fun x => S.g2 (lam • x)) θ p) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      e.symm '' PhaseCoordinates.roomO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      1 / 2 < (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) ∧
      (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) < 1 ∧
      ∃ Kint : ℝ, 0 < Kint ∧
      ∀ (b : R3 → ℝ), ContDiffOn ℝ ∞ b (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam b x = 0) →
      ∀ (bD : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
        (bO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
        (bS : Lp ℝ 2 ((volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
      b =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
        (bD : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
        (bO : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict
        (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
        (bS : R3 → ℝ) →
      ∀ M μ : ℝ, 0 < μ → 0 ≤ M → ‖bS‖ ≤ M → ‖bD‖ ≤ M / μ →
        ‖bO‖ ≤ Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
            (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1) ∧
        μ * ‖bO‖ ≤ Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
            (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H1⟩ := native_room_interpolation_lp_op_loc_centered
    S.g2 S.g2_admissible lam hθ p h0 hdθ hsrc r0 hr0
    (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
    (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam u x).mp h)
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  refine ⟨hloc, hDt, hDo, hOD, hSD, hg1, hg2, Kint, hKint,
    fun b hb hP bD bO bS hbD hbO hbS M μ hμ hM hSb hDb => ?_⟩
  have h := HI bD b hbD hb hP bO bS hbO hbS
  have h1 := interp_coeff_bound hμ hM hKint.le (norm_nonneg _) hSb (norm_nonneg _) hDb
    (by linarith) hg2.le h
  refine ⟨h1, ?_⟩
  calc μ * ‖bO‖ ≤ μ * (Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1)) :=
        mul_le_mul_of_nonneg_left h1 hμ.le
    _ = Kint * M * (μ * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1)) := by ring
    _ = _ := by rw [mul_rpow_sub_one hμ]


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
