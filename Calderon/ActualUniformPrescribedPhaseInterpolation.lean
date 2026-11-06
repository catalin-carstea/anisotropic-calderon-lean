import Calderon.ActualUniformPrescribedPhaseCollar
import Calderon.MixedKernelConstruction.MixedKernelCenteredRooms
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry
theorem native_room_interpolation_uniform_near_dilation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lamBase : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lamBase • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ lam0 ρ : ℝ, 0 < lam0 ∧ 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ lambda ∈ closedBall lamBase lam0, ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          Kint * (Real.sqrt (∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) ^
              ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) ^
              (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ := native_room_collar_sq_uniform_near_dilation g hg lamBase hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨lam0, ρ, C, τ0, hlam0, hρ, hC, H2⟩ := H κ hκ hκ'
  refine ⟨lam0, ρ, hlam0, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨-, -, -, hOD, hloc, hDt, K, hK, HW⟩ := H2 l ε R hε hl hR hlρ hRρ hκh
  have hl0 : 0 < l := by linarith
  have hκl : κ * l ≤ 1 / 4 := by
    have := mul_pos hκ hε
    nlinarith
  obtain ⟨Kint, hKint, HI⟩ := strictHeight_interpolation_of_weighted_sq_uniform (τ0 := τ0)
    hκ hl0 hκl hε.le hε4 (mul_nonneg hC.le hK)
  refine ⟨hloc, hDt, Kint, hKint, fun lambda hlam w hw hLw hwint => ?_⟩
  have hOn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hOD' : (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hOD.eventuallyLE
  refine HI _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hOD')
    (fun τ hτ => ?_)
  rw [Real.sq_sqrt hOn, Real.sq_sqrt hSn, Real.sq_sqrt hDn]
  exact HW lambda hlam τ hτ w hw hLw hwint

theorem native_room_interpolation_lp_op_uniform_near_dilation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lamBase : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lamBase • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ lam0 ρ : ℝ, 0 < lam0 ∧ 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ lambda ∈ closedBall lamBase lam0,
        ∀ (Q : (R3→ℝ)→R3→ℝ),
        (∀ u x,Q u x=0 → Lop (fun i k y => principalCoefficient g (lambda • y) i k) u x=0) →
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ :=
    native_room_interpolation_uniform_near_dilation g hg lamBase hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨lam0, ρ, hlam0, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨lam0, ρ, hlam0, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨hloc, hDt, Kint, hKint, fun lambda hlam Q hQ u q hq hqs hQq uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hwint : IntegrableOn (fun x => q x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) :=
    hmem.integrable_sq
  have hI := HI lambda hlam q hqs (fun x hx => hQ q x (hQq x hx)) hwint
  rw [hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hI
  have hOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hmono : (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2 :=
    setIntegral_mono_set (hwint.mono_set hOD)
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (Set.image_mono PhaseCoordinates.roomO_subset_closedO).eventuallyLE
  calc ‖uO‖ = Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) := by
        rw [hnO, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ _ := hI

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
