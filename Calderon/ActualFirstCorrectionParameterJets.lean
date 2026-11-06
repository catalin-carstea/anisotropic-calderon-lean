import Calderon.ActualBoundedCoordinateFirstCorrection
import Calderon.ActualFramedJacobiVelocityRemainder

/-! Source-only true q/center operator-norm jets of the completed first radial
and coordinate corrections. No Psi seminorm or full moving-family derivative
completion claim is made. All coefficients are the actual reference drift. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError

private instance instCompleteFirstCorrectionJetR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

theorem contDiff_referenceCenterDrift_joint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => referenceCenterDrift g L p.1 p.2) := by
  have hA : ContDiff ℝ ∞ (fun A : R3 →L[ℝ] R3 => A.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  unfold referenceCenterDrift
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => L)).smul
    ((hA.comp (contDiff_conformalReferenceGramFrameOperatorJoint g hg L)).clm_apply
      (contDiff_conformalReferenceDepthGradient.comp contDiff_snd))

theorem contDiff_radialDriftTraceL {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : P → R3) (hd : ContDiff ℝ ∞ d) :
    ContDiff ℝ ∞ (fun p => radialDriftTraceL hF hO hD (d p)) := by
  unfold radialDriftTraceL
  apply ContDiff.neg
  apply ContDiff.sum
  intro i hi
  exact ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hd).smul contDiff_const

theorem contDiff_referenceRadialDriftTraceL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 => radialDriftTraceL hF hO hD (referenceCenterDrift g L p.1 p.2)) :=
  contDiff_radialDriftTraceL hF hO hD _ (contDiff_referenceCenterDrift_joint g hg L)

theorem contDiff_referenceCoordinateRadialDriftTraceL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L p.1 p.2) i) := by
  change ContDiff ℝ ∞ (fun p : ℝ × R3 =>
    (sphereCoordinateMulL i).comp (radialDriftTraceL hF hO hD (referenceCenterDrift g L p.1 p.2)))
  exact contDiff_const.clm_comp (contDiff_referenceRadialDriftTraceL g hg L hF hO hD)

theorem exists_joint_referenceFirstRadialCorrection_operator_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (K : Set (ℝ × R3)) (hK : IsCompact K) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ j (fun x : ℝ × R3 =>
        radialDriftTraceL hF hO hD (referenceCenterDrift g L x.1 x.2)) p‖ ≤ D ∧
      ∀ i : Fin 3, ‖iteratedFDeriv ℝ j (fun x : ℝ × R3 =>
        coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L x.1 x.2) i) p‖ ≤ D := by
  let T : Option (Fin 3) → (ℝ × R3) → SphereL2 →L[ℝ] SphereL2 := fun i p =>
    match i with
    | none => radialDriftTraceL hF hO hD (referenceCenterDrift g L p.1 p.2)
    | some i => coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L p.1 p.2) i
  have hT (i : Option (Fin 3)) : ContDiff ℝ ∞ (T i) := by
    cases i with
    | none => exact contDiff_referenceRadialDriftTraceL g hg L hF hO hD
    | some i => exact contDiff_referenceCoordinateRadialDriftTraceL g hg L hF hO hD i
  obtain ⟨D,hDnonneg,hBound⟩ :=
    exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt T K hK
      (fun i p hp => (hT i).contDiffAt) N
  exact ⟨D,hDnonneg,fun j hj p hp =>
    ⟨hBound j hj p hp none,fun i => hBound j hj p hp (some i)⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
