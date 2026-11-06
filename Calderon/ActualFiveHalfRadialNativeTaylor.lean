import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualFiveHalfRadialNativeJets
import Calderon.ActualFiveHalfRadialTaylorJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame


variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] harmonicSphereSubspace referenceAdjointFiveHalfRadialFamily
  referenceFiveHalfAdjointRadialSecondRemainder
  referenceNativeMovingAdjointParametricCorrection
  sphereSobolevInclusionL sphereSobolevRadialDriftAdjointL sphereSobolevShiftedDegreeL
  sphereSobolevAngularCoordinateTransposeL

theorem referenceAdjointFiveHalfRadialFamily_signed_native_taylor
    (hreg : FixedDirichletRegularity) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ t ∈ uIcc (0:ℝ) r, (q,(y,t)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) =
      sphereSobolevShiftedDegreeL (5/2:ℝ) +
      r • (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y)) +
      r^2 • referenceFiveHalfAdjointRadialSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) := by
  let F : ℝ → (SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) := fun t : ℝ => referenceAdjointFiveHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hSmooth (t : ℝ) (ht : t ∈ uIcc (0:ℝ) r) : ContDiffAt ℝ ∞ F t :=
    ((contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment t ht))).comp t
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hZero : F 0 = sphereSobolevShiftedDegreeL (5/2:ℝ) :=
    referenceAdjointFiveHalfRadialFamily_zero_eq_shiftedDegree
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hFirst : deriv F 0 =
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y)) :=
    deriv_referenceAdjointFiveHalfRadialFamily_zero_eq_nativeFirstCorrection
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  unfold referenceFiveHalfAdjointRadialSecondRemainder
  change F r = sphereSobolevShiftedDegreeL (5/2:ℝ) +
    r • (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD (5/2:ℝ) (referenceCenterDrift g L q y)) +
    r^2 • secondTaylorRemainder F r
  clear_value F
  have hRaw := signed_taylor_integral_remainder F r hSmooth
  have hChange := congrArg₂
    (fun b d : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) =>
      b+r • d+r^2 • secondTaylorRemainder F r) hZero hFirst
  exact hRaw.trans hChange


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
