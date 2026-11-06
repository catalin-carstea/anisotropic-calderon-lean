import Calderon.ActualReferenceGaugeNormalRightProductJet
import Calderon.ActualReferenceGaugeNormalRadialDerivativeCertificates
import Calderon.NativeFirstCorrectionDegreeCommutator
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.NormalCommutatorRightProductJet

/-! Full upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-actual-gauge-normal-commutator-firstjet-v068.md. Actual normal
commutator, right HALF inverse, and the nonzero F0dag-F0 linear subtraction. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeNormalCommutatorFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ((referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse

attribute [local irreducible] referenceGaugeNormalCommutatorFamily
  referenceLowerRadialEndpointFamily referenceRadialEndpointInvertibleLocus
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL sphereSobolevShiftedDegreeL
  referenceGaugeNormalRightProductFamily referenceCenterDrift

set_option diagnostics true in
theorem referenceGaugeNormalCommutatorFamily_zero_radial_jet
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) = 0 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))
      ((sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y) -
          sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L q y))) 0 := by
  let d : R3 := referenceCenterDrift g L q y
  let Mp : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d
  let Mn : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d
  let A0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0))
  let R : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun r =>
    referenceGaugeNormalRightProductFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PUBLIC-K: before typed raw certificate"
    out.flush
  have hRaw : R 0 = 0 ∧ HasDerivAt R (Mn.comp A0 - A0.comp Mp) 0 :=
    referenceGaugeNormalRightProductFamily_zero_radial_raw_jet
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y hy
  have hK0 : R 0 = 0 := hRaw.1
  have hK : HasDerivAt R (Mn.comp A0 - A0.comp Mp) 0 := hRaw.2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PUBLIC-K: raw certificate made"
    out.flush
  have hA0 : A0 = sphereSobolevShiftedDegreeL (1/2:ℝ) :=
    referenceLowerRadialEndpointFamily_zero_eq_shiftedDegree
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have hBand : Mn.comp A0 - A0.comp Mp =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d -
          sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d) := by
    rw [hA0]
    apply ContinuousLinearMap.ext
    intro u
    exact sphereSobolevLinearCoordinateMul_half_degree_commutator hF hO hD d u
  let slope : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevRadialDriftAdjointL hF hO hD (1/2 : ℝ) d -
        sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) d)
  have hCoeff : HasDerivAt R slope 0 :=
    Eq.mp (congrArg (fun K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      HasDerivAt R K 0) hBand) hK
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PUBLIC-K: band transport made"
    out.flush
  have hFamily : referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 =
      referenceGaugeNormalRightProductFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 := by
    funext p
    unfold referenceGaugeNormalCommutatorFamily referenceGaugeNormalRightProductFamily
    rfl
  have hCurve : (fun r : ℝ => referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))) = R := by
    funext r
    exact congrFun hFamily (q,(y,r))
  have hZeroValue : referenceGaugeNormalCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) = R 0 :=
    congrFun hCurve 0
  constructor
  · exact hZeroValue.trans hK0
  · exact Eq.mp (congrArg
      (fun F : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
        HasDerivAt F slope 0) hCurve.symm) hCoeff

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalCommutatorFamily_zero_radial_jet
