import Calderon.ActualReferenceGaugeNormalRadialDerivativeCertificates
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.NormalCommutatorRightProductJet

/-! The right-product derivative, taken before finite-band transport. -/
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

def referenceGaugeNormalRightProductFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ((referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)).comp
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse

attribute [local irreducible] referenceGaugeNormalRightProductFamily
  referenceLowerRadialEndpointFamily referenceGaugeNormalHalfMultiplierFamily
  referenceGaugeNormalNegativeHalfMultiplierFamily sphereSobolevLinearCoordinateMulL referenceCenterDrift

#eval "RAW-K: before raw-jet declaration"

set_option diagnostics true in
lemma referenceGaugeNormalRightProductFamily_zero_radial_raw_jet
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceGaugeNormalRightProductFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,0)) = 0 ∧
    HasDerivAt (fun r : ℝ => referenceGaugeNormalRightProductFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)))
      ((sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) (referenceCenterDrift g L q y)).comp
        (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0))) -
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0))).comp
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2:ℝ) (referenceCenterDrift g L q y))) 0 := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: proof entered"
    out.flush
  let A : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun r =>
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
  let P : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun r =>
    referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  let N : ℝ → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun r =>
    referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r))
  let W : ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun r => (P r).inverse
  let d := referenceCenterDrift g L q y
  let Mp := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d
  let Mn := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d
  have hy2 : ‖y-y0‖ ≤ 2*ρ := by linarith [norm_nonneg (y-y0)]
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: P certificate"
    out.flush
  have hPJet : P 0 = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
      HasDerivAt P Mp 0 :=
    referenceGaugeNormalHalfMultiplierFamily_zero_radial_jet
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: N certificate"
    out.flush
  have hNJet : N 0 = ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) ∧
      HasDerivAt N Mn 0 :=
    referenceGaugeNormalNegativeHalfMultiplierFamily_zero_radial_jet
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: A certificate"
    out.flush
  have hA : HasDerivAt A (deriv A 0) 0 :=
    hasDerivAt_referenceLowerRadialEndpoint_radial_zero
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: W certificate"
    out.flush
  have hWJet : W 0 = ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
      HasDerivAt W (deriv W 0) 0 :=
    referenceGaugeNormalHalfInverse_zero_radial_jet
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q hq y hy2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: product certificate"
    out.flush
  have hProduct : (((N 0).comp (A 0) - (A 0).comp (P 0)).comp (W 0) = 0) ∧
      HasDerivAt (fun r : ℝ => ((N r).comp (A r) - (A r).comp (P r)).comp (W r))
        (Mn.comp (A 0) - (A 0).comp Mp) 0 :=
    zero_hasDerivAt_normalCommutator_right_identity A N P W (deriv A 0) Mn Mp (deriv W 0)
      hA hNJet.2 hPJet.2 hWJet.2 hNJet.1 hPJet.1 hWJet.1
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "RAW-K: product certificate finished"
    out.flush
  constructor
  · unfold referenceGaugeNormalRightProductFamily
    exact hProduct.1
  · simpa only [referenceGaugeNormalRightProductFamily] using hProduct.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalRightProductFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalRightProductFamily_zero_radial_raw_jet
