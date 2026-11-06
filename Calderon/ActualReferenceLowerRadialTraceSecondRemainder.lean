import Calderon.ActualReferenceEndpointFirstRadialJetMatching
import Calderon.JointParameterTaylorRemainder
import Calderon.ActualReferenceLowerRadialTraceRawTaylor

/-! Literal signed integral remainder of SAME actual lower DN curve; native true firstjet
is proved. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance : CompleteSpace
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by infer_instance

def referenceLowerRadialTraceSecondRemainder
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (s : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  secondTaylorRemainder (fun z : ℝ => referenceLowerRadialEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,z))) r

attribute [local irreducible] referenceLowerRadialEndpointFamily referenceLowerRadialTraceSecondRemainder
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily
  sphereSobolevRadialDriftL sphereSobolevInclusionL referenceCenterDrift

lemma exists_reference_commonRadius_lowerRadialTrace_taylor_nativeFirstCorrection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∃ M : ℝ, 0 ≤ M ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ r : ℝ, |r| ≤ δ →
        referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (s,(y,r)) =
        referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 (s,(y,0)) +
        r • ((sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
          (sphereSobolevRadialDriftL hF hO hD (1/2 : ℝ) (referenceCenterDrift g L s y))) +
        r^2 • referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r ∧
        ‖referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r‖ ≤ M/2 := by
  let A : (ℝ × (R3 × ℝ)) → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hRawRoom : HasCompactRadialTaylorRoom A Ω (Icc (0 : ℝ) 1) (closedBall y0 ρ) ρ :=
    exists_reference_commonRadius_lowerRadialTrace_raw_taylor
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  unfold HasCompactRadialTaylorRoom at hRawRoom
  obtain ⟨δ,hδ,hδρ,M,hM,hRoom,hTaylor⟩ := hRawRoom
  refine ⟨δ,hδ,hδρ,M,hM,hRoom,?_⟩
  intro s hs y hy r hr
  have hRaw := hTaylor s hs y hy r hr
  have ht : referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,r)) =
      referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,(y,0)) +
      r • radialFirstDerivative (fun p : R3 × ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (s,p)) (y,0) +
      r^2 • referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r ∧
      ‖referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r‖ ≤ M/2 := by
    simpa only [referenceLowerRadialTraceSecondRemainder] using hRaw
  have hy' : ‖y-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hj := radialFirstDerivative_referenceLowerRadialTrace_eq_nativeFirstCorrection
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg s hs y hy'
  have he := congrArg (fun D : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (s,(y,0)) + r • D + r^2 • referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 s y r) hj
  exact ⟨ht.1.trans he,ht.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerRadialTraceSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_lowerRadialTrace_taylor_nativeFirstCorrection
