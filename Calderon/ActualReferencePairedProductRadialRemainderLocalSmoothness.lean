import Calderon.ActualReferencePairedLowRadialRemainderLocalSmoothness

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-actual-paired-product-radial-local-smoothness-v044.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referencePairedProductRadialLocalSmoothnessHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedProductRadialLocalSmoothnessNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedProductRadialLocalSmoothnessHighOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referencePairedProductRadialLocalSmoothnessLowOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceRadialEndpointInvertibleLocus secondTaylorRemainder

lemma contDiffAt_referencePairedRadialSecondRemainder_product_families_of_segment
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
        (referenceSharpRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2,
         referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2)) (q,(y,r)) ∧
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2,
         secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2)) (q,(y,r)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_PRODUCT_LOCAL BODY_ENTER"
    let remaining ← Lean.getRemainingHeartbeats
    out.putStrLn s!"PAIRED_R2_PRODUCT_LOCAL BODY_ENTER_REMAINING_INTERNAL={remaining}"
    out.flush
  have hHigh :=
    contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_PRODUCT_LOCAL HIGH_READY"
    let remaining ← Lean.getRemainingHeartbeats
    out.putStrLn s!"PAIRED_R2_PRODUCT_LOCAL HIGH_READY_REMAINING_INTERNAL={remaining}"
    out.flush
  have hLow :=
    contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_PRODUCT_LOCAL LOW_READY"
    out.flush
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_R2_PRODUCT_LOCAL ASSEMBLY_READY"
    out.flush
  exact ⟨hHigh.1.prodMk hLow.1,hHigh.2.prodMk hLow.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
