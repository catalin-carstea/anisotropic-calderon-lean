import Calderon.ActualReferenceRadialRotationCommutatorMidpointFamily
import Calderon.ActualReferenceUpperRotationCommutatorHarmonicBlock

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection

/-! Full upfront argument: EXPANSION-v002.json. The PHYSICAL L2 coefficient of
the actual midpoint derivative is decoded through both actual inclusions. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRadialRotationCommutatorMidpointFamily_harmonic_block
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL 0 m
      (referenceRadialRotationCommutatorMidpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
          (sphereSobolevSingleL 1 n u)) =
    harmonicSphereRotation m i j
      (sphereSobolevCoefficientL (1/2:ℝ) m
        (referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
            (sphereSobolevSingleL (3/2:ℝ) n u))) -
    sphereSobolevCoefficientL (1/2:ℝ) m
      (referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
          (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u))) := by
  have hMap := referenceRadialRotationCommutatorMidpointFamily_upper_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp
  have hValue := congrArg
    (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
      A (sphereSobolevSingleL (3/2:ℝ) n u)) hMap
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single] at hValue
  have hCoefficient := congrArg (sphereSobolevCoefficientL 0 m) hValue
  have hDecode := sphereSobolevCoefficientL_inclusion (1/2:ℝ) 0 (by norm_num)
    (referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p
        (sphereSobolevSingleL (3/2:ℝ) n u)) m
  exact hCoefficient.trans (hDecode.trans
    (referenceSharpRadialRotationCommutatorL_harmonic_block
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hp.1 hp.2.1 m n u))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialRotationCommutatorMidpointFamily_harmonic_block
