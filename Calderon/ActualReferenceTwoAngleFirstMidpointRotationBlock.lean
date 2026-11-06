import Calderon.ActualReferenceTwoAngleFirstMidpointHarmonicGraph

/-! Actual degree-data block. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceTwoAngleSharpMidpointRadialTraceFamily
  referenceTwoAngleFirstMidpointDerivativeFamily referenceTwoAngleSharpRadialTraceFamily
  referenceRotationSharpRadialTraceFamily sphereSobolevSingleL sphereSobolevCoefficientL

lemma referenceTwoAngleFirstMidpointDerivativeFamily_rotation_harmonic_block
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hp : (0,(φ,p)) ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL 0 m
      (referenceTwoAngleFirstMidpointDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (φ,p)
        (sphereSobolevSingleL 1 n u)) =
    harmonicSphereRotation m i j (sphereSobolevCoefficientL (1/2:ℝ) m
      (referenceRotationSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p)
        (sphereSobolevSingleL (3/2:ℝ) n u))) -
    sphereSobolevCoefficientL (1/2:ℝ) m
      (referenceRotationSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p)
        (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u))) := by
  let M := referenceTwoAngleSharpMidpointRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p))
  let S := referenceRotationSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l (φ,p)
  have hPhysical (v : harmonicSphereSubspace n) :
      sphereSobolevCoefficientL 0 m (M (sphereSobolevSingleL 1 n v))=
        sphereSobolevCoefficientL (1/2:ℝ) m (S (sphereSobolevSingleL (3/2:ℝ) n v)) := by
    have hUpper := congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
        sphereSobolevCoefficientL 0 m (T (sphereSobolevSingleL (3/2:ℝ) n v)))
      (referenceTwoAngleSharpMidpointRadialTraceFamily_upper_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p)) hp)
    have hLeft : sphereSobolevCoefficientL 0 m (M (sphereSobolevSingleL 1 n v))=
        sphereSobolevCoefficientL (1/2:ℝ) m
          (referenceTwoAngleSharpRadialTraceFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (0,(φ,p))
            (sphereSobolevSingleL (3/2:ℝ) n v)) := by
      simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single,
        sphereSobolevCoefficientL_inclusion] using hUpper
    have hZero := congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
        sphereSobolevCoefficientL (1/2:ℝ) m (T (sphereSobolevSingleL (3/2:ℝ) n v)))
      (referenceTwoAngleSharpRadialTraceFamily_zero_outer_angle
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l φ p)
    exact hLeft.trans hZero
  have hRaw := referenceTwoAngleFirstMidpointDerivativeFamily_harmonic_block
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l φ p hp m n u
  exact hRaw.trans (congrArg₂ (fun x y : harmonicSphereSubspace m => x-y)
    (congrArg (harmonicSphereRotation m i j) (hPhysical u))
    (hPhysical (harmonicSphereRotation n i j u)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFirstMidpointDerivativeFamily_rotation_harmonic_block
