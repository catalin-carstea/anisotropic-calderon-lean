import Calderon.ActualReferenceGaugeTangentHighMultiplierCommutator

/-! Graph of the high tangent multiplier commutator, with the same actual tangent scalar
fields. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier SmoothSphereRotation

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceGaugeTangentSecondEndpointFamily
  referenceGaugeTangentSecondRotationEndpointFamily nativeCoefficientRotationFieldL
  referenceGaugeTangentSecondHighMultiplierCommutatorFamily sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

lemma referenceGaugeTangentSecondHighMultiplierCommutatorFamily_inclusion
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2 : ℝ)) :
    let Q2 := compactCoefficient 2 (coefficientValue 3 Q)
      (contDiff_coefficientValue 3 Q) (hasCompactSupport_coefficientValue 3 Q)
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceGaugeTangentSecondHighMultiplierCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p f)) =
    referenceGaugeTangentSecondEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) -
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
      (referenceGaugeTangentSecondEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) := by
  let Q2 := compactCoefficient 2 (coefficientValue 3 Q)
    (contDiff_coefficientValue 3 Q) (hasCompactSupport_coefficientValue 3 Q)
  let F (k : ℕ) (i j : Fin 3) := referenceGaugeTangentSecondRotationJetsFamily
    g L y0 Φ B ε C ρ H a w hData hg k i j p
  let R (k : ℕ) (i j : Fin 3) := coefficientRotationJets k Q j i
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let T := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let V := nativeCoefficientRotationFieldL hcalc hF hO hD τ0 (F 2)
  have hQ : coefficientValue 2 Q2 = coefficientValue 3 Q :=
    coefficientValue_compactCoefficient 2 _ _ _
  have hFValue (i j : Fin 3) : coefficientValue 3 (F 3 i j) = coefficientValue 2 (F 2 i j) := by
    funext x
    exact (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
      g L y0 Φ B ε C ρ H a w hData hg 3 i j p x).trans
      (coefficientValue_referenceGaugeTangentSecondRotationJetsFamily
        g L y0 Φ B ε C ρ H a w hData hg 2 i j p x).symm
  have hRValue (i j : Fin 3) : coefficientValue 3 (R 3 i j) = coefficientValue 2 (R 2 i j) :=
    (coefficientValue_coefficientRotationJets 3 Q j i).trans
      (coefficientValue_coefficientRotationJets 2 Q j i).symm
  have hDerivative (i j : Fin 3) (x : UnitSphere) :
      coefficientValue 2 (R 2 i j) x.val =
      sphereRotationDerivative j i (coefficientValue 2 Q2) x.val :=
    (coefficientRotationJets_sphere_value 2 Q j i x).trans
      (congrArg (fun m : R3 → ℝ => sphereRotationDerivative j i m x.val) hQ.symm)
  have hT : T = V :=
    (referenceGaugeTangentSecondEndpointFamily_eq_rotation
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).trans (by
        dsimp only [V,F]
        unfold referenceGaugeTangentSecondRotationEndpointFamily nativeCoefficientRotationFieldL
        rfl)
  have hNative := nativeThreeHalfRotationFieldCommutatorGainL_inclusion
    hcalc hF hO hD τ0 (F 3) (R 3) (F 2) (R 2) Q2 hFValue hRValue hDerivative f
  have hFields : V (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (I f)) -
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (V (I f)) =
      T (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (I f)) -
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (T (I f)) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (I f)) -
        nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (A (I f))) hT.symm
  have hResult := hNative.trans hFields
  unfold referenceGaugeTangentSecondHighMultiplierCommutatorFamily
  exact hResult

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeTangentSecondHighMultiplierCommutatorFamily_inclusion
