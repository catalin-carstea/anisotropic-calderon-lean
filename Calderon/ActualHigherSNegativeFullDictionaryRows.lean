import Calderon.ActualHigherSFormation

/-! Literal original Second/Angular/Double rows, arbitrary unchanged R/u. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift SmoothMetricFrame
  MovingFrameConnection ReferenceDensityBounds ConformalDepth

theorem nativeHigherSNegative_eq_full_dictionary_rows
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) :
    let Iout : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Alo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
    let Eh := fun (i : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
    let El := fun i : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
    let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
    let ME := El
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
    let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
      (referenceMetricGramFrame g L (q,y) i) k j
    let f := fun i : Fin 3 => referenceRadiusHorizontalLogDerivative g L q R y i
    let r := R y
    let UE := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (E j) y i+
      ME i (D j y)+f i • Iout (E j y)-(∑ k : Fin 3, Gamma i j k • Iout (E k y))
    let UA := fun i j : Fin 3 => Alo i (E j y)+ME i (Ahi j (u y))
    let UEE := fun i j : Fin 3 => ME i (E j y)
    let USecond := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UE i j)+
      r^2 • (∑ i : Fin 3, b i • Iout (E i y))
    let UAngular := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UA i j)
    let UDouble := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UEE i j)
    ActualHigherSFormation.nativeHigherSNegative
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y =
        USecond + UAngular + UDouble := by
  classical
  intro dIout dAhi dAlo dD dEh dEl dE dME dQ db dGamma df drad
    dUE dUA dUEE dUSecond dUAngular dUDouble
  have hSecond :
      ActualHigherSFormation.nativeHigherSSecondNegative
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y =
          dUSecond := by
    dsimp only [ActualHigherSFormation.nativeHigherSSecondNegative,
      dUSecond,drad,dQ,dUE,db,dIout,dE,dD,dME,df,dGamma,dEh,dEl] <;> rfl
  have hAngular :
      ActualHigherSFormation.nativeHigherSAngularNegative
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y =
          dUAngular := by
    dsimp only [ActualHigherSFormation.nativeHigherSAngularNegative,
      dUAngular,drad,dQ,dUA,dAlo,dAhi,dE,dEh,dME,dEl] <;> rfl
  have hDouble :
      ActualHigherSFormation.nativeHigherSDoubleNegative
        hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 g2 q R u y =
          dUDouble := by
    dsimp only [ActualHigherSFormation.nativeHigherSDoubleNegative,
      dUDouble,drad,dQ,dUEE,dME,dEl,dE,dEh] <;> rfl
  have hRows := congrArg₂
    (fun z t : SphereSobolev (-(1/2 : ℝ)) => z + t)
    (congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z + t)
      hSecond hAngular) hDouble
  exact hRows

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
