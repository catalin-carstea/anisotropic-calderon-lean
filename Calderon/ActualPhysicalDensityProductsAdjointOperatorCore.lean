import Calderon.ActualNativeMovingCorrectionAdjunction
import Calderon.ActualPhysicalAdjointMovingDifferenceQuotientPivot
import Calderon.ActualNativeMovingAdjointCorrectionInclusion
import Calderon.NativeRadialJetTranspose
import Calderon.ActualHighAdjointWeightedCorrectionOpenRoom
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualJacobiCoefficientTubeCover
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.SphereSobolevPairingInclusion
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.SphereSobolevRadialDriftAdjoint
import Calderon.ActualFirstCorrectionParameterJets
import Calderon.CompactParameterReferenceFramedNormalMetric

/-! The actual Products adjoint. No quantitative Productsdag cap, finite-output
assumption or intrinsic Half adjoint is used. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevZeroEquiv
  sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL referenceNativeMovingAdjointParametricCorrection
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceAdjointMovingDifferenceQuotientPivotHigh referenceAdjointMovingDifferenceQuotientPivotLow

def referencePhysicalDensityProductsHalfOperator
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (y : R3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  let Fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let E : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
    ((Fl i).comp (E j)+(E i).comp (Fh j)))

def referencePhysicalDensityProductsAdjointHalfOperator
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (y : R3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  let Fh : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun i =>
    referenceNativeMovingParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fl : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceNativeMovingParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let E : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i =>
    referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
    ((E j).comp (Fh i)+(Fl j).comp (E i)))

lemma referencePhysicalDensityProductsHalfOperator_negative_inclusion
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (g2 : MatrixField)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referencePhysicalDensityProductsHalfOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R y u) =
(R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
          (referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y j (u))) +
       referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) j (u))))) := by
  classical
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Fh : Fin 3 → Hi →L[ℝ] Hi := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Fl : Fin 3 → Half →L[ℝ] Half := fun i =>
    referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Eh : Fin 3 → Hi →L[ℝ] Half := fun i =>
    referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let El : Fin 3 → Half →L[ℝ] Neg := fun i =>
    referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Q : Fin 3 → Fin 3 → ℝ := referenceDensityPrincipalFrameCoefficient g g2 L q y
  have hEnd : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    simpa only [one_mul] using hSegment 1 ⟨zero_le_one,le_rfl⟩
  have hE (i : Fin 3) (v : Hi) : J (Eh i v) = El i (I v) := by
    have h := congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceAdjointMovingDifferenceQuotient_high_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R y hy i hInv hEnd)
    exact h
  have hTerms (i j : Fin 3) :
      J (Fl i (Eh j u)+Eh i (Fh j u)) =
        J (Fl i (Eh j u))+El i (I (Fh j u)) :=
    (J.map_add _ _).trans (congrArg (fun z : Neg => J (Fl i (Eh j u))+z) (hE i (Fh j u)))
  have hSum : J ((R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
      Q i j • (Fl i (Eh j u)+Eh i (Fh j u)))) =
      (R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (J (Fl i (Eh j u))+El i (I (Fh j u)))) := by
    have hInner (i : Fin 3) :
        J (∑ j : Fin 3, Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) =
          ∑ j : Fin 3, Q i j • (J (Fl i (Eh j u))+El i (I (Fh j u))) := by
      have hMap : J (∑ j : Fin 3, Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) =
          ∑ j : Fin 3, J (Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) :=
        map_sum J (fun j : Fin 3 => Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) Finset.univ
      have hEach : (∑ j : Fin 3, J (Q i j • (Fl i (Eh j u)+Eh i (Fh j u)))) =
          ∑ j : Fin 3, Q i j • (J (Fl i (Eh j u))+El i (I (Fh j u))) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (J.map_smul (Q i j) (Fl i (Eh j u)+Eh i (Fh j u))).trans
          (congrArg (fun z : Neg => Q i j • z) (hTerms i j))
      exact hMap.trans hEach
    have hOuter : J (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) =
        ∑ i : Fin 3, J (∑ j : Fin 3, Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) :=
      map_sum J (fun i : Fin 3 => ∑ j : Fin 3,
        Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) Finset.univ
    have hEachOuter : (∑ i : Fin 3,
        J (∑ j : Fin 3, Q i j • (Fl i (Eh j u)+Eh i (Fh j u)))) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          Q i j • (J (Fl i (Eh j u))+El i (I (Fh j u))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hInner i
    have hScale : J ((R y)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (Fl i (Eh j u)+Eh i (Fh j u)))) =
        (R y)^2 • J (∑ i : Fin 3, ∑ j : Fin 3,
          Q i j • (Fl i (Eh j u)+Eh i (Fh j u))) :=
      J.map_smul ((R y)^2) (∑ i : Fin 3, ∑ j : Fin 3,
        Q i j • (Fl i (Eh j u)+Eh i (Fh j u)))
    exact hScale.trans (congrArg (fun z : Neg => (R y)^2 • z)
      (hOuter.trans hEachOuter))
  simpa only [referencePhysicalDensityProductsHalfOperator,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    I,J,Fh,Fl,Eh,El,Q] using hSum



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityProductsHalfOperator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityProductsAdjointHalfOperator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDensityProductsHalfOperator_negative_inclusion
