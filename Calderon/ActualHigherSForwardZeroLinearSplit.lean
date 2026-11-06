import Calderon.ActualHigherSZeroLinearSplitDefinitions
import Calderon.ActualHigherSCoefficientBounds
import Calderon.FixedParameterProfilePullback
import Calderon.ActualHigherSForwardZeroConstructor
import Calderon.ActualForwardZeroCollectedAlgebra

/-! The original forward zero split. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualJacobiAngularGainedRows SmoothMetricFrame MovingFrameConnection FixedParameterProfilePullback
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient

private lemma native_forward_rows_congr
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (E : Fin 3 → Hi →L[ℝ] Half) (El Alo : Fin 3 → Half →L[ℝ] Neg)
    (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (Z Z' : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (hZ : Z=Z') :
    ActualHigherSCoefficientExtraction.zeroCoefficient r Q b Z E El Alo Ahi =
      ActualHigherSCoefficientExtraction.zeroCoefficient r Q b Z' E El Alo Ahi := by
  cases hZ
  rfl

private lemma native_quad_linear_congr (J : Half →L[ℝ] Neg)
    (Quad1 Quad2 : Hi →L[ℝ] Neg) (Lin1 Lin2 : Hi →L[ℝ] Half)
    (hQuadEq : Quad1=Quad2) (hLinEq : Lin1=Lin2) :
    Quad1+J.comp Lin1=Quad2+J.comp Lin2 := by
  cases hQuadEq
  cases hLinEq
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "Q2" => literalQuadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T2" => literalQuadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Z1" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T1" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => ActualHigherSCoefficientExtraction.higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CT" => ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL referenceHighHorizontalAngularL
  referenceLowerHorizontalAngularL referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceRadiusHorizontalLogDerivative

attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
  ActualHigherSAdjointCoefficientExtraction.adjointSecondZeroRow
  ActualHigherSCoefficientExtraction.profileHigh ActualHigherSCoefficientExtraction.profileLow
  ActualHigherSAdjointCoefficientExtraction.reverseProfileHigh
  ActualHigherSAdjointCoefficientExtraction.reverseProfileLow
  ActualHigherSCoefficientExtraction.higherSZeroCoefficient
  ActualHigherSAdjointCoefficientExtraction.higherSAdjointZeroCoefficient

attribute [local irreducible] literalQuadraticZeroNegative literalQuadraticZeroReverseNegative
  linearZeroHigh linearAdjointZeroHigh

/-- Literal forward zero coefficient; the only low-family identification is the
checked canonical dictionary on the original retained common room. -/
theorem source_zero_coefficient_eq_literal (hreg : FixedDirichletRegularity)
    (d0 : ℝ) (W : CoeffRoom d0) (d : ℝ) (Cm : CRoom hreg d0 W d)
    (hJac : ∀ z ∈ commonRoom y0 ρ d,Jac z)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3) (hx : (Tq dr Ar p q) x ∈ ParamRoom d) :
    CZ g2 dr Ar p q x = Q2 g2 dr Ar p q x+(JL).comp (Z1 g2 dr Ar p q x) := by
  have hPL : ActualHigherSCoefficientExtraction.profileLow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 dr Ar p q x =
      fun i => EL i ((Tq dr Ar p q) x) := by
    funext i
    exact ActualHigherSCoefficientBounds.profileLow_eq_canonical
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg d0 W d Cm hJac dr Ar p hdr hAr q hq x hx i
  let R := referenceRadius dr Ar p L
  let r := R x
  let t := (Tq dr Ar p q) x
  let X := referenceMetricGramFrame g L (q,x)
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let b := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Gamma := fun i k j => referenceFrameConnectionCoefficient g L q x (X i) k j
  let E : Fin 3 → Hi →L[ℝ] Half := fun i => EH i t
  let D : Fin 3 → Fin 3 → Hi →L[ℝ] Half := fun i j =>
    fderiv ℝ (fun y => EH j ((Tq dr Ar p q) y)) x (X i)
  let T : Fin 3 → Fin 3 → Hi →L[ℝ] Neg := fun i j =>
    (ActualHigherSCoefficientExtraction.weightedLowerZero g L q R x i).comp (E j)+
      (EL i t).comp (ActualHigherSCoefficientExtraction.weightedHighZero g L q R x j)
  let Ra : Hi →L[ℝ] Neg := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    ((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp (E j)+
      (EL i t).comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)))
  let Rs : Hi →L[ℝ] Neg := r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (EL i t).comp (E j))
  let Quad : Hi →L[ℝ] Neg := (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+Ra)+Rs
  let Lin : Hi →L[ℝ] Half :=
    r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))+
      r^2 • (∑ i : Fin 3, b i • E i)
  have hQuad : Q2 g2 dr Ar p q x=Quad := by
    unfold literalQuadraticZeroNegative
    rfl
  have hLin : Z1 g2 dr Ar p q x=Lin := by
    unfold linearZeroHigh
    rfl
  have hrow (i j : Fin 3) : ActualHigherSCoefficientExtraction.secondZeroRow g L q R
      (fun j y => EH j ((Tq dr Ar p q) y)) (fun i => EL i t) x i j =
      (JL).comp (D i j)+T i j+f i • (JL).comp (E j)-
        ∑ k : Fin 3, Gamma i k j • (JL).comp (E k) := by
    simp only [ActualHigherSCoefficientExtraction.secondZeroRow,D,T,E,Gamma,f,X,t,R,add_assoc]
  have hRows :
      (fun i j => ActualHigherSCoefficientExtraction.secondZeroRow g L q R
        (fun j y => EH j ((Tq dr Ar p q) y)) (fun i => EL i t) x i j) =
      (fun i j => (JL).comp (D i j)+T i j+f i • (JL).comp (E j)-
        ∑ k : Fin 3, Gamma i k j • (JL).comp (E k)) := by
    funext i j
    exact hrow i j
  have hSource0 := ActualHigherSForwardZeroConstructor.actual_zero_source_constructor
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q x (fun i => EL i t) hPL
  have hTransport := native_forward_rows_congr r Q b E (fun i => EL i t)
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))
    (fun i j => ActualHigherSCoefficientExtraction.secondZeroRow g L q R
      (fun j y => EH j ((Tq dr Ar p q) y)) (fun i => EL i t) x i j)
    (fun i j => (JL).comp (D i j)+T i j+f i • (JL).comp (E j)-
      ∑ k : Fin 3, Gamma i k j • (JL).comp (E k)) hRows
  have hSource := hSource0.trans hTransport
  have hCollected : ActualHigherSCoefficientExtraction.zeroCoefficient r Q b
      (fun i j => (JL).comp (D i j)+T i j+f i • (JL).comp (E j)-
        ∑ k : Fin 3, Gamma i k j • (JL).comp (E k)) E (fun i => EL i t)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))=Quad+(JL).comp Lin := by
    have hNative := ActualForwardZeroCollectedAlgebra.native_forward_collected_zero
      r Q b f Gamma E D T (fun i => EL i t)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))
    exact hNative
  have hTarget := native_quad_linear_congr JL Quad (Q2 g2 dr Ar p q x)
    Lin (Z1 g2 dr Ar p q x) hQuad.symm hLin.symm
  exact hSource.trans (hCollected.trans hTarget)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
