import Calderon.ActualPhysicalDensityErrorDecomposition
import Calderon.ActualHigherSFormation

/-! Regrouping of the full physical error: the complementary `USigma+UD+UFirst+UProducts`,
taken term by term from `referencePhysicalDensityError`, and the purely additive identity
`error = complement + nativeHigherSNegative` (the `USecond+UAngular+UDouble` of the formation).
The proof zeta-reduces both sides, then applies the generic lemma. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSErrorSplit
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift

/-- Pure additive regrouping of seven summands (left-associated, as in the source). -/
lemma error_regroup {M : Type*} [AddCommGroup M] (a b c d e f h : M) :
    a+b+c+d+e+f+h = (a+b+c+f)+(d+e+h) := by
  abel

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

/-- The `USigma+UD+UFirst+UProducts` part of `referencePhysicalDensityError`: the `let` block is
that of `referencePhysicalDensityError`; only the final sum drops the three higher-S
summands. -/
def referencePhysicalDensityErrorComplement (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) : SphereSobolev (-(1/2 : ℝ)) :=
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Ahi := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
  let Alo := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
  let D := fun (i : Fin 3) (x : R3) => referenceHighWeightedHorizontalAction g L q R u x i
  let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
  let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
    hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
  let Eh := fun (i : Fin 3) (x : R3) => referenceHighAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R x i
  let El := fun i : Fin 3 => referenceLowerAdjointMovingDifferenceQuotient
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
  let E := fun (i : Fin 3) (x : R3) => Eh i x (u x)
  let MF := fun i : Fin 3 => Iout.comp (Fl i)
  let ME := El
  let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  let sigma := fun i j : Fin 3 => Q i j-if i=j then (1 : ℝ) else 0
  let b := fun i : Fin 3 => normalizedSecondDriftFrameJoint g g2 L i (q,y)
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q y
    (referenceMetricGramFrame g L (q,y) i) k j
  let r := R y
  let CovD := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (D j) y i-
    ∑ k : Fin 3, Gamma i j k • Iout (D k y)
  let UF := fun i j : Fin 3 => referenceLowerWeightedHorizontalAction g L q R (F j) y i+
    MF i (D j y)-(∑ k : Fin 3, Gamma i j k • Iout (F k y))+MF i (F j y)
  let UFE := fun i j : Fin 3 => MF i (E j y)+ME i (F j y)
  let USigma := (2 : ℝ) • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (D j y))+
    r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • Alo i (Ahi j (u y)))
  let UD := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • CovD i j)+
    r • (∑ i : Fin 3, b i • Iout (D i y))
  let UFirst := r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UF i j)+
    r • (∑ i : Fin 3, b i • Iout (F i y))
  let UProducts := r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • UFE i j)
  USigma+UD+UFirst+UProducts

attribute [local irreducible] referencePhysicalDensityOperator referenceDensityCovariantSecondAction
  referenceHighDensityFirstAction referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceNativeMovingAdjointParametricCorrection referenceNativeMovingAdjointHighMixedCorrection
  referenceMetricGramFrame referenceFrameConnectionCoefficient referenceDensityPrincipalFrameCoefficient
  referenceRadiusHorizontalLogDerivative sphereSobolevInclusionL sphereSobolevAngularCoordinateTransposeL
  referenceRadialEndpointInvertibleLocus normalizedSecondDriftFrameJoint

/-- **Literal full-error regrouping.** The exact original physical density error equals the
literal complement plus the literal higher-S negative, for every `g2 q R u y` (no hypothesis). -/
theorem referencePhysicalDensityError_eq_complement_add_higherSNegative
    (g2 : MatrixField) (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) :
    referencePhysicalDensityError g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u y =
      referencePhysicalDensityErrorComplement g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 q R u y +
        ActualHigherSFormation.nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg
          hcalc τ0 g2 q R u y := by
  unfold referencePhysicalDensityError referencePhysicalDensityErrorComplement
    ActualHigherSFormation.nativeHigherSNegative
    ActualHigherSFormation.nativeHigherSSecondNegative
    ActualHigherSFormation.nativeHigherSAngularNegative
    ActualHigherSFormation.nativeHigherSDoubleNegative
  first
    | exact error_regroup _ _ _ _ _ _ _
    | (dsimp only; exact error_regroup _ _ _ _ _ _ _)
    | (dsimp only; abel)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSErrorSplit
