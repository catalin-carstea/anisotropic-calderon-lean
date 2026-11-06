import Calderon.ActualHigherSZeroLinearSplitDefinitions
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualHigherSZeroParameterFactors
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift ActualHigherSZeroCoefficientFactorisation
  ConformalDepth PrincipalCommutator ActualHigherSLinearZero ActualHigherSQuadraticZeroWords
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ActualJacobiAngularGainedRows SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
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

/-- Scalar normalization of exactly one seven-family word row. -/
private lemma seven_row_scalar_expansion {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r Q fi fj : ℝ) (Gi Gj : Fin 3 → Fin 3 → ℝ)
    (v1 v2 : Fin 3 → Fin 3 → V) (d1 d2 a1 a2 z : V) :
    r^2 • (Q • (((1/2 : ℝ) • (∑ a : Fin 3,∑ b : Fin 3,Gi a b • v1 a b)+fi • d1)+
      ((1/2 : ℝ) • (∑ a : Fin 3,∑ b : Fin 3,Gj a b • v2 a b)+fj • d2)))+
    r • (Q • (a1+a2))+r^3 • (Q • z) =
    (∑ a : Fin 3,∑ b : Fin 3,((r^2/2)*Q*Gi a b) • v1 a b)+
    (∑ a : Fin 3,∑ b : Fin 3,((r^2/2)*Q*Gj a b) • v2 a b)+
    (r^2*Q*fi) • d1+(r^2*Q*fj) • d2+(r*Q) • a1+(r*Q) • a2+(r^3*Q) • z := by
  have hcoef (v : ℝ) : r^2*(Q*((1/2 : ℝ)*v))=(r^2/2)*Q*v := by ring
  simp only [smul_add,Finset.smul_sum,smul_smul]
  simp_rw [hcoef]
  module

local notation "Q2" => literalQuadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "T2" => literalQuadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WQ2" => quadraticZeroNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WT2" => quadraticZeroReverseNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  sphereSobolevInclusionL sphereSobolevShiftedDegreeL sphereSobolevRotationL
  referenceMetricGramFrame referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint referenceRadiusHorizontalLogDerivative

/-- The seven original forward word families reproduce the literal quadratic map. -/
theorem literalQuadraticZeroNegative_eq_words (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) : Q2 g2 dr Ar p q x=WQ2 g2 dr Ar p q x := by
  let t := (Tq dr Ar p q) x
  let r := referenceRadius dr Ar p L x
  let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
  let Gamma := fun i a b => parameterConnection g L i a b t
  have hOL (i : Fin 3) : referenceLowerHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ a : Fin 3,∑ b : Fin 3,Gamma i a b • sphereSobolevRotationL (1/2 : ℝ) a b :=
    (parameterLowerAngular_eq g hg L i t).symm
  have hOH (i : Fin 3) : referenceHighHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ a : Fin 3,∑ b : Fin 3,Gamma i a b • sphereSobolevRotationL (3/2 : ℝ) a b :=
    (parameterHighAngular_eq g hg L i t).symm
  have hAH (i : Fin 3) : raisingHigh hF hO hD i=
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i := rfl
  have hAL (i : Fin 3) : raisingLow hF hO hD i=
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i := rfl
  rw [quadraticZeroNegative_eq_seven_rows]
  apply ContinuousLinearMap.ext
  intro u
  have hrow (i j : Fin 3) := seven_row_scalar_expansion r (Q i j) (f i) (f j)
    (Gamma i) (Gamma j)
    (fun a b => sphereSobolevRotationL (1/2 : ℝ) a b (EH j t u))
    (fun a b => EL i t (sphereSobolevRotationL (3/2 : ℝ) a b u))
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) (EH j t u))
    (EL i t (sphereSobolevShiftedDegreeL (3/2 : ℝ) u))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (EH j t u))
    (EL i t (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u))
    (EL i t (EH j t u))
  unfold literalQuadraticZeroNegative sevenWordRows
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    atomLow,atomHigh,eAtom,rotationAtom,degreeAtom,raisingAtom,generatorLow,generatorHigh,hAL,hAH]
  calc
    _ = ∑ i : Fin 3,∑ j : Fin 3,
      (r^2 • (Q i j •
        (ActualHigherSCoefficientExtraction.weightedLowerZero g L q (referenceRadius dr Ar p L) x i (EH j t u)+
         EL i t (ActualHigherSCoefficientExtraction.weightedHighZero g L q (referenceRadius dr Ar p L) x j u)))+
       r • (Q i j •
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i (EH j t u)+
         EL i t (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u)))+
       r^3 • (Q i j • EL i t (EH j t u))) := by
        simp only [Finset.smul_sum,Finset.sum_add_distrib,r,Q,t]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [ActualHigherSCoefficientExtraction.weightedLowerZero,
        ActualHigherSCoefficientExtraction.weightedHighZero,hOL,hOH,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sum_apply,map_add,map_sum,map_smul,r,Q,f,Gamma,t] using hrow i j

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
