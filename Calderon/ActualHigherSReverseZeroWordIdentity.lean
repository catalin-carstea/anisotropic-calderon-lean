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
private lemma native_neg_low_half_sum
    (A : Half →L[ℝ] Neg) (Rot : Fin 3 → Fin 3 → Half →L[ℝ] Neg)
    (G : Fin 3 → Fin 3 → ℝ)
    (hA : A=(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, G a b • Rot a b) :
    -A=(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, G a b • (-Rot a b) := by
  cases hA
  simp only [smul_neg,Finset.sum_neg_distrib]

private lemma native_neg_high_half_sum
    (A : Hi →L[ℝ] Half) (Rot : Fin 3 → Fin 3 → Hi →L[ℝ] Half)
    (G : Fin 3 → Fin 3 → ℝ)
    (hA : A=(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, G a b • Rot a b) :
    -A=(1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3, G a b • (-Rot a b) := by
  cases hA
  simp only [smul_neg,Finset.sum_neg_distrib]

/-- Evaluation of the complete three scalar-power blocks at opaque native maps. -/
private lemma native_quadratic_reverse_apply
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (BH Hh Ah : Fin 3 → Hi →L[ℝ] Half)
    (BL Hl Al : Fin 3 → Half →L[ℝ] Neg) (u : Hi) :
    (r^2 • (∑ i : Fin 3,∑ j : Fin 3,Q i j • ((BL j).comp (Hh i)+(Hl j).comp (BH i)))+
     r • (∑ i : Fin 3,∑ j : Fin 3,Q i j • ((BL j).comp (Ah i)+(Al j).comp (BH i)))+
     r^3 • (∑ i : Fin 3,∑ j : Fin 3,Q i j • (BL j).comp (BH i))) u =
    ∑ i : Fin 3,∑ j : Fin 3,
      (r^2 • (Q i j • (BL j (Hh i u)+Hl j (BH i u)))+
       r • (Q i j • (BL j (Ah i u)+Al j (BH i u)))+
       r^3 • (Q i j • BL j (BH i u))) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    Finset.smul_sum,Finset.sum_add_distrib]

/-- Evaluation of all seven word families without inspecting any atom map. -/
private lemma native_seven_word_rows_apply
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (f : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (W : ZeroAtom → ZeroAtom → Hi →L[ℝ] Neg) (u : Hi) :
    (sevenWordRows r Q f Gamma W) u =
      sevenWordRows r Q f Gamma (fun aa bb => W aa bb u) := by
  simp only [sevenWordRows,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply]

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

/-- Scalar normalization of exactly one seven-family word row.
Finite 207-index enumeration is provided only by the Words owner. -/
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
  atomReverseHigh atomReverseLow generatorSharpHigh generatorSharpLow

/-- The literal reverse quadratic map, evaluated one ordered row at a time. -/
private lemma literal_reverse_apply_rows (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) (u : Hi) :
    T2 g2 dr Ar p q x u =
    let t := (Tq dr Ar p q) x
    let r := referenceRadius dr Ar p L x
    let Q := referenceDensityPrincipalFrameCoefficient g g2 L q x
    let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
    ∑ i : Fin 3,∑ j : Fin 3,
      (r^2 • (Q i j •
        (BL j t ((-referenceHighHorizontalAngularL g L q x i+
          f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)) u)+
         (-referenceLowerHorizontalAngularL g L q x j+
          f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)) (BH i t u)))+
       r • (Q i j • (BL j t (loweringHigh hF hO hD i u)+loweringLow hF hO hD j (BH i t u)))+
       r^3 • (Q i j • BL j t (BH i t u))) := by
  unfold literalQuadraticZeroReverseNegative
  exact native_quadratic_reverse_apply
    (referenceRadius dr Ar p L x) (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (fun i => BH i ((Tq dr Ar p q) x))
    (fun i => -referenceHighHorizontalAngularL g L q x i+
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half))
    (loweringHigh hF hO hD)
    (fun j => BL j ((Tq dr Ar p q) x))
    (fun j => -referenceLowerHorizontalAngularL g L q x j+
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x j •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg))
    (loweringLow hF hO hD) u

/-- Genuine reversed atom order and signs reproduce Hsharp=-O+fDegree. -/
theorem literalQuadraticZeroReverseNegative_eq_words (g2 : MatrixField) (dr Ar : ℝ)
    (p : ℕ) (q : ℝ) (x : R3) : T2 g2 dr Ar p q x=WT2 g2 dr Ar p q x := by
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
  have hSL (i : Fin 3) : -referenceLowerHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ a : Fin 3,∑ b : Fin 3,Gamma i a b • (-sphereSobolevRotationL (1/2 : ℝ) a b) := by
    exact native_neg_low_half_sum (referenceLowerHorizontalAngularL g L q x i)
      (sphereSobolevRotationL (1/2 : ℝ)) (Gamma i) (hOL i)
  have hSH (i : Fin 3) : -referenceHighHorizontalAngularL g L q x i =
      (1/2 : ℝ) • ∑ a : Fin 3,∑ b : Fin 3,Gamma i a b • (-sphereSobolevRotationL (3/2 : ℝ) a b) := by
    exact native_neg_high_half_sum (referenceHighHorizontalAngularL g L q x i)
      (sphereSobolevRotationL (3/2 : ℝ)) (Gamma i) (hOH i)
  rw [quadraticZeroReverseNegative_eq_seven_rows]
  apply ContinuousLinearMap.ext
  intro u
  have hrow (i j : Fin 3) := seven_row_scalar_expansion r (Q i j) (f i) (f j)
    (Gamma i) (Gamma j)
    (fun a b => BL j t (-sphereSobolevRotationL (3/2 : ℝ) a b u))
    (fun a b => -sphereSobolevRotationL (1/2 : ℝ) a b (BH i t u))
    (BL j t (sphereSobolevShiftedDegreeL (3/2 : ℝ) u))
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) (BH i t u))
    (BL j t (loweringHigh hF hO hD i u))
    (loweringLow hF hO hD j (BH i t u)) (BL j t (BH i t u))
  have hREH (i : Fin 3) :
      atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (eAtom i)=BH i t := by
    simp only [atomReverseHigh,eAtom]
  have hREL (i : Fin 3) :
      atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (eAtom i)=BL i t := by
    simp only [atomReverseLow,eAtom]
  have hRRH (aa bb : Fin 3) :
      atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (rotationAtom aa bb)=
        -sphereSobolevRotationL (3/2 : ℝ) aa bb := by
    simp only [atomReverseHigh,rotationAtom,generatorSharpHigh,generatorHigh]
  have hRRL (aa bb : Fin 3) :
      atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (rotationAtom aa bb)=
        -sphereSobolevRotationL (1/2 : ℝ) aa bb := by
    simp only [atomReverseLow,rotationAtom,generatorSharpLow,generatorLow]
  have hRDH :
      atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t degreeAtom=
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half) := by
    simp only [atomReverseHigh,degreeAtom,generatorSharpHigh,generatorHigh]
  have hRDL :
      atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t degreeAtom=
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) := by
    simp only [atomReverseLow,degreeAtom,generatorSharpLow,generatorLow]
  have hRAH (i : Fin 3) :
      atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (raisingAtom i)=
        loweringHigh hF hO hD i := by
    simp only [atomReverseHigh,raisingAtom]
  have hRAL (i : Fin 3) :
      atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t (raisingAtom i)=
        loweringLow hF hO hD i := by
    simp only [atomReverseLow,raisingAtom]
  calc
    _ = ∑ i : Fin 3,∑ j : Fin 3,
      (r^2 • (Q i j •
        (BL j t ((-referenceHighHorizontalAngularL g L q x i+
          f i • (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)) u)+
         (-referenceLowerHorizontalAngularL g L q x j+
          f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)) (BH i t u)))+
       r • (Q i j • (BL j t (loweringHigh hF hO hD i u)+loweringLow hF hO hD j (BH i t u)))+
       r^3 • (Q i j • BL j t (BH i t u))) := by
        exact literal_reverse_apply_rows g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          g2 dr Ar p q x u
    _ = sevenWordRows r Q f Gamma
        (fun aa bb =>
          ((atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t bb).comp
            (atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa)) u) := by
      unfold sevenWordRows
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [hREH,hREL,hRRH,hRRL,hRDH,hRDL,hRAH,hRAL,
        ContinuousLinearMap.comp_apply,hSL,hSH,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.sum_apply,map_add,map_sum,map_smul,r,Q,f,Gamma,t] using hrow i j
    _ = _ := (native_seven_word_rows_apply r Q f Gamma
      (fun aa bb =>
        (atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t bb).comp
          (atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa)) u).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroWordDictionary
