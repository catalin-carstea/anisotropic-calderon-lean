import Calderon.ActualHigherSSecondAdjoint
import Calderon.ActualCommonQuadraticFormationConsumer
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoefficientExtraction
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting ActualFiniteHarmonicModel
  ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Small Banach-space derivative boundary, independent of the Sobolev representation. -/
lemma fderiv_family_apply_point {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : R3 → E →L[ℝ] G) (u : R3 → E) (x v : R3)
    (hc : DifferentiableAt ℝ c x) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => c y (u y)) x v =
      c x (fderiv ℝ u x v) + fderiv ℝ c x v (u x) := by
  exact congrArg (fun D : R3 →L[ℝ] G => D v) (fderiv_clm_apply hc hu)

/-- The original zero-base part of the weighted HIGH horizontal action. -/
def weightedHighZero (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (x : R3)
    (i : Fin 3) : Hi →L[ℝ] Half :=
  referenceHighHorizontalAngularL g L q x i +
    referenceRadiusHorizontalLogDerivative g L q R x i •
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) : Hi →L[ℝ] Half)

/-- The original zero-base part of the weighted LOWER horizontal action. -/
def weightedLowerZero (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (x : R3)
    (i : Fin 3) : Half →L[ℝ] Neg :=
  referenceLowerHorizontalAngularL g L q x i +
    referenceRadiusHorizontalLogDerivative g L q R x i •
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg)

lemma high_action_split (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (u : R3 → Hi) (x : R3) (i : Fin 3) :
    referenceHighWeightedHorizontalAction g L q R u x i =
      IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)) +
        weightedHighZero g L q R x i (u x) := by
  show (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)) +
      referenceHighHorizontalAngularL g L q x i (u x)) +
      referenceRadiusHorizontalLogDerivative g L q R x i •
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x) : Half) = _
  simp only [weightedHighZero,add_apply,smul_apply]
  abel

lemma lower_action_split (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (v : R3 → Half) (x : R3) (i : Fin 3) :
    referenceLowerWeightedHorizontalAction g L q R v x i =
      JL (fderiv ℝ v x (referenceMetricGramFrame g L (q,x) i)) +
        weightedLowerZero g L q R x i (v x) := by
  show (JL (fderiv ℝ v x (referenceMetricGramFrame g L (q,x) i)) +
      referenceLowerHorizontalAngularL g L q x i (v x)) +
      referenceRadiusHorizontalLogDerivative g L q R x i •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (v x) : Neg) = _
  simp only [weightedLowerZero,add_apply,smul_apply]
  abel

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevShiftedDegreeL
 referenceMetricGramFrame referenceRadiusHorizontalLogDerivative
 referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction

/-- Genuine differentiated coefficient rule, before any operator norm estimate. -/
lemma lower_action_family (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : R3 → (Hi →L[ℝ] Half)) (El : Half →L[ℝ] Neg)
    (u : R3 → Hi) (x : R3) (i : Fin 3)
    (hEh : DifferentiableAt ℝ Eh x) (hu : DifferentiableAt ℝ u x)
    (hcompat : ∀ v : Hi, JL (Eh x v) = El (IH v)) :
    referenceLowerWeightedHorizontalAction g L q R (fun y => Eh y (u y)) x i =
      El (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))) +
      JL (fderiv ℝ Eh x (referenceMetricGramFrame g L (q,x) i) (u x)) +
      weightedLowerZero g L q R x i (Eh x (u x)) := by
  have hd : fderiv ℝ (fun y => Eh y (u y)) x (referenceMetricGramFrame g L (q,x) i) =
      Eh x (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)) +
      fderiv ℝ Eh x (referenceMetricGramFrame g L (q,x) i) (u x) :=
    fderiv_family_apply_point Eh u x (referenceMetricGramFrame g L (q,x) i) hEh hu
  have h1 := congrArg (fun z : Half => JL z) hd
  have h2 : JL (Eh x (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)) +
        fderiv ℝ Eh x (referenceMetricGramFrame g L (q,x) i) (u x)) =
      El (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))) +
        JL (fderiv ℝ Eh x (referenceMetricGramFrame g L (q,x) i) (u x)) :=
    (map_add JL _ _).trans (congrArg (fun z : Neg => z +
      JL (fderiv ℝ Eh x (referenceMetricGramFrame g L (q,x) i) (u x)))
      (hcompat (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))))
  exact (lower_action_split g L q R (fun y => Eh y (u y)) x i).trans
    (congrArg (fun z : Neg => z + weightedLowerZero g L q R x i (Eh x (u x)))
      (h1.trans h2))


private lemma second_row_reassociate {E : Type*} [AddCommGroup E]
    (a b c d e f z : E) : (a+b+c)+(d+e)+f-z = a+d+(b+c+e+f-z) := by abel

/-- Complete zero-base coefficient of one original Second row. -/
def secondZeroRow (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : Fin 3 → R3 → (Hi →L[ℝ] Half)) (El : Fin 3 → Half →L[ℝ] Neg)
    (x : R3) (i j : Fin 3) : Hi →L[ℝ] Neg :=
  (JL).comp (fderiv ℝ (Eh j) x (referenceMetricGramFrame g L (q,x) i)) +
    (weightedLowerZero g L q R x i).comp (Eh j x) +
    (El i).comp (weightedHighZero g L q R x j) +
    referenceRadiusHorizontalLogDerivative g L q R x i • (JL).comp (Eh j x) -
    ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • (JL).comp (Eh k x)

/-- Actual weighted Second row, with both first-base terms and every zero-base
coefficient displayed. This is generic in differentiable compatible families. -/
lemma second_row_split (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : Fin 3 → R3 → (Hi →L[ℝ] Half)) (El : Fin 3 → Half →L[ℝ] Neg)
    (u : R3 → Hi) (x : R3) (i j : Fin 3)
    (hEh : DifferentiableAt ℝ (Eh j) x) (hu : DifferentiableAt ℝ u x)
    (hcompat : ∀ v : Hi, JL (Eh j x v) = El j (IH v)) :
    referenceLowerWeightedHorizontalAction g L q R (fun y => Eh j y (u y)) x i +
      El i (referenceHighWeightedHorizontalAction g L q R u x j) +
      referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x)) =
    El j (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))) +
      El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))) +
      secondZeroRow g L q R Eh El x i j (u x) := by
  have hl := lower_action_family g L q R (Eh j) (El j) u x i hEh hu hcompat
  have hh := congrArg (fun v : Half => El i v) (high_action_split g L q R u x j)
  have hz : secondZeroRow g L q R Eh El x i j (u x) =
      JL (fderiv ℝ (Eh j) x (referenceMetricGramFrame g L (q,x) i) (u x)) +
      weightedLowerZero g L q R x i (Eh j x (u x)) +
      El i (weightedHighZero g L q R x j (u x)) +
      referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x)) := by
    simp only [secondZeroRow,add_apply,sub_apply,smul_apply,sum_apply,
      ContinuousLinearMap.comp_apply]
  have hh2 : El i (referenceHighWeightedHorizontalAction g L q R u x j) =
      El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))) +
      El i (weightedHighZero g L q R x j (u x)) := hh.trans (map_add _ _ _)
  calc
    _ = (El j (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))) +
        JL (fderiv ℝ (Eh j) x (referenceMetricGramFrame g L (q,x) i) (u x)) +
        weightedLowerZero g L q R x i (Eh j x (u x))) +
      (El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))) +
        El i (weightedHighZero g L q R x j (u x))) +
      referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x)) :=
      congrArg₂ (fun a b : Neg => a+b+
        referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
        ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
          (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x))) hl hh2
    _ = _ := (second_row_reassociate _ _ _ _ _ _ _).trans
      (congrArg (fun z : Neg =>
        El j (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))) +
        El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))) + z) hz.symm)

/-- Both ordered Q contractions, without a symmetry premise. -/
def firstFrameCoefficient (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (m : Fin 3) : Half →L[ℝ] Neg :=
  r^2 • (∑ j : Fin 3, Q m j • El j) + r^2 • (∑ i : Fin 3, Q i m • El i)

lemma first_frame_coefficient_apply (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (v : Fin 3 → Half) :
    r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j (v i)+El i (v j))) =
      ∑ m : Fin 3, firstFrameCoefficient r Q El m (v m) := by
  simp only [firstFrameCoefficient,Fin.sum_univ_three,add_apply,smul_apply]
  module

/-- Exact moving-frame to fixed-coordinate conversion, using the existing
coordinate dictionary. No differentiability premise is needed for linearity. -/
def firstCoordinateCoefficient (B : Fin 3 → Half →L[ℝ] Neg)
    (X : Fin 3 → R3) (l : Fin 3) : Half →L[ℝ] Neg :=
  ∑ m : Fin 3, X m l • B m

lemma frame_to_coordinate (B : Fin 3 → Half →L[ℝ] Neg) (X : Fin 3 → R3)
    (u : R3 → Hi) (x : R3) :
    (∑ m : Fin 3, B m (IH (fderiv ℝ u x (X m)))) =
      ∑ l : Fin 3, firstCoordinateCoefficient B X l
        (IH (fderiv ℝ u x (ReferenceDensityBounds.coordinateDirection l))) := by
  have h (m : Fin 3) := WeightedFrameGreen.fderiv_apply_eq_sum_coordinate u x (X m)
  simp only [h,map_sum,map_smul,firstCoordinateCoefficient,sum_apply,smul_apply]
  exact Finset.sum_comm


/-- Complete zero-base coefficient: Second, drift, angular, quadratic in original order. -/
def zeroCoefficient (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) : Hi →L[ℝ] Neg :=
  (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j) +
    r^2 • (∑ i : Fin 3, b i • (JL).comp (Eh i))) +
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((Alo i).comp (Eh j)+(El i).comp (Ahi j))) +
    r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El i).comp (Eh j))

private lemma assemble_coefficient_values {E : Type*} [AddCommGroup E]
    (a az z d e f b c : E) (hA : a=az+z) (hB : az=b) (hC : c=(z+d)+e+f) :
    (a+d)+e+f=b+c := by rw [hA,hB,hC]; abel

/-- Finite assembly without symmetry of Q or altered endpoint norms. -/
lemma coefficient_assembly (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (v : Fin 3 → Half) (u : Hi) :
    (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (El j (v i)+El i (v j)+Z i j u)) +
      r^2 • (∑ i : Fin 3, b i • JL (Eh i u))) +
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (Alo i (Eh j u)+El i (Ahi j u))) +
    r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • El i (Eh j u)) =
      (∑ m : Fin 3, firstFrameCoefficient r Q El m (v m)) +
        zeroCoefficient r Q b Z Eh El Alo Ahi u := by
  have hz : zeroCoefficient r Q b Z Eh El Alo Ahi u =
      (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j u) +
        r^2 • (∑ i : Fin 3, b i • JL (Eh i u))) +
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (Alo i (Eh j u)+El i (Ahi j u))) +
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • El i (Eh j u)) := by
    simp only [zeroCoefficient,add_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply]
  have hs : r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (El j (v i)+El i (v j)+Z i j u)) =
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j (v i)+El i (v j))) +
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j u) := by
    simp only [smul_add,Finset.sum_add_distrib]
  have hb := first_frame_coefficient_apply r Q El v
  exact assemble_coefficient_values _ _ _ _ _ _ _ _ hs hb hz


section Actual
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MQ" => referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "LQ" => referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)
local notation "Jac" => ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ
local notation "Room" δr:max Ar:max p:max q:max δ:max => ActualHigherSFormation.HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q δ

def profileHigh (δr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3) : Hi →L[ℝ] Half :=
  EH j ((Tq δr Ar p q) x)
local notation "PH" => profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def profileLow (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (j : Fin 3) : Half →L[ℝ] Neg :=
  LQ q (referenceRadius δr Ar p L) x j
local notation "PL" => profileLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma actual_profile_room (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ∀ x ∈ TS F0, (Room δr Ar p q δ) x :=
  fun x hx => ActualHigherSFormation.higherSRoomAt_of_mem_paramRoom hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q δ δ δ (le_refl _) (le_refl _) Cm.rev.room hJac x (hT x hx)

/-- Equality of WHOLE input fields, not equality only on a closed parameter box. -/
theorem original_high_field_eq_canonical (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) :
    (fun x => MQ q (referenceRadius δr Ar p L) x j (Uin F0 x)) =
      (fun x => PH δr Ar p q j x (Uin F0 x)) := by
  have hRoom := actual_profile_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac δr Ar p hδr hAr q F0 hT
  funext x
  by_cases hx : x ∈ TS F0
  · exact congrArg (fun A : Hi →L[ℝ] Half => A (Uin F0 x))
      (ActualHigherSFormation.movingQuotient_eq_canonical_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        δr Ar p hδr hAr q hreg hq δ x (hRoom x hx) j)
  · have hz := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx
    simp only [hz,map_zero]

/-- Ambient differentiability of the actual canonical coefficient after the
actual profile substitution, from the SAME common-room witness. -/
theorem differentiableAt_profileHigh (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    DifferentiableAt ℝ (PH δr Ar p q j) x := by
  have ht := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q
  exact ((Cm.germHigh j _ hx).comp x ht.contDiffAt).differentiableAt (by simp)


/-- Actual first-base frame coefficient, with the two Q orders retained. -/
def higherSFirstFrameCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (m : Fin 3) : Half →L[ℝ] Neg :=
  firstFrameCoefficient (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (PL δr Ar p q x) m

/-- The complete actual zero-base coefficient, including the differentiated
ordinary high family and all original lower-order coefficient terms. -/
def higherSZeroCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) : Hi →L[ℝ] Neg :=
  zeroCoefficient (referenceRadius δr Ar p L x)
    (fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j)
    (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (secondZeroRow g L q (referenceRadius δr Ar p L) (PH δr Ar p q) (PL δr Ar p q x) x)
    (fun j => PH δr Ar p q j x) (PL δr Ar p q x)
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ))
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ))

/-- The same first-base coefficient in the original fixed coordinate directions. -/
def higherSFirstCoordinateCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (l : Fin 3) : Half →L[ℝ] Neg :=
  firstCoordinateCoefficient
    (higherSFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 δr Ar p q x)
    (referenceMetricGramFrame g L (q,x)) l

attribute [local irreducible] canonicalHigh canonicalLow referenceHighAdjointMovingDifferenceQuotient
 referenceLowerAdjointMovingDifferenceQuotient referenceDensityPrincipalFrameCoefficient
 normalizedSecondDriftFrameJoint referenceFrameConnectionCoefficient
 ActualHigherSFormation.higherSInput ActualHigherSFormation.higherSParam

/-- Original Second row on the finite input support: the ordinary family and
all compatibility/differentiability facts are discharged from one common room. -/
theorem actual_second_row_split (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F0) (i j : Fin 3) :
    referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (fun y => MQ q (referenceRadius δr Ar p L) y j (Uin F0 y)) x i +
    PL δr Ar p q x i
      (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x j) +
    referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i •
      JL (MQ q (referenceRadius δr Ar p L) x j (Uin F0 x)) -
    ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j •
      JL (MQ q (referenceRadius δr Ar p L) x k (Uin F0 x)) =
    PL δr Ar p q x j (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))) +
    PL δr Ar p q x i (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) j))) +
    secondZeroRow g L q (referenceRadius δr Ar p L) (PH δr Ar p q) (PL δr Ar p q x) x i j (Uin F0 x) := by
  have hf (k : Fin 3) := original_high_field_eq_canonical g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac δr Ar p hδr hAr q hq F0 hT k
  have hw := congrArg
    (fun v : R3 → Half => referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L) v x i) (hf j)
  have he : (fun k : Fin 3 => JL (MQ q (referenceRadius δr Ar p L) x k (Uin F0 x))) =
      (fun k : Fin 3 => JL (PH δr Ar p q k x (Uin F0 x))) := by
    funext k
    exact congrArg (fun f : R3 → Half => JL (f x)) (hf k)
  have hc (v : Hi) : JL (PH δr Ar p q j x v) = PL δr Ar p q x j (IH v) :=
    (ActualHigherSFormation.lowerQuotient_inclusion_of_room hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg hq δ x
      (actual_profile_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm hJac δr Ar p hδr hAr q F0 hT x hx) j v).symm
  have hEh := differentiableAt_profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p hδr hAr q j x (hT x hx)
  have hu : DifferentiableAt ℝ (Uin F0) x := by
    simpa only [ActualHigherSFormation.higherSInput] using
      (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0).differentiable (by simp) x
  have hrow := second_row_split g L q (referenceRadius δr Ar p L) (PH δr Ar p q) (PL δr Ar p q x)
    (Uin F0) x i j hEh hu hc
  have hchange := congrArg₂
    (fun (v : Neg) (e : Fin 3 → Neg) => v+
      PL δr Ar p q x i
        (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x j) +
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i • e j -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • e k) hw he
  exact hchange.trans hrow


local notation "BF" => higherSFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZ" => higherSZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BC" => higherSFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NEG" => ActualHigherSFormation.nativeHigherSNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0

/-- Literal HigherS coefficient extraction on the original finite input support. -/
theorem actual_higherS_frame_coefficient_at_support (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : x ∈ TS F0) :
    NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x =
      (∑ m : Fin 3, BF g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
      CZ g2 δr Ar p q x (Uin F0 x) := by
  let R := referenceRadius δr Ar p L
  let r := R x
  let u := Uin F0
  let Q : Fin 3 → Fin 3 → ℝ := fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q x i j
  let b : Fin 3 → ℝ := fun i => normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let Γ : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j
  let f : Fin 3 → ℝ := fun i => referenceRadiusHorizontalLogDerivative g L q R x i
  let EH0 : Fin 3 → Hi →L[ℝ] Half := fun j => PH δr Ar p q j x
  let EL0 : Fin 3 → Half →L[ℝ] Neg := PL δr Ar p q x
  let E0 : Fin 3 → Half := fun j => MQ q R x j (u x)
  let E1 : Fin 3 → Half := fun j => EH0 j (u x)
  let dm : Fin 3 → Half := fun i => IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))
  let Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg :=
    secondZeroRow g L q R (PH δr Ar p q) EL0 x
  let Ahi : Fin 3 → Hi →L[ℝ] Half := sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ)
  let Alo : Fin 3 → Half →L[ℝ] Neg := sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ)
  let rows : Fin 3 → Fin 3 → Neg := fun i j =>
    referenceLowerWeightedHorizontalAction g L q R (fun y => MQ q R y j (u y)) x i +
      EL0 i (referenceHighWeightedHorizontalAction g L q R u x j) + f i • JL (E0 j) -
      ∑ k : Fin 3, Γ i j k • JL (E0 k)
  have he : E0 = E1 := by
    funext j
    exact congrArg (fun v : R3 → Half => v x)
      (original_high_field_eq_canonical g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm hJac δr Ar p hδr hAr q hq F0 hT j)
  have hr : rows = fun i j => EL0 j (dm i)+EL0 i (dm j)+Z i j (u x) := by
    funext i j
    exact actual_second_row_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac δr Ar p hδr hAr q hq F0 hT x hx i j
  have hs : ActualHigherSFormation.nativeHigherSSecondNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      g2 q R u x =
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (EL0 j (dm i)+EL0 i (dm j)+Z i j (u x))) +
      r^2 • (∑ i : Fin 3, b i • JL (EH0 i (u x))) := by
    change r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • rows i j) +
      r^2 • (∑ i : Fin 3, b i • JL (E0 i)) = _
    exact congrArg₂ (fun (rs : Fin 3 → Fin 3 → Neg) (es : Fin 3 → Half) =>
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • rs i j) +
      r^2 • (∑ i : Fin 3, b i • JL (es i))) hr he
  have ha : ActualHigherSFormation.nativeHigherSAngularNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      g2 q R u x = r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (Alo i (EH0 j (u x))+EL0 i (Ahi j (u x)))) := by
    change r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (Alo i (E0 j)+EL0 i (Ahi j (u x)))) = _
    exact congrArg (fun es : Fin 3 → Half => r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Alo i (es j)+EL0 i (Ahi j (u x))))) he
  have hd : ActualHigherSFormation.nativeHigherSDoubleNegative hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      g2 q R u x = r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • EL0 i (EH0 j (u x))) := by
    change r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • EL0 i (E0 j)) = _
    exact congrArg (fun es : Fin 3 → Half => r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • EL0 i (es j))) he
  have hsum := congrArg₂ (fun a b : Neg => a+b)
    (congrArg₂ (fun a b : Neg => a+b) hs ha) hd
  exact hsum.trans (coefficient_assembly r Q b Z EH0 EL0 Alo Ahi dm (u x))


/-- The original negative HigherS vanishes off the original input support,
proved through its already checked full-output graph. -/
lemma nativeHigherSNegative_eq_zero_off_support (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : x ∉ TS F0) : NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x = 0 := by
  have hFacts := ActualCommonQuadraticFormationConsumer.higherSParentFacts_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  have hRoom := actual_profile_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac δr Ar p hδr hAr q F0 hT
  have hg0 := ActualHigherSFormation.nativeHigherSHalf_negative_graph hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 F0 hRoom x
  have hz := ActualHigherSFormation.nativeHigherSHalf_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg δ0 W g2 F0 x hx
  exact hg0.symm.trans ((congrArg (fun v : Half => JL v) hz).trans (map_zero JL))

/-- Exact HigherS coefficient extraction on ALL of R3, with the original
membership-only support premise and no finite-output assumption. -/
theorem actual_higherS_frame_coefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x =
      (∑ m : Fin 3, BF g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
      CZ g2 δr Ar p q x (Uin F0 x) := by
  by_cases hx : x ∈ TS F0
  · exact actual_higherS_frame_coefficient_at_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x hx
  · have hn := nativeHigherSNegative_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x hx
    have hu0 := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx
    have he := ActualHigherSFormation.higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx
    have hd : fderiv ℝ (Uin F0) x = 0 := he.fderiv_eq.trans (fderiv_const_apply _)
    have hr : (∑ m : Fin 3, BF g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
        CZ g2 δr Ar p q x (Uin F0 x) = 0 := by
      simp only [hd,ContinuousLinearMap.zero_apply,map_zero,Finset.sum_const_zero,hu0,add_zero]
    exact hn.trans hr.symm

/-- The exact SAME coefficient identity in original fixed coordinate directions. -/
theorem actual_higherS_coordinate_coefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x =
      (∑ l : Fin 3, BC g2 δr Ar p q x l
        (IH (fderiv ℝ (Uin F0) x (ReferenceDensityBounds.coordinateDirection l)))) +
      CZ g2 δr Ar p q x (Uin F0 x) := by
  have hf := actual_higherS_frame_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x
  have hc := frame_to_coordinate (BF g2 δr Ar p q x) (referenceMetricGramFrame g L (q,x)) (Uin F0) x
  exact hf.trans (congrArg (fun v : Neg => v+CZ g2 δr Ar p q x (Uin F0 x)) hc)

/-- One original room/radius before metrics, profiles and inputs; every
coefficient identity is derived, with all dependencies still explicit. -/
theorem exists_retained_higherS_coefficients (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      ∃ Cm : CRoom hreg δ0 W δ, ∃ hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z,
      ∀ g2 : MatrixField, ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
      ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 → ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      ∀ x : R3, NEG g2 q (referenceRadius δr Ar p L) (Uin F0) x =
        (∑ l : Fin 3, BC g2 δr Ar p q x l
          (IH (fderiv ℝ (Uin F0) x (ReferenceDensityBounds.coordinateDirection l)))) +
        CZ g2 δr Ar p q x (Uin F0 x) := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 δr Ar p hδr hAr q hq F0 hT x
  exact actual_higherS_coordinate_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm hJac g2 δr Ar p hδr hAr q hq F0 hT x

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoefficientExtraction
