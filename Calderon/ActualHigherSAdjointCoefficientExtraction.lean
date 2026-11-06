import Calderon.ActualHigherSCoefficientExtraction
import Calderon.ActualHigherSAdjointFormation
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointCoefficientExtraction
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualHigherSCoefficientExtraction ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth SphereHarmonic.DegreeGraphLifting ReferenceDensityBounds
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

private lemma adjoint_row_reassociate {M : Type*} [AddCommGroup M]
    (a b c d e f h k l : M) :
    -(a+b)+c-((d+e)+f)+h+k-l = -a-d+(-b+c-e-f+h+k-l) := by abel

/-- Every zero-base term in the normalized Second adjoint except the two
coefficient/density corrections (which are kept separately, without dividing by Q). -/
def adjointSecondZeroRow (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : Fin 3 → R3 → (Hi →L[ℝ] Half)) (El : Fin 3 → Half →L[ℝ] Neg)
    (x : R3) (i j : Fin 3) : Hi →L[ℝ] Neg :=
  -((El j).comp (weightedHighZero g L q R x i)) +
    (2*referenceRadiusHorizontalLogDerivative g L q R x i) •
      (El j).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ)) -
    (JL).comp (fderiv ℝ (Eh i) x (referenceMetricGramFrame g L (q,x) j)) -
    (weightedLowerZero g L q R x j).comp (Eh i x) +
    (2*referenceRadiusHorizontalLogDerivative g L q R x j) •
      (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp (Eh i x) +
    referenceRadiusHorizontalLogDerivative g L q R x i • (JL).comp (Eh j x) -
    ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • (JL).comp (Eh k x)

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevShiftedDegreeL
  referenceMetricGramFrame referenceRadiusHorizontalLogDerivative
  referenceHighWeightedHorizontalAction referenceLowerWeightedHorizontalAction
  weightedHighZero weightedLowerZero

/-- Extract the exact two negative first-base terms of one actual adjoint row.
No finite output or symmetry of Q is used. -/
lemma adjoint_second_row_split (g : MatrixField) (L q : ℝ) (R : R3 → ℝ)
    (Eh : Fin 3 → R3 → (Hi →L[ℝ] Half)) (El : Fin 3 → Half →L[ℝ] Neg)
    (u : R3 → Hi) (x : R3) (i j : Fin 3)
    (hEh : DifferentiableAt ℝ (Eh i) x) (hu : DifferentiableAt ℝ u x)
    (hcompat : ∀ v : Hi, JL (Eh i x v) = El i (IH v)) :
    -(El j (referenceHighWeightedHorizontalAction g L q R u x i)) +
      (2*referenceRadiusHorizontalLogDerivative g L q R x i) •
        El j (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x)) -
      referenceLowerWeightedHorizontalAction g L q R (fun y => Eh i y (u y)) x j +
      (2*referenceRadiusHorizontalLogDerivative g L q R x j) •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (Eh i x (u x))) +
      referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x)) =
      -(El j (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i)))) -
        El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))) +
        adjointSecondZeroRow g L q R Eh El x i j (u x) := by
  have hA := congrArg (fun z : Half => El j z) (high_action_split g L q R u x i)
  have hA' := hA.trans (map_add (El j) _ _)
  have hB := lower_action_family g L q R (Eh i) (El i) u x j hEh hu hcompat
  have hChange := congrArg₂ (fun (A B0 : Neg) => -A +
    (2*referenceRadiusHorizontalLogDerivative g L q R x i) •
      El j (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x)) - B0 +
    (2*referenceRadiusHorizontalLogDerivative g L q R x j) •
      (sphereSobolevShiftedDegreeL (1/2 : ℝ) (Eh i x (u x))) +
    referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)) -
    ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
      (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x))) hA' hB
  refine hChange.trans ?_
  simpa only [adjointSecondZeroRow,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply] using adjoint_row_reassociate
      (El j (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) i))))
      (El j (weightedHighZero g L q R x i (u x)))
      ((2*referenceRadiusHorizontalLogDerivative g L q R x i) •
        El j (sphereSobolevShiftedDegreeL (3/2 : ℝ) (u x)))
      (El i (IH (fderiv ℝ u x (referenceMetricGramFrame g L (q,x) j))))
      (JL (fderiv ℝ (Eh i) x (referenceMetricGramFrame g L (q,x) j) (u x)))
      (weightedLowerZero g L q R x j (Eh i x (u x)))
      ((2*referenceRadiusHorizontalLogDerivative g L q R x j) •
        (sphereSobolevShiftedDegreeL (1/2 : ℝ) (Eh i x (u x))))
      (referenceRadiusHorizontalLogDerivative g L q R x i • JL (Eh j x (u x)))
      (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j • JL (Eh k x (u x)))


/-- Exact derivative coefficient of Sdag, with both Q orders retained. -/
def adjointFirstFrameCoefficient (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (m : Fin 3) : Half →L[ℝ] Neg :=
  -firstFrameCoefficient r Q El m

lemma adjoint_first_frame_coefficient_apply (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (El : Fin 3 → Half →L[ℝ] Neg) (v : Fin 3 → Half) :
    r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (-(El j (v i)) - El i (v j))) =
      ∑ m : Fin 3, adjointFirstFrameCoefficient r Q El m (v m) := by
  have h := congrArg (fun z : Neg => -z) (first_frame_coefficient_apply r Q El v)
  simpa only [adjointFirstFrameCoefficient,ContinuousLinearMap.neg_apply,
    neg_smul,← smul_neg,← Finset.sum_neg_distrib,← neg_add,sub_eq_add_neg] using h

/-- Complete derivative-free adjoint coefficient. d1/d2 are the two actual
positive-density-normalized derivatives of R² Q, not quotients by Q. -/
def adjointZeroCoefficient (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) : Hi →L[ℝ] Neg :=
  ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j) -
    ∑ i : Fin 3, ∑ j : Fin 3,
      (d1 i j • (JL).comp (Eh j) + d2 i j • (JL).comp (Eh i))) +
    r^2 • (∑ i : Fin 3, b i • (JL).comp (Eh i))) +
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((El j).comp (Ahi i)+(Alo j).comp (Eh i))) +
    r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j).comp (Eh i))

private lemma assemble_adjoint_values {E : Type*} [AddCommGroup E]
    (a b z d e f g c : E) (ha : a=b+z) (hc : c=((z-d)+e)+f+g) :
    ((a-d)+e)+f+g=b+c := by rw [ha,hc]; abel

/-- Collect the literal reversed terms, without a symmetry premise or a finite output. -/
lemma adjoint_coefficient_assembly (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half)
    (v : Fin 3 → Half) (u : Hi) :
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (-(El j (v i)) - El i (v j) + Z i j u)) -
      ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • JL (Eh j u)+d2 i j • JL (Eh i u))) +
      r^2 • (∑ i : Fin 3, b i • JL (Eh i u))) +
    r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j (Ahi i u)+Alo j (Eh i u))) +
    r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • El j (Eh i u)) =
      (∑ m : Fin 3, adjointFirstFrameCoefficient r Q El m (v m)) +
        adjointZeroCoefficient r Q b d1 d2 Z Eh El Alo Ahi u := by
  have hs : r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (-(El j (v i)) - El i (v j) + Z i j u)) =
      (∑ m : Fin 3, adjointFirstFrameCoefficient r Q El m (v m)) +
      r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j u) := by
    rw [← adjoint_first_frame_coefficient_apply r Q El v]
    simp only [smul_add,Finset.sum_add_distrib]
  have hz : adjointZeroCoefficient r Q b d1 d2 Z Eh El Alo Ahi u =
      ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j u) -
        ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • JL (Eh j u)+d2 i j • JL (Eh i u))) +
        r^2 • (∑ i : Fin 3, b i • JL (Eh i u))) +
      r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El j (Ahi i u)+Alo j (Eh i u))) +
      r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • El j (Eh i u)) := by
    simp only [adjointZeroCoefficient,add_apply,sub_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply]
  exact assemble_adjoint_values _ _ _ _ _ _ _ _ hs hz

/-- Normalize only by the positive physical density, never by a principal coefficient. -/
private lemma normalized_density_row {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →L[ℝ] F) (μ c fi fj di dj : ℝ) (hμ : μ ≠ 0)
    (a b d h ei ej : E) (Γ : Fin 3 → ℝ) (ek : Fin 3 → E) :
    μ⁻¹ • J (((-(μ*c)) • a + (2*(μ*c*fi)) • b - di • ej) +
      ((-(μ*c)) • d + (2*(μ*c*fj)) • h - dj • ei) +
      (μ*c*fi) • ej - ∑ k : Fin 3, (μ*c*Γ k) • ek k) =
    c • (-J a + (2*fi) • J b - J d + (2*fj) • J h + fi • J ej -
      ∑ k : Fin 3, Γ k • J (ek k)) -
      (μ⁻¹*di) • J ej - (μ⁻¹*dj) • J ei := by
  have h1 : μ⁻¹ * (-(μ*c)) = -c := by field_simp [hμ]
  have h2 : μ⁻¹ * (2*(μ*c*fi)) = c*(2*fi) := by field_simp [hμ]
  have h3 : μ⁻¹ * (2*(μ*c*fj)) = c*(2*fj) := by field_simp [hμ]
  have h4 : μ⁻¹ * (μ*c*fi) = c*fi := by field_simp [hμ]
  have h5 (k : Fin 3) : μ⁻¹ * (μ*c*Γ k) = c*Γ k := by field_simp [hμ]
  simp only [map_add,map_sub,map_sum,map_smul,smul_add,smul_sub,Finset.smul_sum,smul_smul,
    h1,h2,h3,h4,h5]
  module


/-- Typed image substitution for one density row, before concrete geometric
coefficient bodies are instantiated. -/
private lemma normalized_density_row_of_images {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →L[ℝ] F) (μ c fi fj di dj : ℝ) (hμ : μ ≠ 0)
    (a b d h ei ej : E) (Γ : Fin 3 → ℝ) (ek : Fin 3 → E)
    (A B D H EI : F) (ha : J a=A) (hb : J b=B) (hd : J d=D)
    (hh : J h=H) (hei : J ei=EI) :
    μ⁻¹ • J (((-(μ*c)) • a + (2*(μ*c*fi)) • b - di • ej) +
      ((-(μ*c)) • d + (2*(μ*c*fj)) • h - dj • ei) +
      (μ*c*fi) • ej - ∑ k : Fin 3, (μ*c*Γ k) • ek k) =
    c • (-A + (2*fi) • B - D + (2*fj) • H + fi • J ej -
      ∑ k : Fin 3, Γ k • J (ek k)) -
      (di/μ) • J ej - (dj/μ) • EI := by
  have hn := normalized_density_row J μ c fi fj di dj hμ a b d h ei ej Γ ek
  rw [ha,hb,hd,hh,hei] at hn
  simpa only [div_eq_mul_inv,mul_comm] using hn
private lemma normalized_density_sum {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E →L[ℝ] F) (μ : ℝ) (hμ : μ ≠ 0)
    (a : Fin 3 → Fin 3 → E) (b : Fin 3 → E) (c : Fin 3 → ℝ) :
    μ⁻¹ • J ((∑ i : Fin 3, ∑ j : Fin 3, a i j) +
      ∑ i : Fin 3, (μ*c i) • b i) =
    (∑ i : Fin 3, ∑ j : Fin 3, μ⁻¹ • J (a i j)) +
      ∑ i : Fin 3, c i • J (b i) := by
  simp only [map_add,map_sum,map_smul,smul_add,Finset.smul_sum,smul_smul,
    inv_mul_cancel_left₀ hμ]

private lemma collect_second_rows {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (d1 d2 : Fin 3 → Fin 3 → ℝ) (z : Fin 3 → Fin 3 → E) (e : Fin 3 → E) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ((r^2*Q i j) • z i j - d1 i j • e j - d2 i j • e i)) +
      (∑ i : Fin 3, (r^2*b i) • e i) =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • z i j) -
      ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • e j+d2 i j • e i)) +
      r^2 • (∑ i : Fin 3, b i • e i)) := by
  simp only [mul_smul,Finset.smul_sum,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  abel

section Actual
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => ActualGeneratorEPairedGainedEndpoints.reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => ActualGeneratorEPairedGainedEndpoints.reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "UD" => ActualHigherSFormation.higherSReferenceInput hO hD g L hg
local notation "UB" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- The original finite differential input lift, with its actual inclusion. -/
lemma referenceInput_inclusion (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar)
    (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD) (i : Fin 3) (x : R3) :
    IH (UD δr Ar p hδr hAr q F0 i x) =
      referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i := by
  exact ActualHigherSSecondAdjoint.referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F0 i x

/-- Actual reverse family after the original profile substitution. -/
def reverseProfileHigh (δr Ar : ℝ) (p : ℕ) (q : ℝ) (j : Fin 3) (x : R3) : Hi →L[ℝ] Half :=
  eH j ((Tq δr Ar p q) x)
def reverseProfileLow (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (j : Fin 3) : Half →L[ℝ] Neg :=
  eL j ((Tq δr Ar p q) x)
local notation "PH" => reverseProfileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PL" => reverseProfileLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma differentiableAt_reverseProfileHigh (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (j : Fin 3) (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    DifferentiableAt ℝ (PH δr Ar p q j) x := by
  have ht := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q
  exact ((Cm.rev.germHigh j _ hx).comp x ht.contDiffAt).differentiableAt (by simp)

/-- The differentiated reverse lift is transported by a WHOLE-field equality.
No equality merely on a closed parameter set is differentiated. -/
theorem weighted_reverseLift_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (i j : Fin 3) (x : R3) :
    JL (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (VR hreg δ0 W δr Ar p q F0 i) x j) =
    referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L)
      (fun y => PH δr Ar p q i y (Uin F0 y)) x j := by
  have hs := ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm.rev δr Ar p hδr hAr q F0 hT i
  have he : (fun y => IH (VR hreg δ0 W δr Ar p q F0 i y)) =
      (fun y => PH δr Ar p q i y (Uin F0 y)) := by
    funext y
    exact ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm.rev δr Ar p q F0 hT i y
  have hw := ActualHigherSFormation.referenceWeightedHorizontalAction_inclusion g L q
    (referenceRadius δr Ar p L) (VR hreg δ0 W δr Ar p q F0 i) x j
    (hs.differentiable (by simp) x)
  exact hw.trans (congrArg (fun v : R3 → Half =>
    referenceLowerWeightedHorizontalAction g L q (referenceRadius δr Ar p L) v x j) he)

/-- Reverse compatibility is the original retained common-room identity. -/
lemma reverse_profile_compat (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) (v : Hi) :
    JL (PH δr Ar p q j x v) = PL δr Ar p q x j (IH v) :=
  Cm.rev.compat j _ hx v

/-- The genuine finite derivative input after reverse compatibility. -/
lemma reverse_reference_input_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (i j : Fin 3) :
    JL (PH δr Ar p q j x (UD δr Ar p hδr hAr q F0 i x)) =
    PL δr Ar p q x j
      (referenceHighWeightedHorizontalAction g L q (referenceRadius δr Ar p L) (Uin F0) x i) :=
  (Cm.rev.compat j _ hx _).trans (congrArg (PL δr Ar p q x j)
    (ActualHigherSSecondAdjoint.referenceInput_inclusion hO hD g hg L q δr Ar p hδr hAr F0 i x))

/-- The finite degree input includes the physical degree k, including zero. -/
lemma reverse_degree_input_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (j : Fin 3) :
    JL (PH δr Ar p q j x (UB F0 x)) =
      PL δr Ar p q x j (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F0 x)) :=
  (Cm.rev.compat j _ hx _).trans (congrArg (PL δr Ar p q x j)
    (inclusion_finiteCoreSobolevLift_coreDegree hO hD F0 x))

/-- Degree transport of the genuine reverse higher lift uses its proven inclusion. -/
lemma reverse_degree_lift_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (δr Ar : ℝ) (p : ℕ) (q : ℝ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (i : Fin 3) (x : R3) :
    JL (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W δr Ar p q F0 i x)) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (PH δr Ar p q i x (Uin F0 x)) := by
  have hd := congrArg (fun A : Hi →L[ℝ] Neg => A (VR hreg δ0 W δr Ar p q F0 i x))
    sphereSobolevShiftedDegree_high_half_compatibility
  have hi := ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm.rev δr Ar p q F0 hT i x
  exact hd.trans (congrArg (sphereSobolevShiftedDegreeL (1/2 : ℝ) : Half →L[ℝ] Neg) hi)

/-- Actual reverse derivative coefficient, with both original Q orders. -/
def higherSAdjointFirstFrameCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (q : ℝ) (x : R3) (m : Fin 3) : Half →L[ℝ] Neg :=
  adjointFirstFrameCoefficient (referenceRadius δr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x) (PL δr Ar p q x) m

/-- Full actual derivative-free coefficient. Each density correction is divided
only by the original positive physical density. -/
def higherSAdjointZeroCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ)
    (q : ℝ) (x : R3) : Hi →L[ℝ] Neg :=
  adjointZeroCoefficient (referenceRadius δr Ar p L x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x)
    (fun i => ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x))
    (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x /
        referenceDensityFamily g L (q,x))
    (fun i j => ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j
      (ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p i j) x /
        referenceDensityFamily g L (q,x))
    (adjointSecondZeroRow g L q (referenceRadius δr Ar p L) (PH δr Ar p q) (PL δr Ar p q x) x)
    (fun i => PH δr Ar p q i x) (PL δr Ar p q x)
    (loweringLow hF hO hD) (loweringHigh hF hO hD)

/-- Literal angular reverse after the genuine lowering and reverse-lift inclusions. -/
lemma angular_adjoint_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    JL (ActualHigherSAngularAdjoint.revAngularHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p q F0 x) =
    referenceRadius δr Ar p L x • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      (PL δr Ar p q x j (loweringHigh hF hO hD i (Uin F0 x)) +
        loweringLow hF hO hD j (PH δr Ar p q i x (Uin F0 x)))) := by
  have hr (i j : Fin 3) :
      JL (eH j ((Tq δr Ar p q) x) (ActualHigherSAngularAdjoint.loweringInput hF hO hD F0 i x)) =
      PL δr Ar p q x j (loweringHigh hF hO hD i (Uin F0 x)) :=
    (Cm.rev.compat j _ hx _).trans (congrArg (PL δr Ar p q x j)
      (ActualHigherSAngularAdjoint.loweringInput_inclusion hF hO hD F0 i x))
  have hl (i j : Fin 3) :
      JL (loweringHigh hF hO hD j (VR hreg δ0 W δr Ar p q F0 i x)) =
      loweringLow hF hO hD j (PH δr Ar p q i x (Uin F0 x)) :=
    (v017_inclusion_loweringHigh hF hO hD j _).trans
      (congrArg (loweringLow hF hO hD j)
        (ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg δ0 W δ Cm.rev δr Ar p q F0 hT i x))
  simp only [ActualHigherSAngularAdjoint.revAngularHalf,map_smul,map_sum,map_add,hr,hl]

/-- Literal quadratic reverse, retaining the original j,i order. -/
lemma double_adjoint_negative (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    JL (ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p q F0 x) =
    (referenceRadius δr Ar p L x)^3 • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
      PL δr Ar p q x j (PH δr Ar p q i x (Uin F0 x))) := by
  have hr (i j : Fin 3) : JL (eH j ((Tq δr Ar p q) x) (VR hreg δ0 W δr Ar p q F0 i x)) =
      PL δr Ar p q x j (PH δr Ar p q i x (Uin F0 x)) :=
    (Cm.rev.compat j _ hx _).trans (congrArg (PL δr Ar p q x j)
      (ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm.rev δr Ar p q F0 hT i x))
  simp only [ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf,map_smul,map_sum,hr]

local notation "SC" g2:max δr:max Ar:max p:max q:max =>
  ActualHigherSSecondAdjoint.secondCoefficient g g2 L q δr Ar p
local notation "Mu" q:max x:max => referenceDensityFamily g L (q,x)
local notation "DC1" g2:max δr:max Ar:max p:max q:max x:max i:max j:max =>
  ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q i ((SC g2 δr Ar p q) i j) x
local notation "DC2" g2:max δr:max Ar:max p:max q:max x:max i:max j:max =>
  ActualHigherSSecondAdjoint.densityDerivativeCoefficient g L q j ((SC g2 δr Ar p q) i j) x
local notation "ZD" δr:max Ar:max p:max q:max x:max =>
  adjointSecondZeroRow g L q (referenceRadius δr Ar p L) (PH δr Ar p q) (PL δr Ar p q x) x

/-- Exact negative coefficient form of the original normalized Second reverse. -/
lemma second_adjoint_negative_at (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ)
    (x : R3) (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    JL (ActualHigherSSecondAdjoint.revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
    (((referenceRadius δr Ar p L x)^2 • (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q x i j •
        (-(PL δr Ar p q x j (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i)))) -
          PL δr Ar p q x i (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) j))) +
          (ZD δr Ar p q x) i j (Uin F0 x))) -
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((DC1 g2 δr Ar p q x i j / Mu q x) • JL (PH δr Ar p q j x (Uin F0 x)) +
         (DC2 g2 δr Ar p q x i j / Mu q x) • JL (PH δr Ar p q i x (Uin F0 x)))) +
      (referenceRadius δr Ar p L x)^2 • (∑ i : Fin 3,
        ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x) •
          JL (PH δr Ar p q i x (Uin F0 x)))) := by
  classical
  let R := referenceRadius δr Ar p L
  let μ := Mu q x
  let c := SC g2 δr Ar p q
  let f := referenceRadiusHorizontalLogDerivative g L q R x
  let Γ := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j
  let e := fun j : Fin 3 => PH δr Ar p q j x (Uin F0 x)
  let d1 := fun i j : Fin 3 => DC1 g2 δr Ar p q x i j
  let d2 := fun i j : Fin 3 => DC2 g2 δr Ar p q x i j
  let b := fun i : Fin 3 => ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x)
  let raw : Fin 3 → Fin 3 → Half := fun i j =>
    ((-(μ*c i j x)) • PH δr Ar p q j x (UD δr Ar p hδr hAr q F0 i x) +
      (2*(μ*c i j x*f i)) • PH δr Ar p q j x (UB F0 x) - d1 i j • e j) +
    ((-(μ*c i j x)) • referenceHighWeightedHorizontalAction g L q R
      (VR hreg δ0 W δr Ar p q F0 i) x j +
      (2*(μ*c i j x*f j)) • sphereSobolevShiftedDegreeL (3/2 : ℝ)
        (VR hreg δ0 W δr Ar p q F0 i x) - d2 i j • IH (VR hreg δ0 W δr Ar p q F0 i x)) +
      (μ*c i j x*f i) • e j - ∑ k : Fin 3, (μ*c i j x*Γ i j k) • e k
  have hμ : μ ≠ 0 := ne_of_gt (referenceDensityFamily_pos g hg L (q,x))
  have hRaw : ActualHigherSSecondAdjoint.revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x =
      (∑ i : Fin 3, ∑ j : Fin 3, raw i j) + ∑ i : Fin 3, (μ*((R x)^2*b i)) • e i := rfl
  have hNorm := (map_smul JL μ⁻¹
    (ActualHigherSSecondAdjoint.revSecondDensityHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x)).trans
    ((congrArg (fun v : Half => μ⁻¹ • JL v) hRaw).trans
      (normalized_density_sum (JL : Half →L[ℝ] Neg) μ hμ raw e (fun i => (R x)^2*b i)))
  have hRef (i j : Fin 3) := reverse_reference_input_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p hδr hAr q F0 x hx i j
  have hDeg (j : Fin 3) := reverse_degree_input_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p q F0 x hx j
  have hDW (i j : Fin 3) := weighted_reverseLift_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p hδr hAr q F0 hT i j x
  have hB (i : Fin 3) := reverse_degree_lift_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm δr Ar p q F0 hT i x
  have hVR (i : Fin 3) : JL (IH (VR hreg δ0 W δr Ar p q F0 i x)) = JL (e i) :=
    congrArg (JL : Half →L[ℝ] Neg)
      (ActualReverseEHigherLift.reverseEHigherLift_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm.rev δr Ar p q F0 hT i x)
  let z := fun i j : Fin 3 =>
    -(PL δr Ar p q x j (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i)))) -
      PL δr Ar p q x i (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) j))) +
      (ZD δr Ar p q x) i j (Uin F0 x)
  have hu : DifferentiableAt ℝ (Uin F0) x :=
    (contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0).differentiable (by simp) x
  have hRow (i j : Fin 3) : μ⁻¹ • JL (raw i j) =
      c i j x • z i j - (d1 i j / μ) • JL (e j) - (d2 i j / μ) • JL (e i) := by
    have hs := adjoint_second_row_split g L q R (PH δr Ar p q) (PL δr Ar p q x) (Uin F0) x i j
      (differentiableAt_reverseProfileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W δ Cm δr Ar p hδr hAr q i x hx) hu (Cm.rev.compat i _ hx)
    have he : μ⁻¹ • JL (raw i j) = c i j x •
      (-(PL δr Ar p q x j (referenceHighWeightedHorizontalAction g L q R (Uin F0) x i)) +
        (2*f i) • PL δr Ar p q x j (sphereSobolevShiftedDegreeL (3/2 : ℝ) (Uin F0 x)) -
        referenceLowerWeightedHorizontalAction g L q R (fun y => PH δr Ar p q i y (Uin F0 y)) x j +
        (2*f j) • sphereSobolevShiftedDegreeL (1/2 : ℝ) (e i) + f i • JL (e j) -
        ∑ k : Fin 3, Γ i j k • JL (e k)) - (d1 i j / μ) • JL (e j) - (d2 i j / μ) • JL (e i) := by
      exact normalized_density_row_of_images (JL : Half →L[ℝ] Neg) μ (c i j x) (f i) (f j)
        (d1 i j) (d2 i j) hμ
        (PH δr Ar p q j x (UD δr Ar p hδr hAr q F0 i x))
        (PH δr Ar p q j x (UB F0 x))
        (referenceHighWeightedHorizontalAction g L q R (VR hreg δ0 W δr Ar p q F0 i) x j)
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (VR hreg δ0 W δr Ar p q F0 i x))
        (IH (VR hreg δ0 W δr Ar p q F0 i x)) (e j) (Γ i j) e
        _ _ _ _ _ (hRef i j) (hDeg j) (hDW i j) (hB i) (hVR i)
    exact he.trans (congrArg (fun v : Neg => c i j x • v -
      (d1 i j / μ) • JL (e j) - (d2 i j / μ) • JL (e i)) hs)
  have hRows : (∑ i : Fin 3, ∑ j : Fin 3, μ⁻¹ • JL (raw i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (c i j x • z i j - (d1 i j / μ) • JL (e j) - (d2 i j / μ) • JL (e i)) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hRow i j))
  have hSum := hNorm.trans (congrArg (fun v : Neg => v +
    ∑ i : Fin 3, ((R x)^2*b i) • JL (e i)) hRows)
  exact hSum.trans (collect_second_rows (R x)
    (referenceDensityPrincipalFrameCoefficient g g2 L q x) b
    (fun i j => d1 i j / μ) (fun i j => d2 i j / μ) z (fun i => JL (e i)))

local notation "BFdag" => higherSAdjointFirstFrameCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CZdag" => higherSAdjointZeroCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ADJ" => ActualHigherSAdjointFormation.higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The complete literal Sdag dictionary on the retained input support. -/
theorem actual_higherS_adjoint_frame_coefficient_at_support (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) (hx : x ∈ TS F0) :
    JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
      (∑ m : Fin 3, BFdag g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
      CZdag g2 δr Ar p q x (Uin F0 x) := by
  have hs := second_adjoint_negative_at g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hT x (hT x hx)
  have ha := angular_adjoint_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p q F0 hT x (hT x hx)
  have hd := double_adjoint_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p q F0 hT x (hT x hx)
  have hsum := congrArg₂ (fun (s a0 : Neg) => s+a0) hs ha
  have hsum' := congrArg₂ (fun (sa d : Neg) => sa+d) hsum hd
  have hmap : JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
      (JL (ActualHigherSSecondAdjoint.revSecondHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p hδr hAr q F0 x) +
       JL (ActualHigherSAngularAdjoint.revAngularHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p q F0 x)) +
       JL (ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg δ0 W g2 δr Ar p q F0 x) := by
    simp only [ActualHigherSAdjointFormation.higherSAdjointHalf,map_add]
  exact (hmap.trans hsum').trans
    (adjoint_coefficient_assembly (referenceRadius δr Ar p L x)
      (referenceDensityPrincipalFrameCoefficient g g2 L q x)
      (fun i => ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x))
      (fun i j => DC1 g2 δr Ar p q x i j / Mu q x)
      (fun i j => DC2 g2 δr Ar p q x i j / Mu q x)
      (ZD δr Ar p q x) (fun i => PH δr Ar p q i x) (PL δr Ar p q x)
      (loweringLow hF hO hD) (loweringHigh hF hO hD)
      (fun i => IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) i))) (Uin F0 x))

/-- Global exact coefficient identity; off support the input and every first base
jet vanish on a neighborhood, so no unrelated profile germ is needed there. -/
theorem actual_higherS_adjoint_frame_coefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) (x : R3) :
    JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
      (∑ m : Fin 3, BFdag g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
      CZdag g2 δr Ar p q x (Uin F0 x) := by
  by_cases hx : x ∈ TS F0
  · exact actual_higherS_adjoint_frame_coefficient_at_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hT x hx
  · have hn := ActualHigherSAdjointFormation.higherSAdjointHalf_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W g2 δr Ar p hδr hAr q F0 x hx
    have hu0 := ActualHigherSFormation.higherSInput_eq_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx
    have he := ActualHigherSFormation.higherSInput_eventually_zero hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q F0 x hx
    have hd : fderiv ℝ (Uin F0) x = 0 := he.fderiv_eq.trans (fderiv_const_apply _)
    have hr : (∑ m : Fin 3, BFdag g2 δr Ar p q x m
        (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
        CZdag g2 δr Ar p q x (Uin F0 x) = 0 := by
      simp only [hd,ContinuousLinearMap.zero_apply,map_zero,Finset.sum_const_zero,hu0,add_zero]
    exact (congrArg (JL : Half →L[ℝ] Neg) hn).trans ((map_zero JL).trans hr.symm)

/-- One original retained W/room before every metric, profile and finite input;
all adjoint coefficients are explicit and require no desired-estimate callback. -/
theorem exists_retained_higherS_adjoint_coefficients (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ Cm : CRoom hreg δ0 W δ,
      ∀ g2 : MatrixField, ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar,
      ∀ q : ℝ, ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) → ∀ x : R3,
      JL (ADJ hreg δ0 W g2 δr Ar p hδr hAr q F0 x) =
        (∑ m : Fin 3, BFdag g2 δr Ar p q x m
          (IH (fderiv ℝ (Uin F0) x (referenceMetricGramFrame g L (q,x) m)))) +
        CZdag g2 δr Ar p q x (Uin F0 x) := by
  have hFull := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hFull with ⟨δ,Cm,_hJac⟩
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,?_⟩
  intro g2 δr Ar p hδr hAr q F0 hT x
  exact actual_higherS_adjoint_frame_coefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg δ0 W δ Cm g2 δr Ar p hδr hAr q F0 hT x

end Actual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAdjointCoefficientExtraction
