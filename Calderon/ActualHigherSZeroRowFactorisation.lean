import Calderon.ActualHigherSZeroParameterFactors
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
open ReferenceDensityBounds ActualHigherSZeroCoefficientJetBounds
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
section GenericRowBridge
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
lemma clear_second_row_of_derivative {κ : Type*} [Fintype κ] (r fi fj li lj : ℝ)
    (D0 DB O1 O2 L1 L2 J G : V) (c : κ → ℝ) (D : κ → V)
    (hd : D0 = DB+∑ k, c k • D k) (hi : r*fi = li) (hj : r*fj = lj) :
    r^2 • (D0+(O1+fi•L1)+(O2+fj•L2)+fi•J-G) =
      r • (r•(DB+O1+O2-G)+(li•L1+lj•L2+li•J))+∑ k, (r^2*c k) • D k := by
  rw [hd]
  have h := clear_second_row r fi fj li lj DB O1 O2 L1 L2 J G c D hi hj
  convert h using 1 <;> module

lemma smul_factored_row {κ : Type*} [Fintype κ] (q r : ℝ) (Z A B : V)
    (h : κ → ℝ) (D : κ → V)
    (hz : r^2 • Z = r • (r•A+B)+∑ k, (r^2*h k) • D k) :
    r^2 • (q•Z) = r • (r•(q•A)+q•B)+∑ k, (r^2*h k) • (q•D k) := by
  have hmain : q • (r • (r•A+B)) = r • (r•(q•A)+q•B) := by module
  have hsum : q • (∑ k, (r^2*h k) • D k) = ∑ k, (r^2*h k) • (q•D k) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm q (r^2*h k) (D k)
  calc
    _ = q • (r^2 • Z) := smul_comm (r^2) q Z
    _ = q • (r • (r•A+B)+∑ k, (r^2*h k) • D k) := congrArg (fun z : V => q•z) hz
    _ = q • (r • (r•A+B))+q • (∑ k, (r^2*h k) • D k) := smul_add _ _ _
    _ = _ := congrArg₂ (fun a b : V => a+b) hmain hsum

lemma sum_factored_rows_two {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (r : ℝ) (Z A B : ι → κ → V) (h : ν → ℝ) (D : ι → κ → ν → V)
    (hz : ∀ i j, r^2 • Z i j = r • (r•A i j+B i j)+∑ k, (r^2*h k) • D i j k) :
    r^2 • (∑ i, ∑ j, Z i j) = r • (r•(∑ i, ∑ j, A i j)+∑ i, ∑ j, B i j)+
      ∑ k, (r^2*h k) • (∑ i, ∑ j, D i j k) :=
  sum_factored_rows r (fun i => ∑ j, Z i j) (fun i => ∑ j, A i j)
    (fun i => ∑ j, B i j) h (fun i k => ∑ j, D i j k)
    (fun i => sum_factored_rows r (Z i) (A i) (B i) h (D i) (hz i))

end GenericRowBridge

section OperatorValueProjection
variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup N] [NormedSpace ℝ N]
lemma operator_row_apply {κ : Type*} [Fintype κ] (r : ℝ) (A B : E →L[ℝ] N)
    (J : H →L[ℝ] N) (c d : κ → ℝ) (C : κ → E →L[ℝ] H) (v : E) :
    (r•(r•A+B)+∑ k, c k • (d k • J.comp (C k))) v =
      r•(r•A v+B v)+∑ k, c k • (d k • J (C k v)) := by
  simp only [add_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply]
end OperatorValueProjection

open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ConformalDepth ReferenceWeightedApproximation ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualGeneratorRadialGainedRows ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting ActualHorizontalNormBridge NormalCoordinatesFrame
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
/-- Literal native constructor boundary, with abstract coefficients before actual parameter substitution. -/
lemma zeroCoefficient_expansion (r : ℝ) (Q : Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (Z : Fin 3 → Fin 3 → Hi →L[ℝ] Neg) (Eh : Fin 3 → Hi →L[ℝ] Half)
    (El Alo : Fin 3 → Half →L[ℝ] Neg) (Ahi : Fin 3 → Hi →L[ℝ] Half) :
    ActualHigherSCoefficientExtraction.zeroCoefficient r Q b Z Eh El Alo Ahi =
      (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • Z i j)+
        r^2 • (∑ i : Fin 3, b i • (JL).comp (Eh i)))+
        r • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • ((Alo i).comp (Eh j)+(El i).comp (Ahi j)))+
        r^3 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • (El i).comp (Eh j)) := rfl
attribute [local irreducible] ActualHigherSCoefficientExtraction.zeroCoefficient

@[instance_reducible] private def factorHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighNormed
@[instance_reducible] private def factorHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorHighSpace
@[instance_reducible] private def factorLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowNormed
@[instance_reducible] private def factorLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] factorLowSpace
@[instance_reducible] private def factorZeroNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroNormed
@[instance_reducible] private def factorZeroSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] factorZeroSpace
@[instance_reducible] private def factorParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] factorParameterNormed
@[instance_reducible] private def factorParameterSpace : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] factorParameterSpace
@[instance_reducible] private def factorDerivativeNormed : NormedAddCommGroup (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeNormed
@[instance_reducible] private def factorDerivativeSpace : NormedSpace ℝ (Tpar →L[ℝ] Hi →L[ℝ] Half) := inferInstance
attribute [local instance] factorDerivativeSpace

attribute [local irreducible] canonicalHigh canonicalLow referenceDensityPrincipalFrameCoefficient
 normalizedSecondDriftFrameJoint referenceMetricGramFrame

section Native
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "XP" => parameterGramFrame g L
local notation "GP" => parameterConnection g L
local notation "OL" => parameterLowerAngular g L
local notation "OH" => parameterHighAngular g L
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "CZc" => ActualHigherSZeroCoefficientJets.canonicalZeroCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QP" g2:max i:max j:max t:max => referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i j
local notation "DP" g2:max i:max t:max => normalizedSecondDriftFrameJoint g g2 L i (t.1.1,t.1.2.1)

local notation "ZR" => regularZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => logarithmicZeroRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PHI" => zeroParameterFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PSI" => zeroHessianFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSCoefficientExtraction.profileHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
attribute [local irreducible] ActualHigherSCoefficientExtraction.secondZeroRow
 ActualHigherSCoefficientExtraction.profileHigh regularZeroRow logarithmicZeroRow parameterGramFrame


lemma regularZeroRow_apply (i j : Fin 3) (t : Tpar) (v : Hi) :
    ZR i j t v = JL (fderiv ℝ (EH j) t (basicTangent t (XP i t)) v)+
      OL i t (EH j t v)+EL i t (OH j t v)-
      ∑ k : Fin 3, GP i k j t • JL (EH k t v) := by
  simp only [regularZeroRow,add_apply,sub_apply,sum_apply,smul_apply,ContinuousLinearMap.comp_apply]

lemma logarithmicZeroRow_apply (i j : Fin 3) (t : Tpar) (v : Hi) :
    ZL i j t v = (t.2 (XP i t)) • sphereSobolevShiftedDegreeL (1/2 : ℝ) (EH j t v)+
      (t.2 (XP j t)) • EL i t (sphereSobolevShiftedDegreeL (3/2 : ℝ) v)+
      (t.2 (XP i t)) • JL (EH j t v) := by
  simp only [logarithmicZeroRow,add_apply,smul_apply,ContinuousLinearMap.comp_apply]

lemma secondZeroRow_apply (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3) (i j : Fin 3) (v : Hi) :
    ActualHigherSCoefficientExtraction.secondZeroRow g L q (referenceRadius δr Ar p L)
      (PH δr Ar p q) (fun k => EL k ((Tq δr Ar p q) x)) x i j v =
      JL (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) v)+
      (referenceLowerHorizontalAngularL g L q x i (PH δr Ar p q j x v)+
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i •
          sphereSobolevShiftedDegreeL (1/2 : ℝ) (PH δr Ar p q j x v))+
      (EL i ((Tq δr Ar p q) x) (referenceHighHorizontalAngularL g L q x j v)+
        referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x j •
          EL i ((Tq δr Ar p q) x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) v))+
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i • JL (PH δr Ar p q j x v)-
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j •
        JL (PH δr Ar p q k x v) := by
  simp only [ActualHigherSCoefficientExtraction.secondZeroRow,
    ActualHigherSCoefficientExtraction.weightedLowerZero,ActualHigherSCoefficientExtraction.weightedHighZero,
    add_apply,sub_apply,smul_apply,sum_apply,ContinuousLinearMap.comp_apply,map_add,map_smul]

lemma regularZeroRow_at_profile_apply (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (i j : Fin 3) (v : Hi) :
    ZR i j ((Tq δr Ar p q) x) v =
      JL (fderiv ℝ (EH j) ((Tq δr Ar p q) x) (basicTangent ((Tq δr Ar p q) x) (XP i ((Tq δr Ar p q) x))) v)+
      referenceLowerHorizontalAngularL g L q x i (PH δr Ar p q j x v)+
      EL i ((Tq δr Ar p q) x) (referenceHighHorizontalAngularL g L q x j v)-
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j •
        JL (PH δr Ar p q k x v) := by
  let t := (Tq δr Ar p q) x
  have hPH (k : Fin 3) : PH δr Ar p q k x v = EH k t v := by
    unfold ActualHigherSCoefficientExtraction.profileHigh
    rfl
  have hXP : XP i t = referenceMetricGramFrame g L (q,x) i := by
    unfold parameterGramFrame
    rfl
  have hOL : OL i t = referenceLowerHorizontalAngularL g L q x i :=
    parameterLowerAngular_eq g hg L i t
  have hOH : OH j t = referenceHighHorizontalAngularL g L q x j :=
    parameterHighAngular_eq g hg L j t
  have h1 := congrArg₂ (fun (A : Half →L[ℝ] Neg) (b : Half) => A b) hOL (hPH j).symm
  have h2 := congrArg (fun z : Half => EL i t z)
    (congrArg (fun A : Hi →L[ℝ] Half => A v) hOH)
  have hG : (∑ k : Fin 3, GP i k j t • JL (EH k t v)) =
      ∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j •
        JL (PH δr Ar p q k x v) := by
    apply Finset.sum_congr rfl
    intro k _
    have hgpk : GP i k j t = referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j :=
      (parameterConnection_eq g hg L i k j t).trans
        (congrArg (fun X : R3 => referenceFrameConnectionCoefficient g L q x X k j) hXP)
    exact congrArg₂ (fun (c : ℝ) (z : Neg) => c•z) hgpk (congrArg JL (hPH k).symm)
  have hAdd := congrArg₂ (fun a b : Neg => a+b)
    (congrArg (fun z : Neg => JL (fderiv ℝ (EH j) t (basicTangent t (XP i t)) v)+z) h1) h2
  exact (regularZeroRow_apply g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v).trans
    (congrArg₂ (fun a b : Neg => a-b) hAdd hG)

lemma logarithmicZeroRow_at_profile_apply (δr Ar : ℝ) (p : ℕ) (q : ℝ) (x : R3)
    (i j : Fin 3) (v : Hi) :
    ZL i j ((Tq δr Ar p q) x) v =
      (((Tq δr Ar p q) x).2 (XP i ((Tq δr Ar p q) x))) •
        sphereSobolevShiftedDegreeL (1/2 : ℝ) (PH δr Ar p q j x v)+
      (((Tq δr Ar p q) x).2 (XP j ((Tq δr Ar p q) x))) •
        EL i ((Tq δr Ar p q) x) (sphereSobolevShiftedDegreeL (3/2 : ℝ) v)+
      (((Tq δr Ar p q) x).2 (XP i ((Tq δr Ar p q) x))) • JL (PH δr Ar p q j x v) := by
  let t := (Tq δr Ar p q) x
  have hPH : PH δr Ar p q j x v = EH j t v := by
    unfold ActualHigherSCoefficientExtraction.profileHigh
    rfl
  have h1 := congrArg (fun z : Half => t.2 (XP i t) • sphereSobolevShiftedDegreeL (1/2 : ℝ) z) hPH.symm
  have h3 := congrArg (fun z : Half => t.2 (XP i t) • JL z) hPH.symm
  exact (logarithmicZeroRow_apply g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v).trans
    (congrArg₂ (fun a b : Neg => a+t.2 (XP j t) • EL i t (sphereSobolevShiftedDegreeL (3/2 : ℝ) v)+b) h1 h3)

/-- Exact complete second-row factorisation, including every original logarithmic term. -/
theorem second_zero_row_factorisation (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (x : R3) (i j : Fin 3)
    (hf : DifferentiableAt ℝ (EH j) ((Tq δr Ar p q) x)) :
    (referenceRadius δr Ar p L x)^2 • ActualHigherSCoefficientExtraction.secondZeroRow
      g L q (referenceRadius δr Ar p L) (PH δr Ar p q)
      (fun k => EL k ((Tq δr Ar p q) x)) x i j =
      referenceRadius δr Ar p L x •
        (referenceRadius δr Ar p L x • ZR i j ((Tq δr Ar p q) x)+ZL i j ((Tq δr Ar p q) x))+
      ∑ mk : Fin 3 × Fin 3,
        ((referenceRadius δr Ar p L x)^2*
          hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x)) •
        ((XP i ((Tq δr Ar p q) x)) mk.1 •
          (JL).comp (fderiv ℝ (EH j) ((Tq δr Ar p q) x) (hessianTangent mk.2))) := by
  let t := (Tq δr Ar p q) x
  let r := referenceRadius δr Ar p L x
  let fi := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x i
  let fj := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δr Ar p L) x j
  have hR := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have hr : r ≠ 0 := (referenceRadius_pos δr Ar p L x hδr hAr).ne'
  have hi : r*fi = t.2 (XP i t) := by
    simpa only [r,fi,t,ActualHigherSFormation.higherSParam,parameterGramFrame] using
      radius_mul_horizontalLogDerivative g L q (referenceRadius δr Ar p L) hR x hr i
  have hj : r*fj = t.2 (XP j t) := by
    simpa only [r,fj,t,ActualHigherSFormation.higherSParam,parameterGramFrame] using
      radius_mul_horizontalLogDerivative g L q (referenceRadius δr Ar p L) hR x hr j
  have hc := fderiv_profileHigh_factor_split g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    δr Ar p hδr hAr q x i j hf
  have hPH (k : Fin 3) : PH δr Ar p q k x = EH k t := by
    unfold ActualHigherSCoefficientExtraction.profileHigh
    rfl
  have hXP (k : Fin 3) : XP k t = referenceMetricGramFrame g L (q,x) k := by
    unfold parameterGramFrame
    rfl
  apply ContinuousLinearMap.ext
  intro v
  have hdc0 := congrArg (fun A : Hi →L[ℝ] Half => JL (A v)) hc
  simp only [add_apply,sum_apply,smul_apply,map_add,map_sum,map_smul] at hdc0
  have hdc : JL (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) v) =
      JL (fderiv ℝ (EH j) t (basicTangent t (XP i t)) v)+
      ∑ mk : Fin 3 × Fin 3, hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x) •
        ((XP i t) mk.1 • JL (fderiv ℝ (EH j) t (hessianTangent mk.2) v)) :=
    (congrArg (fun X : R3 => JL (fderiv ℝ (PH δr Ar p q j) x X v)) (hXP i).symm).trans hdc0
  have hh := clear_second_row_of_derivative (V := Neg) r fi fj (t.2 (XP i t)) (t.2 (XP j t))
    (JL (fderiv ℝ (PH δr Ar p q j) x (referenceMetricGramFrame g L (q,x) i) v))
    (JL (fderiv ℝ (EH j) t (basicTangent t (XP i t)) v))
    (referenceLowerHorizontalAngularL g L q x i (PH δr Ar p q j x v))
    (EL i t (referenceHighHorizontalAngularL g L q x j v))
    (sphereSobolevShiftedDegreeL (1/2 : ℝ) (PH δr Ar p q j x v))
    (EL i t (sphereSobolevShiftedDegreeL (3/2 : ℝ) v))
    (JL (PH δr Ar p q j x v))
    (∑ k : Fin 3, referenceFrameConnectionCoefficient g L q x (referenceMetricGramFrame g L (q,x) i) k j •
      JL (PH δr Ar p q k x v))
    (fun mk : Fin 3 × Fin 3 => hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x))
    (fun mk : Fin 3 × Fin 3 => (XP i t) mk.1 • JL (fderiv ℝ (EH j) t (hessianTangent mk.2) v)) hdc hi hj
  have hLft := congrArg (fun z : Neg => r^2 • z)
    (secondZeroRow_apply g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δr Ar p q x i j v)
  have hReg := regularZeroRow_at_profile_apply g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δr Ar p q x i j v
  have hLog := logarithmicZeroRow_at_profile_apply g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δr Ar p q x i j v
  have hRgt := operator_row_apply r (ZR i j t) (ZL i j t) JL
    (fun mk : Fin 3 × Fin 3 => r^2*hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x))
    (fun mk : Fin 3 × Fin 3 => (XP i t) mk.1)
    (fun mk : Fin 3 × Fin 3 => fderiv ℝ (EH j) t (hessianTangent mk.2)) v
  have hV := congrArg₂ (fun a b : Neg => r•(r•a+b)) hReg hLog
  have hVsum := congrArg (fun z : Neg => z+
    ∑ mk : Fin 3 × Fin 3, (r^2*hessianEntry mk (fderiv ℝ (fderiv ℝ (referenceRadius δr Ar p L)) x)) •
      ((XP i t) mk.1 • JL (fderiv ℝ (EH j) t (hessianTangent mk.2) v))) hV
  exact hLft.trans (hh.trans (hRgt.trans hVsum).symm)

/- Exact literal canonical zero coefficient, from the genuine derivative split and radius clearing. -/
end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroCoefficientFactorisation
