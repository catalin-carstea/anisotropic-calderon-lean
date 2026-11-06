import Calderon.ActualDegreeGramBaseIdentity
import Calderon.ActualDensityPrincipalFrameCoefficientBound
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualHigherSAdjointCoefficientBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualQDegreeBaseContraction
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def gramHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramHighModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def gramLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gramHighNormed gramHighModule gramLowNormed gramLowModule

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RevRoom" => ActualReverseEHigherLift.ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BG" => (Sum.inr () : Generator)

section FiniteCalculus
variable {X0 : Type*} [NormedAddCommGroup X0] [NormedSpace ℝ X0]

private lemma fderiv_sum_apply {ι : Type*} [Fintype ι] (A : ι → X0 → ℝ)
    (x X : X0) (hA : ∀ i, DifferentiableAt ℝ (A i) x) :
    fderiv ℝ (fun y => ∑ i, A i y) x X=∑ i, fderiv ℝ (A i) x X := by
  have hD := fderiv_fun_sum (u := Finset.univ) (fun i _ => hA i)
  simpa using congrArg (fun Q : X0 →L[ℝ] ℝ => Q X) hD

/-- Finite contraction derivative keeps every derivative of the actual coefficient. -/
theorem fderiv_matrix_scalar_contraction (Q A : Fin 3 → Fin 3 → X0 → ℝ)
    (x X : X0) (hQ : ∀ i j, DifferentiableAt ℝ (Q i j) x)
    (hA : ∀ i j, DifferentiableAt ℝ (A i j) x) :
    fderiv ℝ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, Q i j y*A i j y) x X =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ((fderiv ℝ (Q i j) x X)*A i j x+Q i j x*fderiv ℝ (A i j) x X) := by
  have hRow (i : Fin 3) : DifferentiableAt ℝ (fun y => ∑ j : Fin 3, Q i j y*A i j y) x :=
    DifferentiableAt.fun_sum (fun j _ => (hQ i j).mul (hA i j))
  calc
    _ = ∑ i : Fin 3, fderiv ℝ (fun y => ∑ j : Fin 3, Q i j y*A i j y) x X :=
      fderiv_sum_apply _ x X hRow
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hRowD := fderiv_sum_apply (fun j : Fin 3 => fun y => Q i j y*A i j y) x X
        (fun j => (hQ i j).mul (hA i j))
      calc
        _ = ∑ j : Fin 3, fderiv ℝ (fun y => Q i j y*A i j y) x X := hRowD
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          have hProd := congrArg (fun V : X0 →L[ℝ] ℝ => V X) (fderiv_fun_mul (hQ i j) (hA i j))
          simpa [mul_comm,add_comm] using hProd
end FiniteCalculus

private lemma contDiff_fixed_parameter_scalar (f : ℝ × R3 → ℝ)
    (hf : ContDiff ℝ ∞ f) (q : ℝ) : ContDiff ℝ ∞ (fun y : R3 => f (q,y)) := by
  have hEmbed : ContDiff ℝ ∞ (fun y : R3 => (q,y)) := contDiff_const.prodMk contDiff_id
  exact hf.comp hEmbed

attribute [local irreducible] referenceDensityPrincipalFrameCoefficient referenceMetricGramFrame

/-- The actual original principal coefficient is symmetric, from its native positive semidefiniteness. -/
theorem actual_principal_coefficient_symm (hg : IsAdmissibleMetric g) (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (q : ℝ) (x : R3) (i j : Fin 3) :
    referenceDensityPrincipalFrameCoefficient g g2 L q x i j=
      referenceDensityPrincipalFrameCoefficient g g2 L q x j i := by
  have hQ := (referenceDensityPrincipalFrameCoefficient_posSemidef g g2 hg hg2 L q x).isHermitian.apply j i
  simpa only [Matrix.of_apply,star_trivial] using hQ

/-- Real physical Gram contraction can be swapped only after symmetry is proved. -/
theorem symmetric_physical_gram_contraction {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℝ E0]
    (Q : Fin 3 → Fin 3 → ℝ) (hQ : ∀ i j, Q i j=Q j i) (u v : Fin 3 → E0) :
    (∑ i : Fin 3, ∑ j : Fin 3, Q i j*⟪u i,v j⟫_ℝ)=
      ∑ i : Fin 3, ∑ j : Fin 3, Q i j*⟪v i,u j⟫_ℝ := by
  calc
    _ = ∑ j : Fin 3, ∑ i : Fin 3, Q i j*⟪u i,v j⟫_ℝ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg₂ (fun a b : ℝ => a*b) (hQ j i) (real_inner_comm (u j) (v i)).symm

local notation "UBin" => ActualHigherSFormation.higherSDegreeInput hO hD
local notation "GRAM" => ActualDegreeGramCancellation.degreeGram g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FIELD" => ActualDegreeGramBaseIdentity.finiteDegreeGramField g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "COEF" => ActualDegreeGramBaseDerivative.degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "COMM" => ActualDegreeGramBaseIdentity.finiteDegreeGramCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QC" g2:max q:max x:max i:max j:max => referenceDensityPrincipalFrameCoefficient g g2 L q x i j
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The ORIGINAL principal-matrix contracted physical scalar. -/
def principalDegreeGramField (g2 : MatrixField) (q : ℝ) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*FIELD i j T F x

/-- The ORIGINAL principal-matrix mixed base/degree Gram term. -/
def principalDegreeBaseMixed (g2 : MatrixField) (q : ℝ) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x X : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
    GRAM i j (T x) (fderiv ℝ (Uin F) x X) (UBin F x)

/-- Every original coefficient derivative in the contracted scalar. -/
def principalDegreeCoefficientDerivative (g2 : MatrixField) (q : ℝ) (T : R3 → Tpar)
    (F : smoothCompactFiniteSphereCore hO hD) (x X : R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun y => QC g2 q y i j) x X*FIELD i j T F x

local notation "QFIELD" => principalDegreeGramField g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QMIX" => principalDegreeBaseMixed g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "QDER" => principalDegreeCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Global actual Q-contracted Gram smoothness on the original support-only room hypothesis. -/
theorem contDiff_principal_degree_gram (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (QFIELD g2 q (Tq δr Ar p q) F) := by
  unfold principalDegreeGramField
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((contDiff_fixed_parameter_scalar
      (fun z : ℝ × R3 => QC g2 z.1 z.2 i j)
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j) q).mul
      (ActualDegreeGramBaseIdentity.contDiff_original_profile_degree_gram
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
          δr Ar p hδr hAr q F hT i j))))

attribute [local irreducible] principalDegreeGramField principalDegreeBaseMixed
  principalDegreeCoefficientDerivative ActualDegreeGramCancellation.degreeGram
  ActualDegreeGramBaseIdentity.finiteDegreeGramField

private lemma actual_degree_gram_symmetry (i j : Fin 3) (t : Tpar) (u v : Hi) :
    GRAM i j t u v=GRAM j i t v u := by
  unfold ActualDegreeGramCancellation.degreeGram
  exact real_inner_comm _ _

/-- Exact GLOBAL original Q contraction. Both coefficient derivatives and the full
ordered base remainder remain visible. -/
theorem principal_degree_contraction_remainder_identity (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ TS F, (Tq δr Ar p q) x ∈ ParamRoom δ) (x X : R3) :
    2*QMIX g2 q (Tq δr Ar p q) F x X-fderiv ℝ (QFIELD g2 q (Tq δr Ar p q) F) x X =
      (∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
        (GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
          GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
          fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X))-
      QDER g2 q (Tq δr Ar p q) F x X := by
  have hQsm (i j : Fin 3) : ContDiff ℝ ∞ (fun y => QC g2 q y i j) :=
    contDiff_fixed_parameter_scalar
      (fun z : ℝ × R3 => QC g2 z.1 z.2 i j)
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j) q
  have hHsm (i j : Fin 3) : ContDiff ℝ ∞ (FIELD i j (Tq δr Ar p q) F) :=
    ActualDegreeGramBaseIdentity.contDiff_original_profile_degree_gram
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
        δr Ar p hδr hAr q F hT i j
  have hD0 := fderiv_matrix_scalar_contraction
    (fun i j y => QC g2 q y i j) (fun i j => FIELD i j (Tq δr Ar p q) F) x X
    (fun i j => (hQsm i j).differentiable (by simp) x)
    (fun i j => (hHsm i j).differentiable (by simp) x)
  have hContractDerivative : fderiv ℝ (QFIELD g2 q (Tq δr Ar p q) F) x X =
      QDER g2 q (Tq δr Ar p q) F x X+
      ∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X := by
    unfold principalDegreeGramField principalDegreeCoefficientDerivative
    simpa only [Finset.sum_add_distrib] using hD0
  have hSwap : (∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
      GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X))=
      QMIX g2 q (Tq δr Ar p q) F x X := by
    unfold principalDegreeBaseMixed
    calc
      _ = ∑ j : Fin 3, ∑ i : Fin 3, QC g2 q x i j*
          GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg₂ (fun a b : ℝ => a*b)
          (actual_principal_coefficient_symm g L hg g2 hg2 q x j i)
          (actual_degree_gram_symmetry g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            j i ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X))
  have hExpand : (∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
      (GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
        GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
        fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X)) =
      QMIX g2 q (Tq δr Ar p q) F x X+
      (∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
        GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X))-
      ∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X := by
    simp only [principalDegreeBaseMixed,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  linarith only [hContractDerivative,hSwap,hExpand]

/-- Actual physical degree Gram value has an exact low representation, avoiding norm UB_Hi. -/
theorem degree_gram_value_low (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u z zb : Hi)
    (hb : IH zb=generatorHigh BG z) :
    GRAM i j t u zb=PP (EH i t u) (EL j t (generatorHigh BG z)) := by
  have hGraph := (Cm.compat j t ht zb).trans (congrArg (EL j t) hb)
  have hPair := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD (EH i t u) (EH j t zb)
  unfold ActualDegreeGramCancellation.degreeGram
  exact hPair.symm.trans (congrArg (PP (EH i t u)) hGraph)

private lemma value_pairing_bound (A : Hi →L[ℝ] Half) (B : Half →L[ℝ] Neg) (D : Hi →L[ℝ] Half)
    (u z : Hi) : |PP (A u) (B (D z))| ≤ ‖A‖*‖B‖*‖D‖*‖u‖*‖z‖ := by
  have hBD : ‖B (D z)‖ ≤ ‖B‖*(‖D‖*‖z‖) :=
    (B.le_opNorm (D z)).trans (mul_le_mul_of_nonneg_left (D.le_opNorm z) (norm_nonneg B))
  calc
    _ ≤ ‖A u‖*‖B (D z)‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) (A u) (B (D z))
    _ ≤ (‖A‖*‖u‖)*(‖B‖*(‖D‖*‖z‖)) :=
      mul_le_mul (A.le_opNorm u) hBD (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg u))
    _ = _ := by ring

/-- One actual Hi-by-Hi degree Gram value bound before every finite input/profile. -/
theorem exists_actual_degree_gram_value_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u z zb : Hi,
      IH zb=generatorHigh BG z → |GRAM i j t u zb| ≤ K*‖u‖*‖z‖ := by
  have hCapsFull := ActualDegreeGramBaseDerivative.exists_actual_canonical_value_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  rcases hCapsFull with ⟨M,hM,hCap⟩
  refine ⟨M^2*‖generatorHigh BG‖,mul_nonneg (sq_nonneg M) (norm_nonneg _),?_⟩
  intro i j t ht u z zb hb
  have hRep := degree_gram_value_low
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm i j t ht u z zb hb
  have hRaw := value_pairing_bound (EH i t) (EL j t) (generatorHigh BG) u z
  have hCapProd : ‖EH i t‖*‖EL j t‖ ≤ M^2 := by
    calc
      _ ≤ M*M := mul_le_mul (hCap i t ht).1 (hCap j t ht).2.1 (norm_nonneg (EL j t)) hM
      _ = _ := by ring
  exact (congrArg abs hRep).le.trans (hRaw.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCapProd (norm_nonneg (generatorHigh BG))) (norm_nonneg u)) (norm_nonneg z)))

/-- Original principal values and spatial derivatives have one compact fixed-metric cap. -/
theorem exists_actual_principal_value_derivative_caps (hg : IsAdmissibleMetric g)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ, ∀ i j : Fin 3,
      |QC g2 q x i j| ≤ C ∧ ∀ X : R3, |fderiv ℝ (fun y => QC g2 q y i j) x X| ≤ C*‖X‖ := by
  let A : (Fin 3 × Fin 3) → ℝ × R3 → ℝ := fun ij z => QC g2 z.1 z.2 ij.1 ij.2
  have hA (ij : Fin 3 × Fin 3) : ContDiff ℝ ∞ (A ij) :=
    contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L ij.1 ij.2
  have hCapsFull := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt A
    (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) (isCompact_Icc.prod (isCompact_closedBall y0 ρ))
    (fun ij z _ => (hA ij).contDiffAt) 1
  rcases hCapsFull with ⟨C,hC,hCaps⟩
  refine ⟨C,hC,?_⟩
  intro q hq x hx i j
  have hVal := hCaps 0 (by norm_num) (q,x) ⟨hq,hx⟩ (i,j)
  have hFirst := hCaps 1 (le_refl _) (q,x) ⟨hq,hx⟩ (i,j)
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hVal
  rw [norm_iteratedFDeriv_one] at hFirst
  refine ⟨hVal,?_⟩
  intro X
  change |fderiv ℝ (fun y => A (i,j) (q,y)) x X| ≤ C*‖X‖
  rw [ActualHigherSAdjointCoefficientBounds.fderiv_fixed_parameter_apply (A (i,j)) (hA (i,j)),← Real.norm_eq_abs]
  have hVec : ‖((0 : ℝ),X)‖ ≤ ‖X‖ := by simp
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hFirst hVec (norm_nonneg _) hC)

private lemma abs_matrix_contraction_le (Q A : Fin 3 → Fin 3 → ℝ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hQ : ∀ i j, |Q i j| ≤ C) (hA : ∀ i j, |A i j| ≤ D) :
    |∑ i : Fin 3, ∑ j : Fin 3, Q i j*A i j| ≤ 9*C*D := by
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |Q i j*A i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C*D := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul]
      exact mul_le_mul (hQ i j) (hA i j) (abs_nonneg _) hC
    _ = _ := by simp; ring

private lemma contract_two_budgets (C D P Z : ℝ) (hD : 0 ≤ D) (hZ : 0 ≤ Z) :
    C*(P+Z)+D*P ≤ (C+D)*(P+Z) := by nlinarith

/-- Sharp ORIGINAL principal-matrix degree/base remainder. The radius precedes g2;
for fixed admissible g2 one K precedes every profile and finite angular input. -/
theorem exists_retained_original_Q_degree_base_remainder_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, δr ≤ 1 →
      ∀ hAr : 0 < Ar, 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ y ∈ TS F, (Tq δr Ar p q) y ∈ ParamRoom δ) →
      ∀ x ∈ TS F, ∀ X : R3, 1 ≤ actualReferenceBeta g L q δr Ar p x →
      referenceRadius δr Ar p L x*(actualReferenceBeta g L q δr Ar p x)^2 ≤ 1 →
      |2*QMIX g2 q (Tq δr Ar p q) F x X-fderiv ℝ (QFIELD g2 q (Tq δr Ar p q) F) x X| ≤
        K*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) := by
  have hMFull := ActualDegreeGramBaseIdentity.exists_retained_original_profile_degree_base_remainder_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W hL
  rcases hMFull with ⟨δM,hδM,hδM0,hδMρ,KM,hKM,hM⟩
  have hRoomFull := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hRoomFull with ⟨δC,Cm⟩
  have hValueFull := exists_actual_degree_gram_value_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm
  rcases hValueFull with ⟨KH,hKH,hValue⟩
  let δ := min δM δC
  have hδMle : δ ≤ δM := min_le_left _ _
  have hδCle : δ ≤ δC := min_le_right _ _
  have hSubM := commonRoom_mono y0 ρ hδMle
  have hSubC := commonRoom_mono y0 ρ hδCle
  refine ⟨δ,lt_min hδM Cm.rev.pos,hδMle.trans hδM0,hδMle.trans hδMρ,?_⟩
  intro g2 hg2
  have hQFull := exists_actual_principal_value_derivative_caps g L y0 ρ hg g2 hg2
  rcases hQFull with ⟨CQ,hCQ,hQ⟩
  let K1 := 9*CQ*KM
  let K2 := 9*CQ*KH
  have hK10 : 0 ≤ K1 := mul_nonneg (mul_nonneg (by norm_num) hCQ) hKM
  have hK20 : 0 ≤ K2 := mul_nonneg (mul_nonneg (by norm_num) hCQ) hKH
  refine ⟨K1+K2,add_nonneg hK10 hK20,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq F hT x hx X hβ hsmall
  have ht := hT x hx
  have hxK : x ∈ closedBall y0 ρ := ht.1.2.1
  have htM : (Tq δr Ar p q) x ∈ ParamRoom δM := ⟨hSubM ht.1,ht.2⟩
  have hTC : ∀ y ∈ TS F, (Tq δr Ar p q) y ∈ ParamRoom δC :=
    fun y hy => ⟨hSubC (hT y hy).1,(hT y hy).2⟩
  have htC := hTC x hx
  have hP0 : 0 ≤ ‖X‖*‖Uin F x‖^2 := mul_nonneg (norm_nonneg X) (sq_nonneg _)
  have hZ0 : 0 ≤ ‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hEnergy0 := add_nonneg hP0 hZ0
  have hRow (i j : Fin 3) :
      |GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
        GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
        fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X| ≤
        KM*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) :=
    hM δr Ar p hδr hδr1 hAr hp q hq F x X htM hβ hsmall i j
  have hH (i j : Fin 3) : |FIELD i j (Tq δr Ar p q) F x| ≤ KH*‖Uin F x‖^2 := by
    have hVal := hValue i j ((Tq δr Ar p q) x) htC (Uin F x) (Uin F x) (UBin F x)
      (ActualDegreeGramCancellation.finite_degree_input_inclusion hO hD F x)
    unfold ActualDegreeGramBaseIdentity.finiteDegreeGramField
    calc
      _ ≤ KH*‖Uin F x‖*‖Uin F x‖ := hVal
      _ = _ := by ring
  have hQCap (i j : Fin 3) := (hQ q hq x hxK i j).1
  have hQDCap (i j : Fin 3) := (hQ q hq x hxK i j).2 X
  have hRRaw := abs_matrix_contraction_le (fun i j => QC g2 q x i j)
    (fun i j => GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
      GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
      fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X)
    CQ (KM*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖))
    hCQ (mul_nonneg hKM hEnergy0) hQCap hRow
  have hRBound : |∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
      (GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
        GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
        fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X)| ≤
      K1*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖) := by
    calc
      _ ≤ 9*CQ*(KM*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖)) := hRRaw
      _ = _ := by dsimp only [K1]; ring
  have hDRaw := abs_matrix_contraction_le
    (fun i j => fderiv ℝ (fun y => QC g2 q y i j) x X)
    (fun i j => FIELD i j (Tq δr Ar p q) F x) (CQ*‖X‖) (KH*‖Uin F x‖^2)
    (mul_nonneg hCQ (norm_nonneg X)) (mul_nonneg hKH (sq_nonneg _)) hQDCap hH
  have hDBound : |QDER g2 q (Tq δr Ar p q) F x X| ≤ K2*(‖X‖*‖Uin F x‖^2) := by
    unfold principalDegreeCoefficientDerivative
    calc
      _ ≤ 9*(CQ*‖X‖)*(KH*‖Uin F x‖^2) := hDRaw
      _ = _ := by dsimp only [K2]; ring
  have hIdentity := principal_degree_contraction_remainder_identity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δC Cm g2 hg2
      δr Ar p hδr hAr q F hTC x X
  calc
    _ ≤ |∑ i : Fin 3, ∑ j : Fin 3, QC g2 q x i j*
        (GRAM i j ((Tq δr Ar p q) x) (fderiv ℝ (Uin F) x X) (UBin F x)+
          GRAM i j ((Tq δr Ar p q) x) (UBin F x) (fderiv ℝ (Uin F) x X)-
          fderiv ℝ (FIELD i j (Tq δr Ar p q) F) x X)|+|QDER g2 q (Tq δr Ar p q) F x X| :=
      (congrArg abs hIdentity).le.trans (abs_sub _ _)
    _ ≤ K1*(‖X‖*‖Uin F x‖^2+‖Uin F x‖*‖IH (fderiv ℝ (Uin F) x X)‖)+
        K2*(‖X‖*‖Uin F x‖^2) := add_le_add hRBound hDBound
    _ ≤ _ := contract_two_budgets K1 K2 _ _ hK20 hZ0

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualQDegreeBaseContraction
