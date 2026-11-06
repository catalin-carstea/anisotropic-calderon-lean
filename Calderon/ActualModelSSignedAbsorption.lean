import Calderon.ActualModelSErrorDecomposition

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualHigherSLeadingBracketGain ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds
  FixedParameterProfilePullback FixedParameterProfileBudgets NormalizedPrincipalMetric

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
  (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
  (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)

local notation "MR" => nativeModelRaising hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "MD" => nativeModelAdjoint hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "ZZ" => nativeZ hO hD hF g hg L q dr Ar p hdr hAr
local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "TF" => nativeT hO hD hF g hg L q dr Ar p hdr hAr
local notation "TD" => nativeTdag hO hD hF g hg L q dr Ar p hdr hAr
local notation "UF" => nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "UD" => nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "Lead" => actualLeadingSignedSecondOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q
local notation "Sc" => ActualScalarSAdjointCross.nativeScalarSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
  g2 dr Ar p hdr hAr q (referenceNormalizedPrincipalDifference g g2 L q)
local notation "Known" => actualLeadingScalarSReferenceError
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 dr Ar p hdr hAr q (referenceNormalizedPrincipalDifference g g2 L q)


local notation "Rem" => actualModelSUnestimatedDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q

/-- An explicit remaining-density bound combines with the checked leading/scalar estimate.
This conditional consumer does not assert the remaining bound. -/
theorem actual_model_S_full_signed_error_bound
    (CErr CRem eta : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (hDec : ActualModelSErrorDecomposition g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F)
    (hRem : |∫ x, referenceDensityFamily g L (q,x)*Rem F x| ≤ CRem*eta*
      (∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x)) :
    |((∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x+SO F x‖^2)-
      (∫ x, referenceDensityFamily g L (q,x)*‖((MD F)+(2:ℝ) • (ZZ F)).val x+SD F x‖^2))-
      ((∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x‖^2)-
      (∫ x, referenceDensityFamily g L (q,x)*‖((MD F)+(2:ℝ) • (ZZ F)).val x‖^2))| ≤
      (CErr+CRem)*eta*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x) := by
  rcases hDec with ⟨_hAll,_hLo,_hRemI,_hKnownI,_hEnergyI,hEq,hKnownBound⟩
  rw [hEq]
  calc
    _ = |(∫ x, referenceDensityFamily g L (q,x)*Rem F x)+
      (∫ x, referenceDensityFamily g L (q,x)*Known F x)| := congrArg abs (by ring)
    _ ≤ |∫ x, referenceDensityFamily g L (q,x)*Rem F x|+
      |∫ x, referenceDensityFamily g L (q,x)*Known F x| := abs_add_le _ _
    _ ≤ CRem*eta*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)+
      CErr*eta*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) :=
      add_le_add hRem hKnownBound
    _ = _ := by ring

/-- Absorb the literal full signed model/S error. Mean-zero and cofinal-model
qualifications remain exactly in the supplied signed model lower bound. -/
theorem actual_model_S_positive_signed_absorption
    (hL : 0 < L) (hp : 1 ≤ p) (CErr CRem cRaise eta : ℝ) (hc : 0 < cRaise)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hDec : ActualModelSErrorDecomposition g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F)
    (hRem : |∫ x, referenceDensityFamily g L (q,x)*Rem F x| ≤ CRem*eta*
      (∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x))
    (hModel : cRaise*(∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ≤
      (∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x‖^2)-
        (∫ x, referenceDensityFamily g L (q,x)*‖((MD F)+(2:ℝ) • (ZZ F)).val x‖^2))
    (hBudget : (CErr+CRem)*eta ≤ cRaise/2) :
    0 < cRaise/2 ∧
    (cRaise/2)*(∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ≤
      (∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x+SO F x‖^2)-
        (∫ x, referenceDensityFamily g L (q,x)*‖((MD F)+(2:ℝ) • (ZZ F)).val x+SD F x‖^2) ∧
    (cRaise/2)*(∫ x, referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ≤
      ∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x+SO F x‖^2 := by
  let E : ℝ := ∫ x, referenceDensityFamily g L (q,x)*
    finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x
  let M : ℝ := (∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x‖^2)-
    (∫ x, referenceDensityFamily g L (q,x)*‖((MD F)+(2:ℝ) • (ZZ F)).val x‖^2)
  let P : ℝ := ∫ x, referenceDensityFamily g L (q,x)*‖(MR F).val x+SO F x‖^2
  let Q : ℝ := ∫ x, referenceDensityFamily g L (q,x)*
    ‖((MD F)+(2:ℝ) • (ZZ F)).val x+SD F x‖^2
  have hE : 0 ≤ E := integral_nonneg (fun x =>
    mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
      (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _
        (actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x).le F x))
  have hQ : 0 ≤ Q := integral_nonneg (fun x =>
    mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le (sq_nonneg _))
  have hErr : |(P-Q)-M| ≤ (CErr+CRem)*eta*E :=
    actual_model_S_full_signed_error_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q CErr CRem eta F hDec hRem
  have hBudgetE := mul_le_mul_of_nonneg_right hBudget hE
  have hSigned : (cRaise/2)*E ≤ P-Q := by
    have hLow := (abs_le.mp hErr).1
    change cRaise*E ≤ M at hModel
    nlinarith only [hLow,hModel,hBudgetE]
  exact ⟨div_pos hc (by norm_num),hSigned,hSigned.trans (sub_le_self P hQ)⟩

/-- Choose a positive absorption budget before every later profile and input. -/
theorem exists_model_S_signed_absorption_budget
    (CErr CRem cRaise eta0 : ℝ) (hErr : 0 ≤ CErr) (hRem : 0 ≤ CRem)
    (hc : 0 < cRaise) (hEta0 : 0 < eta0) :
    ∃ etaAbs : ℝ, 0 < etaAbs ∧ etaAbs ≤ eta0 ∧ etaAbs ≤ 1 ∧
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaAbs → (CErr+CRem)*eta ≤ cRaise/2 := by
  let Csum := CErr+CRem
  have hCsum : 0 ≤ Csum := add_nonneg hErr hRem
  have hDen : 0 < 2*(Csum+1) := by positivity
  let etaAbs := min eta0 (min 1 (cRaise/(2*(Csum+1))))
  refine ⟨etaAbs,lt_min hEta0 (lt_min zero_lt_one (div_pos hc hDen)),
    min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro eta heta hetaAbs
  have hCap := hetaAbs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMul := (le_div_iff₀ hDen).mp hCap
  change Csum*eta ≤ cRaise/2
  nlinarith only [hMul,heta]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
