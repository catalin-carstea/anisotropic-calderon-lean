import Calderon.ActualUAdjointScalarSplit

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

/-- Literal B/C versus full B/C,V/W,density-derivative U-adjoint lower cross density. -/
def nativeULowerSCrossDensity (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪(nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x,SO F x⟫_ℝ-
    ⟪nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x,SD F x⟫_ℝ
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q

/-- Exactly Main's reserved lower S-self remainder plus the two still unestimated Root groups. -/
def actualModelSUnestimatedDensity (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  (‖SO F x‖^2-‖SD F x‖^2-⟪F.val x,Lead F x⟫_ℝ)+
    4*(⟪(TF F).val x,SO F x⟫_ℝ-⟪((TD F)+(ZZ F)).val x,SD F x⟫_ℝ)+2*Lo F x
local notation "Rem" => actualModelSUnestimatedDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q

/-- Every integral is defined, and the known signed error is quantitatively bounded.
The remaining density is explicit and is not asserted to be small. -/
def ActualModelSErrorDecomposition (CErr eta : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  ActualModelSMixedIntegralIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q F ∧
  Integrable (fun x => mu x*Lo F x) ∧
  Integrable (fun x => mu x*Rem F x) ∧
  Integrable (fun x => mu x*Known F x) ∧
  Integrable (fun x => mu x*
    finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
  (∫ x, mu x*‖(MR F).val x+SO F x‖^2)-
      (∫ x, mu x*‖((MD F)+(2:ℝ) • (ZZ F)).val x+SD F x‖^2) =
    ((∫ x, mu x*‖(MR F).val x‖^2)-
      (∫ x, mu x*‖((MD F)+(2:ℝ) • (ZZ F)).val x‖^2))+
      (∫ x, mu x*Rem F x)+(∫ x, mu x*Known F x) ∧
  |∫ x, mu x*Known F x| ≤ CErr*eta*
    (∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x)

/-- Exact integral assembly of the checked scalar split, retaining all unestimated terms. -/
theorem actual_model_S_error_decomposition
    (CErr eta : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (hMixed : ActualModelSMixedIntegralIdentity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F)
    (hLead : Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F.val x,Lead F x⟫_ℝ))
    (hScalar : Integrable (fun x => referenceDensityFamily g L (q,x)*Sc F x))
    (hKnown : Integrable (fun x => referenceDensityFamily g L (q,x)*Known F x))
    (hEnergy : Integrable (fun x => referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x))
    (hBound : |∫ x, referenceDensityFamily g L (q,x)*Known F x| ≤ CErr*eta*
      (∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)) :
    ActualModelSErrorDecomposition g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let fs : R3 → ℝ := fun x => mu x*‖SO F x‖^2
  let ds : R3 → ℝ := fun x => mu x*‖SD F x‖^2
  let lead : R3 → ℝ := fun x => mu x*⟪F.val x,Lead F x⟫_ℝ
  let ct : R3 → ℝ := fun x => mu x*(⟪(TF F).val x,SO F x⟫_ℝ-
    ⟪((TD F)+(ZZ F)).val x,SD F x⟫_ℝ)
  let cu : R3 → ℝ := fun x => mu x*(⟪(UF F).val x,SO F x⟫_ℝ-⟪(UD F).val x,SD F x⟫_ℝ)
  let cs : R3 → ℝ := fun x => mu x*Sc F x
  let cl : R3 → ℝ := fun x => mu x*Lo F x
  let ck : R3 → ℝ := fun x => mu x*Known F x
  let cr : R3 → ℝ := fun x => mu x*Rem F x
  have hAll := hMixed
  rcases hMixed with ⟨_hFullF,_hFullD,_hMF,_hMD,hfs,hds,hct,hcu,hEq⟩
  have heU : cu = fun x => cs x+cl x := by
    funext x
    have hp := nativeU_scalar_signed_pairing_split hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr F x (SO F x) (SD F x)
    dsimp only [cu,cs,cl,nativeULowerSCrossDensity,ActualScalarSAdjointCross.nativeScalarSCrossDensity]
    rw [hp]
    ring
  have heL : cl = fun x => cu x-cs x := by
    funext x
    have he := congrFun heU x
    linarith only [he]
  have hcl : Integrable cl :=
    Eq.mpr (congrArg (fun f : R3 → ℝ => Integrable f) heL) (hcu.sub hScalar)
  have heK : ck = fun x => lead x+2*cs x := by
    funext x
    dsimp only [ck,lead,cs,actualLeadingScalarSReferenceError]
    ring
  have heR : cr = fun x => ((fs x-ds x)-lead x)+4*ct x+2*cl x := by
    funext x
    dsimp only [cr,fs,ds,lead,ct,cl,actualModelSUnestimatedDensity]
    ring
  have hRsum : Integrable (fun x => ((fs x-ds x)-lead x)+4*ct x+2*cl x) :=
    ((hfs.sub hds).sub hLead).add (hct.const_mul 4) |>.add (hcl.const_mul 2)
  have hcr : Integrable cr :=
    Eq.mpr (congrArg (fun f : R3 → ℝ => Integrable f) heR) hRsum
  have hiU : (∫ x, cu x) = (∫ x, cs x)+(∫ x, cl x) :=
    (congrArg (fun f : R3 → ℝ => ∫ x, f x) heU).trans (integral_add hScalar hcl)
  have hiK : (∫ x, ck x) = (∫ x, lead x)+2*(∫ x, cs x) := by
    rw [heK,integral_add hLead (hScalar.const_mul 2),integral_const_mul]
  have hiR : (∫ x, cr x) =
      ((∫ x, fs x)-(∫ x, ds x))-(∫ x, lead x)+4*(∫ x, ct x)+2*(∫ x, cl x) := by
    rw [heR]
    calc
      _ = (∫ x, ((fs x-ds x)-lead x)+4*ct x)+(∫ x, 2*cl x) :=
        integral_add (((hfs.sub hds).sub hLead).add (hct.const_mul 4)) (hcl.const_mul 2)
      _ = ((∫ x, (fs x-ds x)-lead x)+(∫ x, 4*ct x))+(∫ x, 2*cl x) :=
        congrArg (fun z : ℝ => z+(∫ x, 2*cl x))
          (integral_add ((hfs.sub hds).sub hLead) (hct.const_mul 4))
      _ = (((∫ x, fs x-ds x)-(∫ x, lead x))+(∫ x, 4*ct x))+(∫ x, 2*cl x) :=
        congrArg (fun z : ℝ => (z+(∫ x, 4*ct x))+(∫ x, 2*cl x))
          (integral_sub (hfs.sub hds) hLead)
      _ = _ := by
        rw [show (∫ x, fs x-ds x)=(∫ x, fs x)-(∫ x, ds x) from integral_sub hfs hds,
          integral_const_mul,integral_const_mul]
  refine ⟨hAll,hcl,hcr,hKnown,hEnergy,?_,hBound⟩
  rw [hEq]
  change _ = _+(∫ x, cr x)+(∫ x, ck x)
  change _+((∫ x, fs x)-(∫ x, ds x))+4*(∫ x, ct x)+2*(∫ x, cu x) = _
  rw [hiU,hiR,hiK]
  ring

/-- The full original model+S comparison and known signed estimate share an actual
uniform profile threshold. No estimate for the remaining density is assumed. -/
theorem exists_actual_model_S_error_decomposition
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ CErr : ℝ, 0 < CErr ∧ ∃ etaID : ℝ, 0 < etaID ∧ etaID ≤ data.eta0 ∧ etaID ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaID →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
      ActualModelSErrorDecomposition g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q CErr eta F := by
  obtain ⟨Ck,hCk,etaK,hEtaK,hEtaK0,hEtaK1,hK⟩ :=
    actual_principal_leading_scalar_S_reference_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg hKernel data g2 hg2
  obtain ⟨etaF,hEtaF,hEtaF0,hEtaF1,hFull⟩ :=
    actual_model_S_full_weak_uniform_reference
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL hKernel
  refine ⟨Ck,hCk,min etaK etaF,lt_min hEtaK hEtaF,
    (min_le_left _ _).trans hEtaK0,(min_le_left _ _).trans hEtaK1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaID K hCompact hBall F hsupp hb hs hH8
  have hKnownFull := hK q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaID.trans (min_le_left _ _)) K hCompact hBall F hsupp hb hs hH8
  rcases hKnownFull with ⟨_hSmooth,_hSupp,_hCompact,hLead,hScalar,hEnergy,hKnown,hBound⟩
  have hFullID := hFull g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta
    (hetaID.trans (min_le_right _ _)) K hCompact hBall F hsupp hb hs
  exact actual_model_S_error_decomposition g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q Ck eta F hFullID.1 hLead hScalar hKnown hEnergy hBound

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
