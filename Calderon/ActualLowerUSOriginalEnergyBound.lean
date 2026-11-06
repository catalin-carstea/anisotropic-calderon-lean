import Calderon.ActualLowerUSIntegralSplit
import Calderon.ActualLowerUSSignedRows
import Calderon.ActualLowerUSTWeightedIBP
import Calderon.ActualLowerUSRZEnergy

/-!
Author-support GPT-6.1 Sol, Root/lower_jq_gained. Actual backend/version/tokens unknown.
Full before-code expansion: ../lower-us-final-original-energy-upfront-v001.md.
Governing resumed expansion: ../UPFRONT-RESUMED-v002.md.
ONLY local lower U/S bound and exact full/scalar split, no final paper assembly.
TARGET proposition declarations below are copied literally from TARGET.lean
SHA256 e7df98468b98f1093497ed2b4941ea9541c960179a75c84626fd15c4e133f92f.
Fix the ORIGINAL ordered metric pair; constants precede every q/profile/input.
Source-uniformity clarification: ../METRIC-UNIFORMITY-SOURCE-RESOLUTION-v001.json.
No analytic cap callback among final producer premises. No author compiler.
Exact formal/review status is recorded in the bound delivery receipts; canonical Main is separate.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSEnergyBound
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualModelSMixedComparison ConformalDepth
  ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric
  ActualLowerUSIntegralSplit ActualLowerUSSignedRows ActualLowerUSTWeightedIBP ActualLowerUSRZEnergy

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

/-- The literal integral statement, including the source factor two and original energy. -/
def LowerUSOriginalEnergyConclusion (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q C_US eta : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let Lo := nativeULowerSCrossDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q F
  Integrable (fun x => mu x * Lo x) ∧
  Integrable (fun x => mu x * (2 * Lo x)) ∧
  Integrable (fun x => mu x * finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x) ∧
  |∫ x, mu x * (2 * Lo x)| ≤ C_US * eta *
    (∫ x, mu x * finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x)

/-- Selected fixed-original-pair obligation. All profile hypotheses are exactly those of
`exists_actual_model_S_error_decomposition`; constants and threshold precede every profile/input.
The original standing hypotheses hL and hKernel must be retained by its producer. -/
def FixedMetricLowerUSOriginalEnergyBound (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Prop :=
  ∃ C_US : ℝ, 0 < C_US ∧ ∃ etaUS : ℝ, 0 < etaUS ∧ etaUS ≤ data.eta0 ∧ etaUS ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaUS →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
      (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
    LowerUSOriginalEnergyConclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q C_US eta F

/-- Exact desired fixed-metric theorem type as a proposition; not an inhabitant/proof. -/
def FixedMetricLowerUSOriginalEnergyProducer (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Prop :=
  0 < L → UnitBallValueTraceKernel τ0 →
    FixedMetricLowerUSOriginalEnergyBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2


/-- Literal full physical U/S contribution minus the already checked scalar/S
contribution. This definition retains the original common data/germs and factor two. -/
def FullUSScalarDifferenceConclusion (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q C_US eta : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let full : R3 → ℝ := fun x =>
    ⟪(nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x,
      ActualHigherSFormation.nativeHigherSOut hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
        dr Ar p hdr hAr q hreg data.δ0 data.germs g2 F x⟫_ℝ -
    ⟪(nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x,
      ActualHigherSAdjointFormation.higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x⟫_ℝ
  let scalar : R3 → ℝ := ActualScalarSAdjointCross.nativeScalarSCrossDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs
    g2 dr Ar p hdr hAr q (referenceNormalizedPrincipalDifference g g2 L q) F
  |(∫ x, mu x*(2*full x))-(∫ x, mu x*(2*scalar x))| ≤
    C_US*eta*(∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x)

/-- Pure bookkeeping using the QUALIFIED literal native split. This does not
reprove the principal scalar estimate or add an analytic assumption to a producer. -/
lemma fullUSScalarDifference_of_lower_and_split
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q C_US eta : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hLower : LowerUSOriginalEnergyConclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q C_US eta F)
    (hSplit : LowerUSIntegralSplit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F) :
    FullUSScalarDifferenceConclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q C_US eta F := by
  rcases hSplit with ⟨_hLo,_h2Lo,_hE,_hFull,_hScalar,_hSplit,hTwiceSplit,_hTwiceLo⟩
  dsimp only [FullUSScalarDifferenceConclusion]
  rw [hTwiceSplit,add_sub_cancel_left]
  exact hLower.2.2.2

/-- Complete actual local assembly, including original integrability, exact
factor two, qualified integral split and the literal full-minus-scalar bound.
All actual row/cap factories are invoked internally, before every profile. -/
theorem exists_actual_lower_US_original_energy_bound_and_split
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ C_US : ℝ, 0 < C_US ∧ ∃ etaUS : ℝ, 0 < etaUS ∧ etaUS ≤ data.eta0 ∧ etaUS ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaUS →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
      LowerUSOriginalEnergyConclusion
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q C_US eta F ∧
      LowerUSIntegralSplit
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q F ∧
      FullUSScalarDifferenceConclusion
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q C_US eta F := by
  obtain ⟨etaRows,hEtaRows,hEtaRows0,hEtaRows1,hRows⟩ :=
    exists_actual_lower_US_signed_rows_integral
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨mixed,δ,hδ,gen,CT,hCT,etaT,hEtaT,hEtaT0,hEtaT1,hT⟩ :=
    exists_nativeTSecond_uniform_profile_integral_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CRZ,hCRZ,etaRZ,hEtaRZ,hEtaRZ0,hEtaRZ1,hRZ⟩ :=
    exists_actual_lower_US_RZ_uniform_profile_integral_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨etaSplit,hEtaSplit,hEtaSplit0,hEtaSplit1,hSplit⟩ :=
    exists_lowerUSIntegralSplit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  let C_US : ℝ := 2*(CT+CRZ)
  let etaUS : ℝ := min etaRows (min etaT (min etaRZ etaSplit))
  have hCUS : 0 < C_US := by dsimp only [C_US]; positivity
  have hEtaUS : 0 < etaUS := lt_min hEtaRows (lt_min hEtaT (lt_min hEtaRZ hEtaSplit))
  have hERows : etaUS ≤ etaRows := min_le_left _ _
  have hET : etaUS ≤ etaT := (min_le_right _ _).trans (min_le_left _ _)
  have hERZ : etaUS ≤ etaRZ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hESplit : etaUS ≤ etaSplit := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨C_US,hCUS,etaUS,hEtaUS,hERows.trans hEtaRows0,hERows.trans hEtaRows1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hSupp hb hs hH8
  have hRowsF := hRows q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaUS.trans hERows)
    K hK hBall F hSupp hb hs hH8
  have hTF := hT q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaUS.trans hET)
    K hK hBall F hSupp hb hs hH8
  have hRZF := hRZ q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaUS.trans hERZ)
    K hK hBall F hSupp hb hs hH8
  have hSplitF := hSplit q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaUS.trans hESplit)
    K hK hBall F hSupp hb hs hH8
  have hSplitKeep := hSplitF
  rcases hSplitF with ⟨hLo,h2Lo,hEnergy,_hFull,_hScalar,_hFullSplit,_h2FullSplit,h2LoEq⟩
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let Lo : R3 → ℝ := nativeULowerSCrossDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let T : R3 → ℝ := nativeTSecondDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 dr Ar p hdr hAr q F
  let R : R3 → ℝ := nativeRFirstDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let Z : R3 → ℝ := nativeZZeroDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let Rows : R3 → ℝ := nativeSignedRowsDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let Eint : ℝ := ∫ x, mu x*finiteCoreReferenceProfileEnergy hO hD g hg L q
    (actualReferenceBeta g L q dr Ar p x) F x
  have hTint : Integrable (fun x => mu x*T x) := hTF.1.1
  have hRint : Integrable (fun x => mu x*R x) := hRZF.1
  have hZint : Integrable (fun x => mu x*Z x) := hRZF.2.1
  have hWeightedRows : (fun x => mu x*Rows x) =
      (fun x => (mu x*T x+mu x*R x)+mu x*Z x) := by
    funext x
    change mu x*(T x+R x+Z x) = _
    ring
  have hRowsIntegral : (∫ x, mu x*Rows x) =
      (∫ x, mu x*T x)+(∫ x, mu x*R x)+(∫ x, mu x*Z x) := by
    rw [hWeightedRows]
    have hTR := integral_add hTint hRint
    have hAll := integral_add (hTint.add hRint) hZint
    simp only [Pi.add_def] at hTR hAll
    have hTransport := congrArg (fun z : ℝ => z+(∫ x, mu x*Z x)) hTR
    exact hAll.trans hTransport
  have hLoIntegral : (∫ x, mu x*Lo x) =
      (∫ x, mu x*T x)+(∫ x, mu x*R x)+(∫ x, mu x*Z x) :=
    hRowsF.2.2.trans hRowsIntegral
  have hTcap : |∫ x, mu x*T x| ≤ CT*eta*Eint := hTF.2
  have hRZcap : |∫ x, mu x*R x|+|∫ x, mu x*Z x| ≤ CRZ*eta*Eint := hRZF.2.2.1
  have hLoCap : |∫ x, mu x*Lo x| ≤ (CT+CRZ)*eta*Eint := by
    rw [hLoIntegral]
    calc
      _ ≤ |∫ x, mu x*T x|+|∫ x, mu x*R x|+|∫ x, mu x*Z x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ = |∫ x, mu x*T x|+(|∫ x, mu x*R x|+|∫ x, mu x*Z x|) := by ring
      _ ≤ CT*eta*Eint+CRZ*eta*Eint := add_le_add hTcap hRZcap
      _ = _ := by ring
  have hTwiceCap : |∫ x, mu x*(2*Lo x)| ≤ C_US*eta*Eint := by
    rw [h2LoEq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*((CT+CRZ)*eta*Eint) := mul_le_mul_of_nonneg_left hLoCap (by norm_num)
      _ = _ := by dsimp only [C_US]; ring
  have hConclusion : LowerUSOriginalEnergyConclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q C_US eta F := ⟨hLo,h2Lo,hEnergy,hTwiceCap⟩
  refine ⟨hConclusion,hSplitKeep,?_⟩
  exact fullUSScalarDifference_of_lower_and_split
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q C_US eta F hConclusion hSplitKeep

/-- The exact selected TARGET, derived from actual T/R/Z and qualified split
factories, with no analytic cap callback among its hypotheses. The ORIGINAL ordered
metric pair is fixed; constants precede every q/profile/input. -/
theorem exists_actual_lower_US_original_energy_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    FixedMetricLowerUSOriginalEnergyBound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 := by
  obtain ⟨CUS,hCUS,etaUS,hEtaUS,hEtaUS0,hEtaUS1,hBound⟩ :=
    exists_actual_lower_US_original_energy_bound_and_split
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  refine ⟨CUS,hCUS,etaUS,hEtaUS,hEtaUS0,hEtaUS1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hSupp hb hs hH8
  exact (hBound q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hSupp hb hs hH8).1

/-- Public inhabitant of the exact original fixed-metric producer proposition. -/
theorem fixedMetricLowerUSOriginalEnergyProducer
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    FixedMetricLowerUSOriginalEnergyProducer
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 := by
  intro hL hKernel
  exact exists_actual_lower_US_original_energy_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSEnergyBound
