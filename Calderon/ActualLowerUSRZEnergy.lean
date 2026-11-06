import Calderon.ActualLowerUSGainedDQ
import Calderon.ActualLowerUSRZIntegrability
import Calderon.ActualLowerUSGainedJP
import Calderon.ActualLowerUSGainedJQ
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral

/-! Actual full R/Z integral estimate in the original reference-profile energy.
No analytic cap callback or physical output substitution is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSRZEnergy
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualFullEGainedEndpoints ActualAngularHighDraft ActualAngularPiDraft
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  ReferenceDensityBounds PrincipalCommutator ConformalDepth ReferenceWeightedApproximation NormalizedPrincipalMetric
  ActualLowerUSFirstOutput ActualHigherSZeroPhysicalGraph ActualLowerUSSignedRows ActualLowerUSGainedDQ
  ActualLowerUSOrdinaryRows ActualLowerUSRZIntegrability ActualLowerUSGainedJP ActualLowerUSGainedJQ
  ActualLowerUSJPPresentation ActualHigherSZeroScalarCommutatorForm ActualHigherSScalarCommutatorForm
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)

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


local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)

/-- Exact original fixed-metric R/Z integral budget, including both separate
absolute integrals and the signed combined integral used in the final bound. -/
def ActualLowerUSRZOriginalEnergyBound (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : Prop :=
  ∃ CRZ : ℝ, 0 < CRZ ∧ ∃ etaRZ : ℝ, 0 < etaRZ ∧ etaRZ ≤ data.eta0 ∧ etaRZ ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaRZ →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : FC, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
      (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta*referenceRadius dr Ar p L x) →
    let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
    let R : R3 → ℝ := nativeRFirstDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F
    let Z : R3 → ℝ := nativeZZeroDensity
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 hg2 dr Ar p hdr hAr q F
    let E : R3 → ℝ := fun x => finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x
    Integrable (fun x => mu x*R x) ∧ Integrable (fun x => mu x*Z x) ∧
    (|∫ x, mu x*R x|+|∫ x, mu x*Z x| ≤ CRZ*eta*(∫ x, mu x*E x)) ∧
    |∫ x, mu x*(R x+Z x)| ≤ CRZ*eta*(∫ x, mu x*E x)

private lemma abs_finite_RZ_sum_bound
    (r : Fin 3 → Fin 3 → ℝ) (dq jp z : Fin 3 → ℝ) (jq A B C D E : ℝ)
    (hr : ∀ i j, |r i j| ≤ A) (hdq : ∀ j, |dq j| ≤ B)
    (hjp : ∀ j, |jp j| ≤ C) (hz : ∀ i, |z i| ≤ D) (hjq : |jq| ≤ E) :
    |∑ j : Fin 3, ((∑ i : Fin 3, r i j)+dq j+jp j)|+
      |(∑ i : Fin 3, z i)+jq| ≤ 9*A+3*B+3*C+3*D+E := by
  have hrSum (j : Fin 3) : |∑ i : Fin 3, r i j| ≤ 3*A := by
    calc
      _ ≤ ∑ i : Fin 3, |r i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, A := Finset.sum_le_sum (fun i _ => hr i j)
      _ = _ := by simp <;> ring
  have hrTerm (j : Fin 3) : |(∑ i : Fin 3, r i j)+dq j+jp j| ≤ 3*A+B+C :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add (hrSum j) (hdq j)) (hjp j))
  have hR : |∑ j : Fin 3, ((∑ i : Fin 3, r i j)+dq j+jp j)| ≤ 3*(3*A+B+C) := by
    calc
      _ ≤ ∑ j : Fin 3, |(∑ i : Fin 3, r i j)+dq j+jp j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, (3*A+B+C) := Finset.sum_le_sum (fun j _ => hrTerm j)
      _ = _ := by simp <;> ring
  have hZSum : |∑ i : Fin 3, z i| ≤ 3*D := by
    calc
      _ ≤ ∑ i : Fin 3, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, D := Finset.sum_le_sum (fun i _ => hz i)
      _ = _ := by simp <;> ring
  have hZ : |(∑ i : Fin 3, z i)+jq| ≤ 3*D+E :=
    (abs_add_le _ _).trans (add_le_add hZSum hjq)
  linarith


private lemma finiteCore_mixed_energy_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : ℝ) (hbeta : 0 < beta) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) (j : Fin 3) :
    ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (3/2 : ℝ)) F).val x‖ *
      ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (1/2 : ℝ))
        (coreDirectionalDerivative hO hD (coordinateDirection j) F)).val x‖ ≤
      inclusionEnergyDensity IH beta (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x := by
  have hGradient : IH (directionalFDeriv (coordinateDirection j)
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x :=
    (congrArg IH (directionalFDeriv_finiteCoreSobolevLift
      hO hD (3/2 : ℝ) F (coordinateDirection j) x)).trans
        (sphereSobolevInclusionL_finiteCoreSobolevLift hO hD (3/2 : ℝ) (1/2 : ℝ)
          (by norm_num) (coreDirectionalDerivative hO hD (coordinateDirection j) F) x)
  have hGradientNorm := (congrArg norm hGradient).trans
    (norm_finiteCoreSobolevLift hO hD (1/2 : ℝ)
      (coreDirectionalDerivative hO hD (coordinateDirection j) F) x)
  have hValueNorm := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x
  have hProduct := congrArg₂ (fun a b : ℝ => a*b) hGradientNorm hValueNorm
  have hSwap :
      ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (3/2 : ℝ)) F).val x‖ *
        ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)).val x‖ =
      ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (1/2 : ℝ))
          (coreDirectionalDerivative hO hD (coordinateDirection j) F)).val x‖ *
        ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (3/2 : ℝ)) F).val x‖ :=
    mul_comm _ _
  have hMixed := inclusion_energy_mixed_le IH beta
    (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x hbeta j
  exact (hSwap.trans hProduct.symm).trans_le hMixed

private lemma finiteCore_weighted_mass_energy_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta : ℝ) (hbeta : 0 ≤ beta) (F : smoothCompactFiniteSphereCore hO hD)
    (x : R3) :
    beta * ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (3/2 : ℝ)) F).val x‖^2 ≤
      inclusionEnergyDensity IH beta (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x := by
  have hNorm := norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x
  have hMassNorm := congrArg (fun z : ℝ => beta*z^2) hNorm
  have hGradient : 0 ≤ beta⁻¹ * (∑ i : Fin 3,
      ‖IH (directionalFDeriv (coordinateDirection i)
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x)‖^2) :=
    mul_nonneg (inv_nonneg.mpr hbeta) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  calc
    _ = beta * ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 := hMassNorm.symm
    _ ≤ _ := by
      unfold inclusionEnergyDensity
      exact le_add_of_nonneg_left hGradient

/-- The literal rows vanish outside the original finite input support. -/
private lemma nativeRZ_zero_off
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : FC) (x : R3) (hx : x ∉ tsupport F.val) :
    nativeRFirstDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x = 0 ∧
    nativeZZeroDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x = 0 := by
  have hFZero : F.val x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hB (i : Fin 3) :
      (nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr F).val x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx
      ((finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i F) hy))
  have hJs : (nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr F).val x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx
      ((finiteCoreSupportPreserving_nativeULowerAdjointZeroSphereAdjointCore
        hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F) hy))
  constructor <;>
    simp only [nativeRFirstDensity,nativeZZeroDensity,nativeOrdinaryRRow,nativeOrdinaryZRow,
      nativeDZeroCommutatorDensity,hFZero,hB,hJs,neg_zero,inner_zero_left,sub_self,
      Finset.sum_const_zero,zero_add,add_zero]

/-- Complete actual R/Z producer in the selected original energy. -/
theorem exists_actual_lower_US_RZ_uniform_profile_integral_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ActualLowerUSRZOriginalEnergyBound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 := by
  obtain ⟨δ,Cm,hJac,CO,hCO,etaO,hEtaO,hEtaO0,hEtaO1,hOrd⟩ :=
    exists_nativeOrdinaryRows_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨δD,CmD,hJacD,CDQ,hCDQ,etaD,hEtaD,hEtaD0,hEtaD1,hDQ⟩ :=
    exists_nativeDZeroCommutator_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CJP,hCJP,etaP,hEtaP,hEtaP0,hEtaP1,hJP⟩ :=
    exists_nativeJP_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CJQ,hCJQ,etaQ,hEtaQ,hEtaQ0,hEtaQ1,hJQ⟩ :=
    exists_nativeJQ_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CE,hCE,hCompare⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound
    hO hD g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  let C0 : ℝ := 12*CO+3*CDQ+3*CJP+CJQ
  let CRZ : ℝ := C0*CE
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  have hCRZ : 0 < CRZ := mul_pos hC0 hCE
  let etaRZ := min etaO (min etaD (min etaP etaQ))
  have hEtaRZ : 0 < etaRZ := lt_min hEtaO (lt_min hEtaD (lt_min hEtaP hEtaQ))
  have hEO : etaRZ ≤ etaO := min_le_left _ _
  have hED : etaRZ ≤ etaD := (min_le_right _ _).trans (min_le_left _ _)
  have hEP : etaRZ ≤ etaP := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hEQ : etaRZ ≤ etaQ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨CRZ,hCRZ,etaRZ,hEtaRZ,hEO.trans hEtaO0,hEO.trans hEtaO1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaRZ K hK hBall F hSupp hb hs hH8
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let beta : R3 → ℝ := actualReferenceBeta g L q dr Ar p
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let R : R3 → ℝ := nativeRFirstDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let Z : R3 → ℝ := nativeZZeroDensity
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q F
  let E : R3 → ℝ := fun x => finiteCoreReferenceProfileEnergy hO hD g hg L q (beta x) F x
  have hOrdHere := hOrd q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRZ.trans hEO)
    K hK hBall hb hs hH8
  have hDQHere := (hDQ q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRZ.trans hED)
    K hK hBall hb hs hH8).2
  have hJPHere := hJP q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRZ.trans hEP)
    K hK hBall hb hs hH8
  have hJQHere := hJQ q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaRZ.trans hEQ)
    K hK hBall F hSupp hb hs hH8
  have hTF : ∀ x ∈ tsupport F.val,
      (ActualHigherSFormation.higherSParam L dr Ar p q) x ∈
        Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
    fun x hx => hOrdHere.1 x (hSupp hx)
  obtain ⟨hRI,hZI⟩ := nativeRZ_integrable_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF
  have hbeta : Continuous beta := continuous_actualReferenceBeta g hg L q dr Ar p hL hdr hAr
  have hbetaPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  have hEI : Integrable (fun x => mu x*E x) :=
    integrable_finiteCoreReferenceProfileEnergy hO hD g hg L q beta hbeta hbetaPos F
  have hPointK (x : R3) (hx : x ∈ K) : |R x|+|Z x| ≤ CRZ*eta*E x := by
    let e := inclusionEnergyDensity IH (beta x) u x
    let N := ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (3/2 : ℝ)) F).val x‖
    let dN : Fin 3 → ℝ := fun j => ‖(coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight (1/2 : ℝ)) ((dd j) F)).val x‖
    have hb1 : 1 ≤ beta x := hb x hx
    have he : 0 ≤ e := inclusionEnergyDensity_nonneg IH (beta x) u x (hbetaPos x).le
    have hMixed (j : Fin 3) : N*dN j ≤ e :=
      finiteCore_mixed_energy_le hO hD (beta x) (hbetaPos x) F x j
    have hMass : beta x*N^2 ≤ e :=
      finiteCore_weighted_mass_energy_le hO hD (beta x) (hbetaPos x).le F x
    have hddSupp (j : Fin 3) : tsupport ((dd j) F).val ⊆ K :=
      (finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _ F).trans hSupp
    have hOrdR (i j : Fin 3) : |nativeOrdinaryRRow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 hg2 dr Ar p hdr hAr q i j F x| ≤ CO*eta*e := by
      have hh := (hOrdHere.2 F ((dd j) F) hSupp (hddSupp j) i j x hx).1
      rw [nativeOrdinaryRProduct_dd_eq_row] at hh
      exact hh.trans (by change CO*eta*N*dN j ≤ CO*eta*e; nlinarith [mul_le_mul_of_nonneg_left (hMixed j) (mul_nonneg hCO.le heta)])
    have hDQBound (j : Fin 3) : |nativeDZeroCommutatorDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x| ≤ CDQ*eta*e := by
      have hh := (hDQHere j F ((dd j) F) hSupp (hddSupp j) x hx).2
      have hScale : CDQ*eta/beta x ≤ CDQ*eta := div_le_self (by positivity) hb1
      calc
        _ ≤ (CDQ*eta/beta x)*N*dN j := hh
        _ ≤ CDQ*eta*N*dN j := by gcongr
        _ ≤ CDQ*eta*e := by nlinarith [mul_le_mul_of_nonneg_left (hMixed j) (mul_nonneg hCDQ.le heta)]
    have hJPBound (j : Fin 3) : |nativeJPCommutatorDensity
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x| ≤ CJP*eta*e := by
      have hh := (hJPHere F ((dd j) F) hSupp (hddSupp j) j x hx).2
      exact hh.trans (by change CJP*eta*N*dN j ≤ CJP*eta*e; nlinarith [mul_le_mul_of_nonneg_left (hMixed j) (mul_nonneg hCJP.le heta)])
    have hOrdZ (i : Fin 3) : |nativeOrdinaryZRow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
        g2 hg2 dr Ar p hdr hAr q i F x| ≤ CO*eta*e := by
      have hh := (hOrdHere.2 F F hSupp hSupp i i x hx).2
      rw [nativeOrdinaryZProduct_self_eq_row] at hh
      exact hh.trans (by change CO*eta*beta x*N*N ≤ CO*eta*e; nlinarith [mul_le_mul_of_nonneg_left hMass (mul_nonneg hCO.le heta)])
    have hJQBound : |⟪(nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2
        L q dr Ar p hdr hAr F).val x,
        nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F x⟫_ℝ-
      ⟪F.val x,nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
          (nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F) x⟫_ℝ| ≤ CJQ*eta*e := by
      have hh := hJQHere x hx
      rw [norm_finiteCoreSobolevLift] at hh
      exact hh.trans (by change CJQ*eta*beta x*N^2 ≤ CJQ*eta*e; nlinarith [mul_le_mul_of_nonneg_left hMass (mul_nonneg hCJQ.le heta)])
    have hFinite := abs_finite_RZ_sum_bound
      (fun i j => nativeOrdinaryRRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 hg2 dr Ar p hdr hAr q i j F x)
      (fun j => nativeDZeroCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x)
      (fun j => nativeJPCommutatorDensity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        g2 hg2 dr Ar p hdr hAr q j F ((dd j) F) x)
      (fun i => nativeOrdinaryZRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q i F x)
      _ (CO*eta*e) (CDQ*eta*e) (CJP*eta*e) (CO*eta*e) (CJQ*eta*e)
      hOrdR hDQBound hJPBound hOrdZ hJQBound
    have hExpanded : |R x|+|Z x| ≤
        9*(CO*eta*e)+3*(CDQ*eta*e)+3*(CJP*eta*e)+3*(CO*eta*e)+CJQ*eta*e := by
      simpa only [R,Z,nativeRFirstDensity,nativeZZeroDensity,nativeJPCommutatorDensity] using hFinite
    have hRows : |R x|+|Z x| ≤ C0*eta*e :=
      hExpanded.trans_eq (by dsimp only [C0]; ring)
    have hSource : e ≤ finiteCoreSourceEnergy hO hD (beta x) F x :=
      native_threeHalf_angular_energy_le_finiteCoreSourceEnergy hO hD (beta x) F x
    have hRef := hCompare q hq x (ball_subset_closedBall (hBall hx)) (beta x) hb1 F
    calc
      _ ≤ C0*eta*e := hRows
      _ ≤ C0*eta*finiteCoreSourceEnergy hO hD (beta x) F x := by gcongr
      _ ≤ C0*eta*(CE*E x) := by gcongr
      _ = CRZ*eta*E x := by dsimp only [CRZ]; ring
  have hPoint (x : R3) : |mu x*R x|+|mu x*Z x| ≤ CRZ*eta*(mu x*E x) := by
    have hmu : 0 ≤ mu x := (referenceDensityFamily_pos g hg L (q,x)).le
    rw [abs_mul,abs_mul,abs_of_nonneg hmu]
    by_cases hx : x ∈ K
    · have hh := mul_le_mul_of_nonneg_left (hPointK x hx) hmu
      nlinarith only [hh]
    · have hxF : x ∉ tsupport F.val := fun hy => hx (hSupp hy)
      have hz := nativeRZ_zero_off g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F x hxF
      change R x=0 ∧ Z x=0 at hz
      simp only [hz.1,hz.2,abs_zero,mul_zero,add_zero]
      exact mul_nonneg (mul_nonneg hCRZ.le heta)
        (mul_nonneg hmu (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q (beta x) (hbetaPos x).le F x))
  have hIntegral : (∫ x, |mu x*R x|+|mu x*Z x|) ≤ CRZ*eta*(∫ x, mu x*E x) := by
    calc
      _ ≤ ∫ x, CRZ*eta*(mu x*E x) := integral_mono (hRI.abs.add hZI.abs) (hEI.const_mul _) hPoint
      _ = _ := integral_const_mul _ _
  have hSeparate : |∫ x, mu x*R x|+|∫ x, mu x*Z x| ≤ CRZ*eta*(∫ x, mu x*E x) := by
    calc
      _ ≤ (∫ x, |mu x*R x|)+(∫ x, |mu x*Z x|) :=
        add_le_add (abs_integral_le_integral_abs) (abs_integral_le_integral_abs)
      _ = ∫ x, |mu x*R x|+|mu x*Z x| := (integral_add hRI.abs hZI.abs).symm
      _ ≤ _ := hIntegral
  refine ⟨hRI,hZI,hSeparate,?_⟩
  calc
    _ = |(∫ x, mu x*R x)+(∫ x, mu x*Z x)| := by
      rw [show (fun x => mu x*(R x+Z x)) = (fun x => mu x*R x+mu x*Z x) by funext x; ring,
        integral_add hRI hZI]
    _ ≤ |∫ x, mu x*R x|+|∫ x, mu x*Z x| := abs_add_le _ _
    _ ≤ _ := hSeparate

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSRZEnergy
