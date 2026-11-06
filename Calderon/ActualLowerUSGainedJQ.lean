import Calderon.ActualLowerUSGeneratorZeroCommutator
import Calderon.ActualLowerUSJQExpansionMass
import Calderon.ActualLowerUSFinitePretestSupport

/-! Complete fixed-g2 JQ assembly from the actual primitive producer and the imported
generator/Q producer. No analytic cap callback is introduced as a theorem premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedJQ
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints ActualFullEGainedAssembly
  ActualRetainedGeneratorMultiplierGains ReferenceDensityBounds ConformalDepth
  ReferenceWeightedApproximation NormalizedPrincipalMetric ActualHigherSZeroPhysicalGraph
  ActualLowerUSGeneratorZeroCommutator ActualLowerUSJQExpansionMass
  ActualLowerUSFiniteQuadraticCommutator
  ActualFiniteHarmonicModel.ActualLowerUSLowerWordAdjoints

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


local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Qout" g2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeZeroOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "J" g2:max hg2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Js" g2:max hg2:max dr:max Ar:max p:max hdr:max hAr:max q:max =>
  nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LG" => lowerCoreAngularGenerator hO hD hF
local notation "LGS" => lowerCoreAngularGeneratorAdjoint hO hD hF
local notation "Word" => lowerQuadraticWord hO hD hF
local notation "WordStar" => lowerQuadraticWordAdjoint hO hD hF
private abbrev finiteWeightValue (s : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  (coreWeightOperator hO hD (SpectralWeightedGraph.besselWeight s) F).val x
local notation "WH" F:max x:max => ‖finiteWeightValue hO hD (1/2 : ℝ) F x‖
local notation "WHi" F:max x:max => ‖finiteWeightValue hO hD (3/2 : ℝ) F x‖

/-- Complete original fixed-metric gained J/Q conclusion. The actual all-five-
group primitive producer is invoked internally; no cap callback is a premise. -/
theorem exists_nativeJQ_uniform_profile_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ C_JQ : ℝ, 0 < C_JQ ∧ ∃ etaJQ : ℝ, 0 < etaJQ ∧ etaJQ ≤ data.eta0 ∧ etaJQ ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaJQ →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x * (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
      ∀ x ∈ K,
        |⟪((Js g2 hg2 dr Ar p hdr hAr q) F).val x,(Qout g2 dr Ar p hdr hAr q) F x⟫_ℝ -
          ⟪F.val x,(Qout g2 dr Ar p hdr hAr q) ((J g2 hg2 dr Ar p hdr hAr q) F) x⟫_ℝ| ≤
          C_JQ * eta * actualReferenceBeta g L q dr Ar p x *
            ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖^2 := by
  obtain ⟨δ,Cm,hJac,CG,hCG,etaG,hEtaG,hEtaG0,hEtaG1,hG⟩ :=
    exists_lowerGeneratorZeroCommutator_uniform_profile_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 hL hKernel
  obtain ⟨CJ,hCJ,hExp⟩ := exists_nativeJQ_lower_word_expansion_uniform_mass
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 hL
  let G0 : ℝ := coreAngularGeneratorBound hO hD
  have hG0 : 0 < G0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<15)
    (coreAngularGeneratorBound_bounds hO hD).1
  let CC : ℝ := 2*G0*CG*CJ
  let C_JQ : ℝ := 1+CC
  have hCC : 0 ≤ CC := by dsimp only [CC]; positivity
  have hC : 0 < C_JQ := by dsimp only [C_JQ]; positivity
  refine ⟨C_JQ,hC,etaG,hEtaG,hEtaG0,hEtaG1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hSupp hb hs hH8 x hx
  have heta1 : eta ≤ 1 := hetaG.trans hEtaG1
  have hProfile := hG q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball hb hs hH8
  have hTF : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom δ :=
    fun y hy => hProfile.1 y (hSupp hy)
  have hxClosed : x ∈ closedBall y0 ρ := ball_subset_closedBall (hKball hx)
  obtain ⟨c,hc,hJ,hMass,hEq⟩ :=
    hExp q hq dr hdr hdr1 Ar hAr p hp eta heta heta1 x hxClosed (hb x hx) (hH8 x hx) (hs x hx)
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let N : ℝ := WHi F x
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hBeta : 1 ≤ beta := hb x hx
  have hr1 : r ≤ 1 := by
    have hb2 : 1 ≤ beta^2 := one_le_pow₀ hBeta
    have hrb : r ≤ r*beta^2 := le_mul_of_one_le_right hr.le hb2
    exact (hrb.trans (hs x hx)).trans heta1
  have hrBeta : r ≤ beta := hr1.trans hBeta
  have hRate : 0 ≤ CG*r := mul_nonneg hCG.le hr.le
  let wordForm (ij : LowerCoreAngularGeneratorIndex × LowerCoreAngularGeneratorIndex) : ℝ :=
    ⟪(WordStar ij F).val x,(Qout g2 dr Ar p hdr hAr q) F x⟫_ℝ -
      ⟪F.val x,(Qout g2 dr Ar p hdr hAr q) (Word ij F) x⟫_ℝ
  let BW : ℝ := (2*G0*CG*r)*N^2
  have hBW : 0 ≤ BW := by dsimp only [BW]; positivity
  have hWords : ∀ ij, |wordForm ij| ≤ BW := by
    intro ij
    have hStarSupp : tsupport (LGS ij.1 F).val ⊆ K :=
      (finiteCoreSupportPreserving_lowerCoreAngularGeneratorAdjoint hO hD hF ij.1 F).trans hSupp
    have hLowSupp : tsupport (LG ij.2 F).val ⊆ K :=
      (finiteCoreSupportPreserving_lowerCoreAngularGenerator hO hD hF ij.2 F).trans hSupp
    have hbComm := (hProfile.2 ij.2 (LGS ij.1 F) F hStarSupp hSupp x hx).1
    have haComm := (hProfile.2 ij.1 F (LG ij.2 F) hSupp hLowSupp x hx).2
    have hStarNorm := (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator
      hO hD hF ij.1 x).2.2.2.2 F
    have hLowNorm := (hasCoreAngularFirstOrderBounds_lowerCoreAngularGenerator
      hO hD hF ij.2 x).2.2.2.1 F
    have h1 := hbComm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hStarNorm hRate) (norm_nonneg _))
    have h2 := haComm.trans (mul_le_mul_of_nonneg_left hLowNorm
      (mul_nonneg hRate (norm_nonneg _)))
    dsimp only [wordForm]
    rw [lowerQuadraticWord_zero_commutator_split
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg data.δ0 data.germs g2 dr Ar p hdr hAr q ij F F x]
    calc
      _ ≤ |lowerGeneratorZeroCommutatorDensity
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg data.δ0 data.germs g2 dr Ar p hdr hAr q ij.2 (LGS ij.1 F) F x| +
          |lowerGeneratorZeroCommutatorDensity
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            hreg data.δ0 data.germs g2 dr Ar p hdr hAr q ij.1 F (LG ij.2 F) x| := abs_add_le _ _
      _ ≤ (CG*r)*(G0*N)*N + (CG*r)*N*(G0*N) := add_le_add h1 h2
      _ = BW := by dsimp only [BW]; ring
  have hLiftNorm : ‖finiteCoreSobolevLift hO hD (3/2 : ℝ) F x‖ = N :=
    norm_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x
  rw [hLiftNorm,hEq hreg data.δ0 data.germs δ Cm hJac F F hTF]
  change |∑ ij, c ij x*wordForm ij| ≤ C_JQ*eta*beta*N^2
  calc
    _ ≤ ∑ ij, |c ij x*wordForm ij| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ij, |c ij x| * |wordForm ij| := by simp only [abs_mul]
    _ ≤ ∑ ij, |c ij x| * BW :=
      Finset.sum_le_sum (fun ij _ => mul_le_mul_of_nonneg_left (hWords ij) (abs_nonneg _))
    _ = (∑ ij, |c ij x|)*BW := (Finset.sum_mul _ _ _).symm
    _ ≤ (CJ*eta)*BW := mul_le_mul_of_nonneg_right hMass hBW
    _ = CC*eta*r*N^2 := by dsimp only [CC,BW]; ring
    _ ≤ C_JQ*eta*r*N^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C_JQ]; linarith : CC ≤ C_JQ) heta) hr.le)
        (sq_nonneg N)
    _ ≤ C_JQ*eta*beta*N^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrBeta (mul_nonneg hC.le heta)) (sq_nonneg N)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSGainedJQ
