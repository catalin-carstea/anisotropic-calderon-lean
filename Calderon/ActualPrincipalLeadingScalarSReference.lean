import Calderon.ActualLeadingScalarSReferenceError
import Calderon.CoordinateBootstrapJets

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  ActualHigherSLeadingBracketGain ActualHigherSScalarCommutatorNativeForm ActualHigherSScalarCommutatorForm
open NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  FixedParameterProfilePullback FixedParameterProfileBudgets ActualScalarPrincipalAdjoint
  ScalarBaseAdjoint PerturbedDensityAdjoint ActualHigherSZeroScalarCommutatorForm

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))

local notation "Out" => actualLeadingSignedSecondOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "Cross" => ActualScalarSAdjointCross.nativeScalarSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

local notation "HQ" g2:max q:max => NormalizedPrincipalMetric.referenceNormalizedPrincipalDifference g g2 L q
local notation "Err" => actualLeadingScalarSReferenceError
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

/-- Original H8 profile budget for the literal actual normalized principal coefficient. -/
def ActualPrincipalLeadingScalarSReferenceBound
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) : Prop :=
  ∃ CErr : ℝ, 0 < CErr ∧ ∃ etaJ : ℝ, 0 < etaJ ∧ etaJ ≤ data.eta0 ∧ etaJ ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaJ →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8 (HQ g2 q) x ≤
      eta*referenceRadius dr Ar p L x) →
    ContDiff ℝ ∞ (Out hreg data g2 dr Ar p q F) ∧
    tsupport (Out hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (Out hreg data g2 dr Ar p q F) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,Out hreg data g2 dr Ar p q F x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      Cross hreg data.δ0 data.germs g2 dr Ar p hdr hAr q (HQ g2 q) F x) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      Err hreg data g2 dr Ar p hdr hAr q (HQ g2 q) F x) ∧
    |∫ x, referenceDensityFamily g L (q,x)*Err hreg data g2 dr Ar p hdr hAr q (HQ g2 q) F x| ≤
      CErr*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x

/-- Existing exact smoothness, symmetry and H8 recovery discharge every matrix callback. -/
theorem actual_principal_leading_scalar_S_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ActualPrincipalLeadingScalarSReferenceBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 := by
  obtain ⟨CErr,hCErr,etaJ,hEtaJ,hEtaJ0,hEtaJ1,hBound⟩ :=
    actual_leading_scalar_S_reference_bound
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg hKernel data g2 hg2
  refine ⟨CErr,hCErr,etaJ,hEtaJ,hEtaJ0,hEtaJ1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaJ K hK hKball F hsupp hb hs hH8
  have hh (i j : Fin 3) : ContDiff ℝ ∞ (fun x => (HQ g2 q) x i j) :=
    NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q i j
  have hjet (x : R3) (hx : x ∈ tsupport F.val) (i j k l : Fin 3) :
      TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => (HQ g2 q) y i j) x (eta*referenceRadius dr Ar p L x) :=
    CoordinateBootstrapJets.twoJetBound_component_of_coordinateH8_le
      (HQ g2 q) x hh i j k l (eta*referenceRadius dr Ar p L x) (hH8 x (hsupp hx))
  have hsym (x : R3) (_hx : x ∈ tsupport F.val) :
      ∀ᶠ y in 𝓝 x, ((HQ g2 q) y).IsHermitian :=
    Filter.Eventually.of_forall (fun y =>
      NormalizedPrincipalMetric.referenceNormalizedPrincipalDifference_isHermitian g g2 hg hg2 L q y)
  exact hBound q hq dr hdr hdr1 Ar hAr p hp eta heta hetaJ K hK hKball
    (HQ g2 q) hh F hsupp hb hs hjet hsym

/-- One actual Main endpoint record carries the actual principal contribution for every g2. -/
theorem exists_actual_principal_leading_scalar_S_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ selectedRoom : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)),
    ∃ data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg,
    ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ActualPrincipalLeadingScalarSReferenceBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 := by
  obtain ⟨selectedRoom,⟨data⟩⟩ := exists_actual_fullE_physical_endpoint_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg hKernel
  refine ⟨selectedRoom,data,?_⟩
  intro g2 hg2
  exact actual_principal_leading_scalar_S_reference_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hL hreg hKernel data g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
