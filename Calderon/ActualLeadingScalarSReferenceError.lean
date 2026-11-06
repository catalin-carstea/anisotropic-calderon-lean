import Calderon.ActualLeadingFullOutputReferenceForm
import Calderon.ActualScalarSAdjointCross

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

/-- The literal leading contribution plus twice the original physical scalar/S cross density. -/
def actualLeadingScalarSReferenceError
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
    (q : ℝ) (h : MatrixField) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪F.val x,Out hreg data g2 dr Ar p q F x⟫_ℝ+
    2*Cross hreg data.δ0 data.germs g2 dr Ar p hdr hAr q h F x
local notation "Err" => actualLeadingScalarSReferenceError
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

/-- Original matrix hypotheses, one actual endpoint record and no assumed parameter membership. -/
def ActualLeadingScalarSReferenceBound
    (hreg : FixedDirichletRegularity)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) : Prop :=
  ∃ CErr : ℝ, 0 < CErr ∧ ∃ etaJ : ℝ, 0 < etaJ ∧ etaJ ≤ data.eta0 ∧ etaJ ≤ 1 ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaJ →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun x => h x i j)) →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ tsupport F.val, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun y => h y i j) x (eta*referenceRadius dr Ar p L x)) →
    (∀ x ∈ tsupport F.val, ∀ᶠ y in 𝓝 x, (h y).IsHermitian) →
    ContDiff ℝ ∞ (Out hreg data g2 dr Ar p q F) ∧
    tsupport (Out hreg data g2 dr Ar p q F) ⊆ tsupport F.val ∧
    HasCompactSupport (Out hreg data g2 dr Ar p q F) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪F.val x,Out hreg data g2 dr Ar p q F x⟫_ℝ) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      Cross hreg data.δ0 data.germs g2 dr Ar p hdr hAr q h F x) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      Err hreg data g2 dr Ar p hdr hAr q h F x) ∧
    |∫ x, referenceDensityFamily g L (q,x)*Err hreg data g2 dr Ar p hdr hAr q h F x| ≤
      CErr*eta*∫ x, referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x

/-- The two original signed estimates share the actual germ, trace, profile and energy. -/
theorem actual_leading_scalar_S_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ActualLeadingScalarSReferenceBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 := by
  obtain ⟨δS,hδS,_hδS0,_hδSρ,_Cm,_hJac,hCross⟩ :=
    ActualScalarSAdjointCross.exists_retained_actual_scalar_S_signed_cross_reference_form
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs hL
  obtain ⟨etaRoom,hEtaRoom,hEtaRoom1,hRoomGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δS hδS
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨CLead,hCLead,etaLead,hEtaLead,hEtaLead0,hLeading⟩ :=
    exists_actual_leading_full_output_reference_form
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  obtain ⟨CCross,hCCross,hCrossBound⟩ := hCross g2 hg2
  refine ⟨CLead+2*CCross,by positivity,min etaLead etaRoom,lt_min hEtaLead hEtaRoom,
    (min_le_left _ _).trans hEtaLead0,(min_le_right _ _).trans hEtaRoom1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaJ K hK hKball h hh F hsupp hb hs hjet hsym
  have hetaL : eta ≤ etaLead := hetaJ.trans (min_le_left _ _)
  have hetaR : eta ≤ etaRoom := hetaJ.trans (min_le_right _ _)
  have heta1 : eta ≤ 1 := hetaR.trans hEtaRoom1
  have hTF (x : R3) (hx : x ∈ tsupport F.val) : (Tq dr Ar p q) x ∈ ParamRoom δS := by
    have ht := hRoomGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hetaR
      x (ball_subset_closedBall (hKball (hsupp hx))) (hKball (hsupp hx))
      (hb x (hsupp hx)) (hs x (hsupp hx))
    exact (higherSParam_eventually_mem y0 ρ δS L dr Ar q p hdr hAr x ht).self_of_nhds
  obtain ⟨hSmooth,hSupp,hCompact,_hGraph,_hCoeff,hLeadInt,hEnergyInt,hLeadBound⟩ :=
    hLeading q hq dr hdr hdr1 Ar hAr p hp eta heta hetaL K hK hKball F hsupp hb hs
  obtain ⟨hCrossInt,_hCrossEnergy,hCrossEstimate⟩ :=
    hCrossBound dr Ar p hdr hdr1 hAr hp q hq eta heta heta1 h hh F hTF hjet hsym
      (fun x hx => hb x (hsupp hx)) (fun x hx => hs x (hsupp hx))
  let dLead : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)*
    ⟪F.val x,Out hreg data g2 dr Ar p q F x⟫_ℝ
  let dCross : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)*
    Cross hreg data.δ0 data.germs g2 dr Ar p hdr hAr q h F x
  have he : (fun x => referenceDensityFamily g L (q,x)*
      Err hreg data g2 dr Ar p hdr hAr q h F x) = (fun x => dLead x+2*dCross x) := by
    funext x
    dsimp only [actualLeadingScalarSReferenceError,dLead,dCross]
    ring
  have hSumInt : Integrable (fun x => dLead x+2*dCross x) :=
    hLeadInt.add (hCrossInt.const_mul 2)
  have hErrInt : Integrable (fun x => referenceDensityFamily g L (q,x)*
      Err hreg data g2 dr Ar p hdr hAr q h F x) :=
    Eq.mpr (congrArg (fun f : R3 → ℝ => Integrable f) he) hSumInt
  have hSplit : (∫ x, referenceDensityFamily g L (q,x)*
      Err hreg data g2 dr Ar p hdr hAr q h F x) =
      (∫ x, dLead x)+2*(∫ x, dCross x) := by
    calc
      _ = ∫ x, dLead x+2*dCross x := congrArg (fun f : R3 → ℝ => ∫ x, f x) he
      _ = (∫ x, dLead x)+(∫ x, 2*dCross x) := integral_add hLeadInt (hCrossInt.const_mul 2)
      _ = _ := by rw [integral_const_mul]
  refine ⟨hSmooth,hSupp,hCompact,hLeadInt,hCrossInt,hEnergyInt,hErrInt,?_⟩
  calc
    _ = |(∫ x, dLead x)+2*(∫ x, dCross x)| := congrArg abs hSplit
    _ ≤ |∫ x, dLead x|+|2*(∫ x, dCross x)| := abs_add_le _ _
    _ = |∫ x, dLead x|+2*|∫ x, dCross x| := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ CLead*eta*(∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)+
        2*(CCross*eta*(∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)) :=
      add_le_add hLeadBound (mul_le_mul_of_nonneg_left hCrossEstimate (by norm_num))
    _ = _ := by ring

/-- Main supplies one actual endpoint record before either signed estimate is chosen. -/
theorem exists_actual_leading_scalar_S_reference_bound (hL : 0 < L)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ selectedRoom : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)),
    ∃ data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg,
    ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ActualLeadingScalarSReferenceBound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg data g2 := by
  obtain ⟨selectedRoom,⟨data⟩⟩ := exists_actual_fullE_physical_endpoint_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg hKernel
  refine ⟨selectedRoom,data,?_⟩
  intro g2 hg2
  exact actual_leading_scalar_S_reference_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hL hreg hKernel data g2 hg2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
