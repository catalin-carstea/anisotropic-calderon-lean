import Calderon.ActualModelSMixedPointwise
import Calderon.ActualPhysicalModelResidualEnergy

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints

open MeasureTheory ReferenceDensityBounds FixedParameterProfilePullback FixedParameterProfileBudgets
  ActualHigherSLeadingBracketGain ConformalDepth ReferenceWeightedApproximation

/-- Weighted real difference: both integrability and literal integral splitting. -/
theorem weighted_difference_integral (mu f h : R3 → ℝ)
    (hf : Integrable (fun x => mu x*f x)) (hh : Integrable (fun x => mu x*h x)) :
    Integrable (fun x => mu x*(f x-h x)) ∧
      (∫ x, mu x*(f x-h x)) = (∫ x, mu x*f x)-(∫ x, mu x*h x) := by
  have he : (fun x => mu x*(f x-h x)) = (fun x => mu x*f x-mu x*h x) := by
    funext x
    ring
  refine ⟨Eq.mpr (congrArg (fun v : R3 → ℝ => Integrable v) he) (hf.sub hh),?_⟩
  exact (congrArg (fun v : R3 → ℝ => ∫ x, v x) he).trans (integral_sub hf hh)

/-- Exact four-term weighted splitting used by the original mixed comparison. -/
theorem integral_mixed_four_terms (f h ct cu : R3 → ℝ)
    (hf : Integrable f) (hh : Integrable h) (ht : Integrable ct) (hu : Integrable cu) :
    (∫ x, (f x+h x)+4*ct x+2*cu x) =
      (∫ x, f x)+(∫ x, h x)+4*(∫ x, ct x)+2*(∫ x, cu x) := by
  have hfh : Integrable (fun x => f x+h x) := hf.add hh
  have hfht : Integrable (fun x => (f x+h x)+4*ct x) := hfh.add (ht.const_mul 4)
  calc
    _ = (∫ x, (f x+h x)+4*ct x)+(∫ x, 2*cu x) := integral_add hfht (hu.const_mul 2)
    _ = _ := by
      rw [integral_add hfh (ht.const_mul 4),integral_add hf hh,
        integral_const_mul,integral_const_mul]

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
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- The original shifted model/S comparison with every required weighted integral defined. -/
def ActualModelSMixedIntegralIdentity (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let m := (MR F).val
  let b := ((MD F)+(2:ℝ) • (ZZ F)).val
  let sf := SO F
  let sd := SD F
  let t := (TF F).val
  let td := ((TD F)+(ZZ F)).val
  let u := (UF F).val
  let ud := (UD F).val
  Integrable (fun x => mu x*‖m x+sf x‖^2) ∧
  Integrable (fun x => mu x*‖b x+sd x‖^2) ∧
  Integrable (fun x => mu x*‖m x‖^2) ∧
  Integrable (fun x => mu x*‖b x‖^2) ∧
  Integrable (fun x => mu x*‖sf x‖^2) ∧
  Integrable (fun x => mu x*‖sd x‖^2) ∧
  Integrable (fun x => mu x*(⟪t x,sf x⟫_ℝ-⟪td x,sd x⟫_ℝ)) ∧
  Integrable (fun x => mu x*(⟪u x,sf x⟫_ℝ-⟪ud x,sd x⟫_ℝ)) ∧
  (∫ x, mu x*‖m x+sf x‖^2)-(∫ x, mu x*‖b x+sd x‖^2) =
    ((∫ x, mu x*‖m x‖^2)-(∫ x, mu x*‖b x‖^2))+
    ((∫ x, mu x*‖sf x‖^2)-(∫ x, mu x*‖sd x‖^2))+
    4*(∫ x, mu x*(⟪t x,sf x⟫_ℝ-⟪td x,sd x⟫_ℝ))+
    2*(∫ x, mu x*(⟪u x,sf x⟫_ℝ-⟪ud x,sd x⟫_ℝ))

/-- Existing genuine common-room formation discharges all mixed integrabilities. -/
theorem actual_model_S_mixed_integral_of_common_room (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ) :
    ActualModelSMixedIntegralIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let m := (MR F).val
  let bF := (MD F)+(2:ℝ) • (ZZ F)
  let b := bF.val
  let sf := SO F
  let sd := SD F
  let tF := TF F
  let tdF := (TD F)+(ZZ F)
  let uF := UF F
  let udF := UD F
  have hS := ActualCommonQuadraticFormationConsumer.higherSOutputConclusions_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm hJac g2 hg2 dr Ar p hdr hAr q hq F hTF
  have hsf : ContDiff ℝ ∞ sf := hS.2.2.2.2.2.1.1
  have hcsf : HasCompactSupport sf := hS.2.2.2.2.2.1.2.2
  have hsd := ActualHigherSAdjointFormation.contDiff_higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q F hTF
  have hcsd := ActualHigherSAdjointFormation.hasCompactSupport_higherSAdjointOut
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs g2 dr Ar p hdr hAr q F
  have hA := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact
    g hg L q (fun x => m x+sf x) ((MR F).property.1.add hsf) ((MR F).property.2.1.add hcsf)
  have hB := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact
    g hg L q (fun x => b x+sd x) (bF.property.1.add hsd) (bF.property.2.1.add hcsd)
  have hM := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact
    g hg L q m (MR F).property.1 (MR F).property.2.1
  have hBM := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact
    g hg L q b bF.property.1 bF.property.2.1
  have hNS := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact g hg L q sf hsf hcsf
  have hND := MixedKernelConstructionTask.referenceDensity_integrable_normSq_of_smooth_compact g hg L q sd hsd hcsd
  have hTS := MixedKernelConstructionTask.referenceDensity_integrable_model_error_pairing
    g hg L q tF.val sf tF.property.1 hsf tF.property.2.1
  have hTDS := MixedKernelConstructionTask.referenceDensity_integrable_model_error_pairing
    g hg L q tdF.val sd tdF.property.1 hsd tdF.property.2.1
  have hUS := MixedKernelConstructionTask.referenceDensity_integrable_model_error_pairing
    g hg L q uF.val sf uF.property.1 hsf uF.property.2.1
  have hUDS := MixedKernelConstructionTask.referenceDensity_integrable_model_error_pairing
    g hg L q udF.val sd udF.property.1 hsd udF.property.2.1
  have hCT := weighted_difference_integral mu (fun x => ⟪tF.val x,sf x⟫_ℝ)
    (fun x => ⟪tdF.val x,sd x⟫_ℝ) hTS hTDS
  have hCU := weighted_difference_integral mu (fun x => ⟪uF.val x,sf x⟫_ℝ)
    (fun x => ⟪udF.val x,sd x⟫_ℝ) hUS hUDS
  have hG := weighted_difference_integral mu (fun x => ‖m x‖^2) (fun x => ‖b x‖^2) hM hBM
  have hSS := weighted_difference_integral mu (fun x => ‖sf x‖^2) (fun x => ‖sd x‖^2) hNS hND
  have hFull := weighted_difference_integral mu
    (fun x => ‖m x+sf x‖^2) (fun x => ‖b x+sd x‖^2) hA hB
  let vg : R3 → ℝ := fun x => mu x*(‖m x‖^2-‖b x‖^2)
  let vs : R3 → ℝ := fun x => mu x*(‖sf x‖^2-‖sd x‖^2)
  let vt : R3 → ℝ := fun x => mu x*(⟪tF.val x,sf x⟫_ℝ-⟪tdF.val x,sd x⟫_ℝ)
  let vu : R3 → ℝ := fun x => mu x*(⟪uF.val x,sf x⟫_ℝ-⟪udF.val x,sd x⟫_ℝ)
  have he : (fun x => mu x*(‖m x+sf x‖^2-‖b x+sd x‖^2)) =
      (fun x => (vg x+vs x)+4*vt x+2*vu x) := by
    funext x
    have hp := actual_model_S_signed_pointwise
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x
    change ‖m x+sf x‖^2-‖b x+sd x‖^2 =
      (‖m x‖^2-‖b x‖^2)+(‖sf x‖^2-‖sd x‖^2)+
        4*(⟪tF.val x,sf x⟫_ℝ-⟪tdF.val x,sd x⟫_ℝ)+
        2*(⟪uF.val x,sf x⟫_ℝ-⟪udF.val x,sd x⟫_ℝ) at hp
    rw [hp]
    dsimp only [vg,vs,vt,vu]
    ring
  refine ⟨hA,hB,hM,hBM,hNS,hND,hCT.1,hCU.1,?_⟩
  calc
    _ = ∫ x, mu x*(‖m x+sf x‖^2-‖b x+sd x‖^2) := hFull.2.symm
    _ = ∫ x, (vg x+vs x)+4*vt x+2*vu x := congrArg (fun f : R3 → ℝ => ∫ x, f x) he
    _ = (∫ x, vg x)+(∫ x, vs x)+4*(∫ x, vt x)+2*(∫ x, vu x) :=
      integral_mixed_four_terms vg vs vt vu hG.1 hSS.1 hCT.1 hCU.1
    _ = _ := by rw [hG.2,hSS.2]

/-- One true room threshold before every metric/profile/input, with the same actual Main germ. -/
theorem exists_actual_model_S_mixed_integral_identity (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ etaID : ℝ, 0 < etaID ∧ etaID ≤ data.eta0 ∧ etaID ≤ 1 ∧
    ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2,
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaID →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    ActualModelSMixedIntegralIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  obtain ⟨δ,Cm,hJac⟩ :=
    ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaRoom,hEtaRoom,hEtaRoom1,hGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ Cm.rev.pos
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨min data.eta0 etaRoom,lt_min data.eta0_pos hEtaRoom,min_le_left _ _,
    (min_le_right _ _).trans hEtaRoom1,?_⟩
  intro g2 hg2 q hq dr hdr hdr1 Ar hAr p hp eta heta hetaID K _hK hKball F hsupp hb hs
  have hTF (x : R3) (hx : x ∈ tsupport F.val) :
      ActualHigherSFormation.higherSParam L dr Ar p q x ∈ ParamRoom δ := by
    have ht := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta
      (hetaID.trans (min_le_right _ _)) x
      (ball_subset_closedBall (hKball (hsupp hx))) (hKball (hsupp hx))
      (hb x (hsupp hx)) (hs x (hsupp hx))
    exact (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x ht).self_of_nhds
  exact actual_model_S_mixed_integral_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
