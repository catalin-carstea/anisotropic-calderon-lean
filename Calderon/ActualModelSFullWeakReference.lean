import Calderon.ActualPerturbedModelSupport

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualHigherSLeadingBracketGain ConformalDepth ReferenceWeightedApproximation ReferenceDensityBounds
  FixedParameterProfilePullback FixedParameterProfileBudgets

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


/-- Literal weak operator of the complete original U/S cross group. -/
def actualUSMixedWeakOut (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  actualModelSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p hdr hAr q (UF F) (UD F) x

/-- Exact original shifted model+S norm defect, retaining the full S-self term literally. -/
def ActualModelSFullWeakReference (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let m := (MR F).val
  let b := ((MD F)+(2:ℝ) • (ZZ F)).val
  let sf := SO F
  let sd := SD F
  let wt : R3 → ℝ := fun x => ⟪F.val x,
    actualTSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 dr Ar p hdr hAr q F x⟫_ℝ
  let wu : R3 → ℝ := fun x => ⟪F.val x,
    actualUSMixedWeakOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F x⟫_ℝ
  ActualModelSMixedIntegralIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q F ∧
  ActualTSMixedWeakIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p hdr hAr q F ∧
  Integrable (fun x => mu x*wu x) ∧
  (∫ x, mu x*(⟪(UF F).val x,sf x⟫_ℝ-⟪(UD F).val x,sd x⟫_ℝ)) =
    (∫ x, mu x*wu x) ∧
  (∫ x, mu x*‖m x+sf x‖^2)-(∫ x, mu x*‖b x+sd x‖^2) =
    ((∫ x, mu x*‖m x‖^2)-(∫ x, mu x*‖b x‖^2))+
    ((∫ x, mu x*‖sf x‖^2)-(∫ x, mu x*‖sd x‖^2))+
    4*(∫ x, mu x*wt x)+2*(∫ x, mu x*wu x)

/-- Genuine finite adjunction and checked model locality discharge both mixed groups. -/
theorem actual_model_S_full_weak_reference_of_common_room (δ : ℝ) (Cm : CRoom δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ,
      ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z)
    (hq : q ∈ Icc (0 : ℝ) 1) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ) :
    ActualModelSFullWeakReference g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  have hMixed := actual_model_S_mixed_integral_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF
  have hT := actual_T_S_mixed_weak_identity_of_common_room (hg2 := hg2)
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p hdr hAr q δ Cm F hTF
  have hUA : tsupport (UF F).val ⊆ tsupport F.val :=
    finiteCoreSupportPreserving_nativeU hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F
  have hUB : tsupport (UD F).val ⊆ tsupport F.val :=
    finiteCoreSupportPreserving_nativeUdag hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F
  have hU := actual_model_S_mixed_weak_identity_of_common_room (hg2 := hg2)
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p hdr hAr q δ Cm F (UF F) (UD F)
    hTF (fun x hx => hTF x (hUA hx)) (fun x hx => hTF x (hUB hx))
  refine ⟨hMixed,hT,hU.2.1,hU.2.2,?_⟩
  have hEq := hMixed.2.2.2.2.2.2.2.2
  rw [hEq,hT.2.2,hU.2.2]
  rfl

/-- One original threshold before both metrics/profiles/inputs in the full weak identity. -/
def ActualModelSFullWeakUniformReference : Prop :=
  ∃ etaID : ℝ, 0 < etaID ∧ etaID ≤ data.eta0 ∧ etaID ≤ 1 ∧
    ∀ g2 : MatrixField, ∀ hg2 : IsAdmissibleMetric g2,
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
    ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
    ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaID →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    ActualModelSFullWeakReference g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F

/-- Genuine room and uniform profile guard retain the actual original trace/germ witness. -/
theorem actual_model_S_full_weak_uniform_reference (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ActualModelSFullWeakUniformReference g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
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
  exact actual_model_S_full_weak_reference_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm hJac hq F hTF

/-- Actual Main selects one room/trace/germ before the common full weak comparison. -/
theorem exists_actual_model_S_full_weak_uniform_reference (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ selectedRoom : ReferenceGaugeNormalReciprocalRoom g L Φ a
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)),
    ∃ selectedData : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg,
      ActualModelSFullWeakUniformReference g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        selectedRoom hreg selectedData := by
  obtain ⟨selectedRoom,⟨selectedData⟩⟩ := exists_actual_fullE_physical_endpoint_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hL hreg hKernel
  exact ⟨selectedRoom,selectedData,actual_model_S_full_weak_uniform_reference
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 selectedRoom hreg selectedData hL hKernel⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualModelSMixedComparison
