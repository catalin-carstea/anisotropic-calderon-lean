import Calderon.ActualLowerUSAdjointCore
import Calderon.ActualLowerUSIntegralSplit

/-!
Actual full S/true S-adjoint weak-domain identity and original-profile integrability.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSWeakDomain
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualFullEGainedAssembly ActualModelSMixedComparison ActualAngularHighDraft ConformalDepth
  ReferenceWeightedApproximation ReferenceDensityBounds NormalizedPrincipalMetric
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

local notation "SO" => ActualHigherSFormation.nativeHigherSOut
  hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
  dr Ar p hdr hAr q hreg data.δ0 data.germs g2
local notation "SD" => ActualHigherSAdjointFormation.higherSAdjointOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  hreg data.δ0 data.germs g2 dr Ar p hdr hAr q
local notation "AF" => nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LA" => nativeULowerAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "LO" => nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Lo" => nativeULowerSCrossDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 hg2 dr Ar p hdr hAr q
local notation "CRoom" δ:max => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs δ
local notation "Tq" => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Safe actual weak output; both arguments of S and S-dagger are genuine finite inputs. -/
def actualLowerSWeakOut (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : SphereL2 :=
  SD (AF F) x - SO (LA F) x

/-- The concrete diagonal weak [LA,S] density; LA is never applied to an S output. -/
def actualLowerSWeakDensity (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ℝ :=
  ⟪(AF F).val x,SO F x⟫_ℝ - ⟪F.val x,SO (LA F) x⟫_ℝ

local notation "WO" => actualLowerSWeakOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 hg2 dr Ar p hdr hAr q
local notation "WD" => actualLowerSWeakDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
  g2 hg2 dr Ar p hdr hAr q

/-- Integrability and exact signed identities for the same original physical S. -/
def ActualLowerSWeakIdentity (F : smoothCompactFiniteSphereCore hO hD) : Prop :=
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  Integrable (fun x => mu x * Lo F x) ∧
  Integrable (fun x => mu x * WD F x) ∧
  Integrable (fun x => mu x * ⟪F.val x,WO F x⟫_ℝ) ∧
  (∫ x, mu x * Lo F x) = (∫ x, mu x * WD F x) ∧
  (∫ x, mu x * WD F x) = (∫ x, mu x * ⟪F.val x,WO F x⟫_ℝ)

/-- Locality discharges composed-input rooms; the original full physical adjoint
supplies the integrated replacement and all weighted integrability. -/
theorem actualLowerSWeakIdentity_of_common_room
    (δ : ℝ) (Cm : CRoom δ) (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, Tq x ∈ ParamRoom δ) :
    ActualLowerSWeakIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  have hTA : ∀ x ∈ tsupport (AF F).val, Tq x ∈ ParamRoom δ := by
    intro x hx
    exact hTF x (finiteCoreSupportPreserving_nativeUFirstZeroPart
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F hx)
  have hTLA : ∀ x ∈ tsupport (LA F).val, Tq x ∈ ParamRoom δ := by
    intro x hx
    exact hTF x (finiteCoreSupportPreserving_nativeULowerAdjointCore
      hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F hx)
  have hMixed := actual_model_S_mixed_weak_identity_of_common_room (hg2 := hg2)
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 dr Ar p hdr hAr q δ Cm F (AF F) (LA F) hTF hTA hTLA
  have hMixedActual :
      Integrable (fun x => referenceDensityFamily g L (q,x) * Lo F x) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x) * ⟪F.val x,WO F x⟫_ℝ) ∧
      (∫ x, referenceDensityFamily g L (q,x) * Lo F x) =
        ∫ x, referenceDensityFamily g L (q,x) * ⟪F.val x,WO F x⟫_ℝ := by
    simpa only [nativeULowerSCrossDensity,nativeULowerAdjointCore_apply,
      actualModelSMixedWeakOut,actualLowerSWeakOut] using hMixed
  have hA := ActualHigherSAdjointFormation.integrated_higherS_physical_adjoint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs δ Cm g2 hg2 dr Ar p hdr hAr q (AF F) F hTA hTF
  have hAd := ActualLowerUSAdjointCore.actual_lower_adjoint_S_weak_identity_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm F hTF
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  have hOld := weighted_difference_integral mu
    (fun x => ⟪(AF F).val x,SO F x⟫_ℝ) (fun x => ⟪LO F x,SD F x⟫_ℝ) hA.1 hAd.1
  have hNew := weighted_difference_integral mu
    (fun x => ⟪(AF F).val x,SO F x⟫_ℝ) (fun x => ⟪F.val x,SO (LA F) x⟫_ℝ) hA.1 hAd.2.1
  have hEq : (∫ x, mu x * Lo F x) = ∫ x, mu x * WD F x := by
    change (∫ x, mu x * (⟪(AF F).val x,SO F x⟫_ℝ-⟪LO F x,SD F x⟫_ℝ)) =
      ∫ x, mu x * (⟪(AF F).val x,SO F x⟫_ℝ-⟪F.val x,SO (LA F) x⟫_ℝ)
    rw [hOld.2,hNew.2,hAd.2.2]
  exact ⟨hMixedActual.1,hNew.1,hMixedActual.2.1,hEq,hEq.symm.trans hMixedActual.2.2⟩

/-- Original-profile producer, with the exact integral split retained. This
asserts no coefficient estimate and no additional metric-neighborhood uniformity. -/
theorem exists_actualLowerSWeakIdentity
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ etaUS : ℝ, 0 < etaUS ∧ etaUS ≤ data.eta0 ∧ etaUS ≤ 1 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 →
      ∀ Ar : ℝ, ∀ hAr : 0 < Ar, ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaUS →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x *
        (actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ K, CoordinateBootstrapJets.coordinateH8
        (referenceNormalizedPrincipalDifference g g2 L q) x ≤ eta * referenceRadius dr Ar p L x) →
      ActualLowerSWeakIdentity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F ∧
      ActualLowerUSIntegralSplit.LowerUSIntegralSplit
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        Room hreg data g2 hg2 dr Ar p hdr hAr q F := by
  obtain ⟨δ,Cm,_hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg hKernel data.δ0 data.δ0_pos data.germs
  obtain ⟨etaRoom,hEtaRoom,hEtaRoom1,hGuard⟩ :=
    exists_uniform_strict_higherSParam_guard g hg L hL y0 ρ δ Cm.rev.pos
      (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨etaSplit,hEtaSplit,hEtaSplit0,hEtaSplit1,hSplit⟩ :=
    ActualLowerUSIntegralSplit.exists_lowerUSIntegralSplit
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      Room hreg data g2 hg2 hL hKernel
  refine ⟨min etaSplit etaRoom,lt_min hEtaSplit hEtaRoom,
    (min_le_left _ _).trans hEtaSplit0,(min_le_left _ _).trans hEtaSplit1,?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaUS K hK hBall F hsupp hb hs hH8
  have hTF (x : R3) (hx : x ∈ tsupport F.val) :
      ActualHigherSFormation.higherSParam L dr Ar p q x ∈ ParamRoom δ := by
    have ht := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta
      (hetaUS.trans (min_le_right _ _)) x
      (ball_subset_closedBall (hBall (hsupp hx))) (hBall (hsupp hx))
      (hb x (hsupp hx)) (hs x (hsupp hx))
    exact (higherSParam_eventually_mem y0 ρ δ L dr Ar q p hdr hAr x ht).self_of_nhds
  exact ⟨actualLowerSWeakIdentity_of_common_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    Room hreg data g2 hg2 dr Ar p hdr hAr q δ Cm F hTF,
    hSplit q hq dr hdr hdr1 Ar hAr p hp eta heta (hetaUS.trans (min_le_left _ _))
      K hK hBall F hsupp hb hs hH8⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerSWeakDomain
