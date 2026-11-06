import Calderon.ActualQradCompactOutputFormation
import Calderon.ActualQradUniformFirstOutputSections
import Calderon.ActualQradFirstOutputGraphTransport
import Calderon.ActualQradSectionContinuityAndHighGraph
import Calderon.ActualFinitePairedRadialRemainderClosedSections
import Calderon.ActualOriginalPiQradReferenceProfile
import Calderon.ActualFinitePairedRadialRemainderSections
import Calderon.ActualFinitePhysicalWeakSquaredNorm
import Calderon.ActualQradJointCoefficientCaps
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderTopologyCoercivity

/-! Original-Pi Qrad self row as a difference of two SEPARATELY integrable weighted squared norms
(author-only successor, v010). Complete expansion: output/MATHEMATICS.md (N0–N7), written before
these declarations. Imports the proposed parent `Calderon.ActualOriginalPiQradReferenceProfile`
without redoing it. No compiler was run; no acceptance is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
open ActualFiniteHarmonicCore ActualFiniteHarmonicModel ReferenceDensityBounds ConformalDepth
  ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  commonSupportCoefficientFamily referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier referenceDensityPrincipalFrameCoefficient finiteCoreSobolevLift
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder

attribute [local instance] adjacentGainThreeHalfComplete adjacentGainHalfComplete adjacentGainNegativeHalfComplete adjacentGainHighHighComplete adjacentGainHighHalfComplete adjacentGainHalfHalfComplete adjacentGainHalfNegComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCL" => referenceSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-! ### N3 (L1): continuity patch — continuous on a closed set, input vanishing off it. -/

attribute [local irreducible] sphereSobolevPartialSum qradSignedWeakSelfExpression qradFourIndexWeakForm

include hg in
theorem exists_reference_commonRadius_originalPi_qrad_squaredNorm_integrals_referenceProfile
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) (hL : 0 < L) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
      (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0),
    ∃ Cst : ℝ, 0 ≤ Cst ∧
    ∀ (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2),
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ (δ A : ℝ) (p : ℕ), 0 < δ → 0 < A → 1 ≤ p →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → θ ≤ d/2 →
    ∀ F : smoothCompactFiniteSphereCore hO hD,
      (∀ y ∈ tsupport F.val, ‖y-y0‖ ≤ ρ ∧ 1 ≤ actualReferenceBeta g L q δ A p y ∧
        referenceRadius δ A p L y*(actualReferenceBeta g L q δ A p y)^2 ≤ θ ∧
        ‖fderiv ℝ (referenceRadius δ A p L) y‖ ≤ 1) →
    let u : R3 → Hi := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
    let R : R3 → ℝ := referenceRadius δ A p L
    let tt : R3 → Tpar := fun y => ((q,(y,R y)),fderiv ℝ R y)
    let Qy : R3 → Fin 3 → Fin 3 → ℝ := fun y i j =>
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let W : R3 → ℝ := fun y => qradSignedWeakSelfExpression
      (fun i => (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)).comp
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))))
      (fun i => (NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)))).comp
        (Sh q y (R y)))
      (fun i => (NMN (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)))).comp
        (Sl q y (R y)))
      (fun i k => CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt y)) q y (R y))
      (fun i k => CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))
        (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) (tt y)) q y (R y))
      (Qy y) (R y) (u y)
    -- actual first-output SECTIONS (genuine Hi lifts, globally defined, no finite output)
    ∃ r l : Fin 3 → R3 → Hi,
      (∀ i, ContDiff ℝ ∞ (r i)) ∧ (∀ i, Continuous (l i)) ∧
      (∀ i y, y ∉ tsupport F.val → r i y = 0 ∧ l i y = 0) ∧
      (∀ y ∈ tsupport F.val, ∀ i : Fin 3,
        Ihi (r i y) =
          secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (u y)) ∧
        Ihi (l i y) = PiL i (tt y) (Sh q y (R y) (u y))) ∧
      -- both genuine negative images: ORIGINAL Qrad and reverse adjoint
      (∀ y ∈ tsupport F.val,
        Jlo (R y^3 • ∑ i, ∑ j, Qy y i j •
            secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (r j y))) =
          R y^3 • ∑ i, ∑ j, Qy y i j •
            secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) (R y)
              (PiL i (tt y) (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)
                (PiH j (tt y) (u y)))) ∧
        Jlo (R y^3 • ∑ i, ∑ j, Qy y i j • PiL j (tt y) (Sh q y (R y) (l i y))) =
          R y^3 • ∑ i, ∑ j, Qy y i j •
            PiN j (tt y) (Sl q y (R y) (PiL i (tt y) (Sh q y (R y) (u y))))) ∧
      let O : R3 → SphereSobolev (0 : ℝ) := fun y => R y^3 • ∑ i, ∑ j, Qy y i j •
        Z0 (((secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)).comp
          (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)))) (r j y))
      let Aout : R3 → SphereSobolev (0 : ℝ) := fun y => R y^3 • ∑ i, ∑ j, Qy y i j •
        Z0 (((NML (smoothMultiplierLowerJets
          (commonSupportCoefficientFamily 3 (m j) (hm j) Km hKm (hmz j) (tt y)))).comp
          (Sh q y (R y))) (l i y))
      Continuous O ∧ Continuous Aout ∧ HasCompactSupport O ∧ HasCompactSupport Aout ∧
      -- on the support the two outputs are the ORIGINAL-Pi expressions
      (∀ y ∈ tsupport F.val,
        O y = R y^3 • ∑ i, ∑ j, Qy y i j •
          Z0 (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (r j y))) ∧
        Aout y = R y^3 • ∑ i, ∑ j, Qy y i j • Z0 (PiL j (tt y) (Sh q y (R y) (l i y)))) ∧
      (∀ y : R3, W y = ‖O y‖^2 - ‖Aout y‖^2) ∧
      -- SEPARATE integrability against the SAME reference density, BEFORE subtracting
      Integrable (fun y : R3 => referenceDensityFamily g L (q,y) * ‖O y‖^2) ∧
      Integrable (fun y : R3 => referenceDensityFamily g L (q,y) * ‖Aout y‖^2) ∧
      (∫ y : R3, referenceDensityFamily g L (q,y) * W y) =
        (∫ y : R3, referenceDensityFamily g L (q,y) * ‖O y‖^2) -
          ∫ y : R3, referenceDensityFamily g L (q,y) * ‖Aout y‖^2 ∧
      |(∫ y : R3, referenceDensityFamily g L (q,y) * ‖O y‖^2) -
          ∫ y : R3, referenceDensityFamily g L (q,y) * ‖Aout y‖^2| ≤
        Cst*θ*(∫ y : R3, referenceDensityFamily g L (q,y)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q δ A p y) F y) := by
  -- N1: every radius before the families / profiles / inputs
  have hRootV009 := exists_reference_commonRadius_originalPi_qrad_signed_selfRow_referenceProfile
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel hL
  rcases hRootV009 with ⟨d9,hd9,hd9ρ,m,hm,Km,hKm,hmz,Cst,hCst,h9⟩
  have hRootJoint := exists_reference_commonRadius_joint_radial_and_gained_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel Tpar
  rcases hRootJoint with ⟨dJ,hdJ,-,hJ⟩
  have hFirstFull := exists_reference_commonRadius_finite_radial_coefficient_first_output_sections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel Tpar
  rcases hFirstFull with ⟨dS,hdS,-,hFirst⟩
  let d := min d9 (min dJ dS)
  have hdDef : d = min d9 (min dJ dS) := rfl
  have hd : 0 < d := lt_min hd9 (lt_min hdJ hdS)
  have hdd9 : d ≤ d9 := min_le_left _ _
  have hddJ : d ≤ dJ := (min_le_right _ _).trans (min_le_left _ _)
  have hddS : d ≤ dS := (min_le_right _ _).trans (min_le_right _ _)
  -- N1(4): joint regularity of the actual radial coefficient maps, SAME m, compact frozen-parameter set
  have hKt : IsCompact ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod (isCompact_closedBall _ _)
  have hRootJointSel := hJ m hm Km hKm hmz _ hKt
  rcases hRootJointSel with ⟨MJ,-,hJcap,-⟩
  refine ⟨d,hd,hdd9.trans hd9ρ,m,hm,Km,hKm,hmz,Cst,hCst,?_⟩
  intro g2 hg2 q hq δ A p hδ hA hp θ hθ0 hθ1 hθd F hProf
  intro u R tt Qy W
  -- (V9) at the SAME profile and input (closed budgets follow from the strict one)
  have hθd9 : θ ≤ d9/2 := hθd.trans (by linarith)
  have hRoot9 := h9 g2 hg2 q hq δ A p hδ hA hp θ hθ0 hθ1 hθd9 F hProf
  rcases hRoot9 with ⟨-,hGerm,hPoint,hWzero,-,hBound⟩
  -- finite input: smooth, compact, ONE cut
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  rcases hRep with ⟨hUsm,-,hUsupp,-,n,hBand⟩
  have hcut : ∀ y : R3, sphereSobolevPartialSum (3/2 : ℝ) n (u y) = u y := fun y =>
    (sphereSobolevPartialSumL_apply (3/2 : ℝ) n (u y)).symm.trans (congrFun hBand y)
  have hK : IsCompact (tsupport F.val) := F.property.2.1
  have hU0 : ∀ y : R3, y ∉ tsupport F.val → u y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hUsupp h))
  have hUc : HasCompactSupport u := HasCompactSupport.intro hK hU0
  -- N1: radius containment along the actual profile
  have hRsm : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hRpos : ∀ y : R3, 0 < R y := fun y => referenceRadius_pos δ A p L y hδ hA
  have hRθ : ∀ y ∈ tsupport F.val, |R y| ≤ θ := by
    intro y hy
    have hb : 1 ≤ actualReferenceBeta g L q δ A p y := (hProf y hy).2.1
    have hs : R y*(actualReferenceBeta g L q δ A p y)^2 ≤ θ := (hProf y hy).2.2.1
    have hb2 : 1 ≤ (actualReferenceBeta g L q δ A p y)^2 := by nlinarith
    have hR1 : R y ≤ R y*(actualReferenceBeta g L q δ A p y)^2 :=
      le_mul_of_one_le_right (hRpos y).le hb2
    rw [abs_of_pos (hRpos y)]
    linarith
  have hRd : ∀ y ∈ tsupport F.val, |R y| ≤ d := fun y hy => (hRθ y hy).trans (by linarith)
  have hRlt : ∀ y ∈ tsupport F.val, |R y| < d := fun y hy => (hRθ y hy).trans_lt (by linarith)
  have hyB : ∀ y ∈ tsupport F.val, y ∈ closedBall y0 ρ := fun y hy => by
    simpa only [mem_closedBall,dist_eq_norm] using (hProf y hy).1
  have hpJ : ∀ y ∈ tsupport F.val,
      ((q,(y,R y)) : Pphys) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dJ) dJ) :=
    fun y hy => ⟨hq,hyB y hy,abs_le.mp ((hRd y hy).trans hddJ)⟩
  have htK : ∀ y ∈ tsupport F.val, tt y ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1 := fun y hy =>
    ⟨⟨hq,hyB y hy,abs_le.mp ((hRd y hy).trans (hdd9.trans hd9ρ))⟩,
      mem_closedBall_zero_iff.mpr (hProf y hy).2.2.2⟩
  -- the actual C^∞ parameter map y ↦ ((q,(y,R y)),t(y))
  have hdR : ContDiff ℝ ∞ (fderiv ℝ R) := (contDiff_infty_iff_fderiv.mp hRsm).2
  have hPsm : ContDiff ℝ ∞ (fun y : R3 => ((q,(y,R y)) : Pphys)) :=
    contDiff_const.prodMk (contDiff_id.prodMk hRsm)
  have httsm : ContDiff ℝ ∞ tt := hPsm.prodMk hdR
  have hZsm : ContDiff ℝ ∞ (fun y : R3 => (((q,(y,R y)) : Pphys), tt y)) := hPsm.prodMk httsm
  -- N3: pointwise continuity of the actual operator families on K (coefficients frozen, then t = t(y))
  have hRHc : ∀ i : Fin 3, ∀ y ∈ tsupport F.val, ContinuousAt (fun x : R3 =>
      (secondTaylorRemainder (fun s : ℝ => RAH (q,(x,s))) (R x)).comp
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))) y := by
    intro i y hy
    exact ((hJcap i _ (hpJ y hy) (tt y) (htK y hy)).1.comp
      (f := fun x : R3 => (((q,(x,R x)) : Pphys), tt x)) y hZsm.contDiffAt).continuousAt
  have hLHc : ∀ i : Fin 3, ∀ y ∈ tsupport F.val, ContinuousAt (fun x : R3 =>
      (NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)))).comp
        (Sh q x (R x))) y := by
    intro i y hy
    exact ((hJcap i _ (hpJ y hy) (tt y) (htK y hy)).2.1.comp
      (f := fun x : R3 => (((q,(x,R x)) : Pphys), tt x)) y hZsm.contDiffAt).continuousAt
  have hInputRoom : ∀ y ∈ tsupport u, ‖y-y0‖ ≤ ρ ∧ |R y| < dS :=
    fun y hy => ⟨(hProf y (hUsupp hy)).1,(hRlt y (hUsupp hy)).trans_le hddS⟩
  have hFirstSelected := hFirst m hm Km hKm hmz q hq R hRsm tt httsm n u hUsm hUc hcut hInputRoom
  rcases hFirstSelected with ⟨rS,lS,hrSm,hlC,hFirstZero,hNativeGraphs⟩
  have hr0 : ∀ i y, y ∉ tsupport F.val → rS i y=0 :=
    fun i y hy => (hFirstZero i y (fun h => hy (hUsupp h))).1
  have hl0 : ∀ i y, y ∉ tsupport F.val → lS i y=0 :=
    fun i y hy => (hFirstZero i y (fun h => hy (hUsupp h))).2
  have hrI : ∀ i : Fin 3, ∀ y ∈ tsupport F.val,
      Ihi (rS i y) =
        secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (u y)) := by
    intro i y hy
    exact (hNativeGraphs i y).1.trans (congrArg (fun Aop : Hi →L[ℝ] Hi =>
      (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)) (Aop (u y))) (hGerm y hy i).1)
  have hlI : ∀ i : Fin 3, ∀ y ∈ tsupport F.val,
      Ihi (lS i y) = PiL i (tt y) (Sh q y (R y) (u y)) := by
    intro i y hy
    exact (hNativeGraphs i y).2.trans (congrArg (fun Aop : Half →L[ℝ] Half =>
      Aop (Sh q y (R y) (u y))) (hGerm y hy i).2.1)
  -- N5: identification with the pointwise parent witnesses through injectivity of Ihi
  have hInj : Function.Injective (Ihi) :=
    sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hWit : ∀ y ∈ tsupport F.val,
      (Jlo (R y^3 • ∑ i, ∑ j, Qy y i j •
          secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (rS j y))) =
        R y^3 • ∑ i, ∑ j, Qy y i j •
          secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) (R y)
            (PiL i (tt y) (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)
              (PiH j (tt y) (u y)))) ∧
      Jlo (R y^3 • ∑ i, ∑ j, Qy y i j • PiL j (tt y) (Sh q y (R y) (lS i y))) =
        R y^3 • ∑ i, ∑ j, Qy y i j •
          PiN j (tt y) (Sl q y (R y) (PiL i (tt y) (Sh q y (R y) (u y))))) ∧
      W y = ‖R y^3 • ∑ i, ∑ j, Qy y i j •
            Z0 (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (rS j y)))‖^2 -
          ‖R y^3 • ∑ i, ∑ j, Qy y i j • Z0 (PiL j (tt y) (Sh q y (R y) (lS i y)))‖^2 := by
    intro y hy
    have hPointY := hPoint y hy
    rcases hPointY with ⟨rL,lL,hrL,hlL,hJr,hJl,hW,-⟩
    have hrEq : rL = fun j => rS j y :=
      funext fun j => hInj ((hrL j).trans (hrI j y hy).symm)
    have hlEq : lL = fun i => lS i y :=
      funext fun i => hInj ((hlL i).trans (hlI i y hy).symm)
    subst hrEq
    subst hlEq
    exact ⟨⟨hJr,hJl⟩,hW⟩
  -- continuity of the sections (N3)
  have hrC : ∀ i, Continuous (rS i) := fun i => (hrSm i).continuous
  refine ⟨rS,lS,hrSm,hlC,fun i y hy => ⟨hr0 i y hy,hl0 i y hy⟩,
    fun y hy i => ⟨hrI i y hy,hlI i y hy⟩,fun y hy => (hWit y hy).1,?_⟩
  intro O Aout
  -- N4: the two output sections are continuous with compact support
  have hqy : Continuous (fun y : R3 => ((q,y) : ℝ × R3)) := continuous_const.prodMk continuous_id
  have hQc : ∀ i j : Fin 3, Continuous (fun y => Qy y i j) := fun i j =>
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.comp hqy
  have hOformed := continuous_compact_referenceQrad_output
    (tsupport F.val) hK R hRsm.continuous Qy hQc
    (fun i _ x => (secondTaylorRemainder (fun s : ℝ => RAH (q,(x,s))) (R x)).comp
      (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x))))
    (fun _ j => rS j) (fun i _ y hy => hRHc i y hy) (fun _ j => hrC j) (fun _ j y hy => hr0 j y hy)
  rcases hOformed with ⟨hOc,hOcpt,hOz⟩
  have hAformed := continuous_compact_referenceQrad_output
    (tsupport F.val) hK R hRsm.continuous Qy hQc
    (fun _ j x => (NML (smoothMultiplierLowerJets
      (commonSupportCoefficientFamily 3 (m j) (hm j) Km hKm (hmz j) (tt x)))).comp (Sh q x (R x)))
    (fun i _ => lS i) (fun _ j y hy => hLHc j y hy) (fun i _ => hlC i) (fun i _ y hy => hl0 i y hy)
  rcases hAformed with ⟨hAc,hAcpt,hAz⟩
  -- N4: ORIGINAL-Pi forms on K
  have hOrig : ∀ y ∈ tsupport F.val,
      O y = R y^3 • ∑ i, ∑ j, Qy y i j •
        Z0 (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (rS j y))) ∧
      Aout y = R y^3 • ∑ i, ∑ j, Qy y i j • Z0 (PiL j (tt y) (Sh q y (R y) (lS i y))) := by
    intro y hy
    constructor
    · apply referenceQrad_output_congr (R y) (Qy y)
      intro i j
      simpa only [ContinuousLinearMap.comp_apply] using
        (congrArg (fun Aop : Hi →L[ℝ] Hi =>
          (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)) (Aop (rS j y)))
            (hGerm y hy i).1)
    · apply referenceQrad_output_congr (R y) (Qy y)
      intro i j
      simpa only [ContinuousLinearMap.comp_apply] using
        (congrArg (fun Aop : Half →L[ℝ] Half => Aop (Sh q y (R y) (lS i y)))
          (hGerm y hy j).2.1)
  -- N5: the signed weak expression is the difference of the two squared norms everywhere
  have hWOA : ∀ y : R3, W y = ‖O y‖^2 - ‖Aout y‖^2 := by
    intro y
    by_cases hy : y ∈ tsupport F.val
    · have hEq := congrArg₂ (fun x z : SphereSobolev (0 : ℝ) => ‖x‖^2 - ‖z‖^2)
        (hOrig y hy).1 (hOrig y hy).2
      exact (hWit y hy).2.trans hEq.symm
    · have hEq := congrArg₂ (fun x z : SphereSobolev (0 : ℝ) => ‖x‖^2 - ‖z‖^2)
        (hOz y hy) (hAz y hy)
      have hz : ‖(0 : SphereSobolev (0 : ℝ))‖^2 - ‖(0 : SphereSobolev (0 : ℝ))‖^2 = 0 := by simp
      exact (hWzero y hy).trans ((hEq.trans hz).symm)
  -- N6: SEPARATE integrability, then subtraction of the two integrals
  have hmu : Continuous (fun y : R3 => referenceDensityFamily g L (q,y)) :=
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hIntegrals := weighted_norm_difference_integrable_of_continuous_compact
    (fun y : R3 => referenceDensityFamily g L (q,y)) hmu O Aout hOc hAc hOcpt hAcpt W hWOA
  rcases hIntegrals with ⟨hIO,hIA,hInt⟩
  refine ⟨hOc,hAc,hOcpt,hAcpt,hOrig,hWOA,hIO,hIA,hInt,?_⟩
  exact (congrArg abs hInt.symm).trans_le hBound

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
