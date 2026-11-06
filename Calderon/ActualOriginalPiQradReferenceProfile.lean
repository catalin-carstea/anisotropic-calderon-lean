import Calderon.ActualQradFixedInputSignedSelfRow
import Calderon.ActualQradSignedSelfRow
import Calderon.ActualQradReferenceProfileEnergy
import Calderon.ActualPiNativeOperatorGerms
import Calderon.ActualDensityPrincipalFrameCoefficientBound
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.ActualMixedDensityScalarZeroFactorSmoothness

/-! Original-Pi / SAME reference-profile Qrad signed self row (author-only successor, v009).
Complete expansion: output/MATHEMATICS.md, written before these declarations.
Imports the proposed parent `Calderon.ActualQradSignedSelfRow` (Root partition of v008) and
Root's profile helper `Calderon.ActualQradReferenceProfileEnergy`; no parent/helper is redone.
No compiler was run; no acceptance is claimed. -/
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
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  commonSupportCoefficientFamily referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier referenceDensityPrincipalFrameCoefficient finiteCoreSobolevLift

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

/-! ### M6 algebra: the signed weak self expression vanishes at the zero input. -/

lemma qradSignedWeakSelfExpression_zero
    (RH LH : Fin 3 → Hi →L[ℝ] Half) (LL : Fin 3 → Half →L[ℝ] Neg)
    (CHf : Fin 3 → Fin 3 → Hi →L[ℝ] Half) (CLf : Fin 3 → Fin 3 → Half →L[ℝ] Neg)
    (Q : Fin 3 → Fin 3 → ℝ) (r : ℝ) :
    qradSignedWeakSelfExpression RH LH LL CHf CLf Q r 0 = 0 := by
  have hW : ∀ i j k l : Fin 3, qradFourIndexWeakForm RH LH LL CHf CLf i j k l 0 = 0 := by
    intro i j k l
    simp [qradFourIndexWeakForm, sphereSobolevDualPairing]
  simp only [qradSignedWeakSelfExpression, hW, mul_zero, Finset.sum_const_zero]

/-! ### M1–M7 Actual original-Pi Qrad signed self row against the SAME reference density. -/

attribute [local irreducible] sphereSobolevPartialSum qradSignedWeakSelfExpression qradFourIndexWeakForm

include hg in
theorem exists_reference_commonRadius_originalPi_qrad_signed_selfRow_referenceProfile
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
    -- ONE finite cut for all y (original finite INPUT, no finite output assumed)
    (∃ n : ℕ, ∀ y : R3, sphereSobolevPartialSum (3/2 : ℝ) n (u y) = u y) ∧
    -- native multipliers are the ORIGINAL Pi_i at all three endpoints along the profile
    (∀ y ∈ tsupport F.val, ∀ i : Fin 3,
      NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) = PiH i (tt y) ∧
      NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiL i (tt y) ∧
      NMN (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiN i (tt y)) ∧
    -- pointwise: genuine lifts, ORIGINAL Qrad and reverse adjoint, signed identity, uniform bound
    (∀ y ∈ tsupport F.val, ∃ rL lL : Fin 3 → Hi,
      (∀ i, Ihi (rL i) =
        secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (u y))) ∧
      (∀ i, Ihi (lL i) = PiL i (tt y) (Sh q y (R y) (u y))) ∧
      Jlo (R y^3 • ∑ i, ∑ j, Qy y i j •
          secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (rL j))) =
        R y^3 • ∑ i, ∑ j, Qy y i j •
          secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) (R y)
            (PiL i (tt y) (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y)
              (PiH j (tt y) (u y)))) ∧
      Jlo (R y^3 • ∑ i, ∑ j, Qy y i j • PiL j (tt y) (Sh q y (R y) (lL i))) =
        R y^3 • ∑ i, ∑ j, Qy y i j •
          PiN j (tt y) (Sl q y (R y) (PiL i (tt y) (Sh q y (R y) (u y)))) ∧
      W y = ‖R y^3 • ∑ i, ∑ j, Qy y i j •
            Z0 (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y) (PiH i (tt y) (rL j)))‖^2 -
          ‖R y^3 • ∑ i, ∑ j, Qy y i j • Z0 (PiL j (tt y) (Sh q y (R y) (lL i)))‖^2 ∧
      |W y| ≤ Cst * R y^6 * ‖u y‖^2) ∧
    (∀ y : R3, y ∉ tsupport F.val → W y = 0) ∧
    -- SAME reference density, integrability BEFORE the integral, EXACT reference energy
    Integrable (fun y : R3 => referenceDensityFamily g L (q,y)*W y) ∧
    |∫ y : R3, referenceDensityFamily g L (q,y)*W y| ≤
      Cst*θ*(∫ y : R3, referenceDensityFamily g L (q,y)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q δ A p y) F y) := by
  -- M1: radii of the parents (before families), then the actual Pi germs and their room
  have hRootSelected1 := exists_reference_commonRadius_qrad_signed_selfRow_fixed_input
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel Tpar
  rcases hRootSelected1 with ⟨dS,hdS,hdSρ,hS⟩
  have hRootSelected2 := exists_reference_commonRadius_qrad_signed_selfRow_integrated
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel Tpar
  rcases hRootSelected2 with ⟨dI,hdI,-,hI⟩
  have hRootSelected3 := exists_referencePi_commonSupport_native_operator_germs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  rcases hRootSelected3 with ⟨dPi,hdPi,-,m,hm,Km,hKm,hmz,hG⟩
  let d := min dS (min dI dPi)
  have hdDef : d = min dS (min dI dPi) := rfl
  have hd : 0 < d := by rw [hdDef]; exact lt_min hdS (lt_min hdI hdPi)
  have hddS : d ≤ dS := by rw [hdDef]; exact min_le_left _ _
  have hddI : d ≤ dI := by rw [hdDef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hddPi : d ≤ dPi := by rw [hdDef]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- the exact compact Pi parameter set (same factory proof as the germ owner)
  have hKt : IsCompact ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dPi) dPi)) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1) :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod (isCompact_closedBall _ _)
  -- MQ = 3; the constant is chosen here, after m/Kt and before every profile and input
  have hRootSelected4 := hS m hm Km hKm hmz _ hKt 3 (by norm_num)
  rcases hRootSelected4 with ⟨Cst,hCst,hPt⟩
  have hRootSelected5 := hI m hm Km hKm hmz _ hKt 3 (by norm_num)
  rcases hRootSelected5 with ⟨CI,-,hIC⟩
  refine ⟨d,hd,hddS.trans hdSρ,m,hm,Km,hKm,hmz,Cst,hCst,?_⟩
  intro g2 hg2 q hq δ A p hδ hA hp θ hθ0 hθ1 hθd F hProf
  intro u R tt Qy W
  -- M4: original finite input, single cut, smooth, compact support
  have hRep := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F
  rcases hRep with ⟨hUsm,-,hUsupp,-,n,hBand⟩
  have hcut : ∀ y : R3, sphereSobolevPartialSum (3/2 : ℝ) n (u y) = u y := fun y =>
    (sphereSobolevPartialSumL_apply (3/2 : ℝ) n (u y)).symm.trans (congrFun hBand y)
  have hK : IsCompact (tsupport F.val) := F.property.2.1
  have hKmeas : MeasurableSet (tsupport F.val) := (isClosed_tsupport _).measurableSet
  -- M2: radius containment along the actual profile
  have hRsm : ContDiff ℝ ∞ R :=
    ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δ A p L hδ hA
  have hRpos : ∀ y : R3, 0 < R y := fun y => referenceRadius_pos δ A p L y hδ hA
  have hRd : ∀ y ∈ tsupport F.val, |R y| ≤ d := by
    intro y hy
    have hb : 1 ≤ actualReferenceBeta g L q δ A p y := (hProf y hy).2.1
    have hs : R y*(actualReferenceBeta g L q δ A p y)^2 ≤ θ := (hProf y hy).2.2.1
    have hb2 : 1 ≤ (actualReferenceBeta g L q δ A p y)^2 := by nlinarith
    have hR1 : R y ≤ R y*(actualReferenceBeta g L q δ A p y)^2 :=
      le_mul_of_one_le_right (hRpos y).le hb2
    rw [abs_of_pos (hRpos y)]
    linarith
  have hyB : ∀ y ∈ tsupport F.val, y ∈ closedBall y0 ρ := fun y hy => by
    simpa only [mem_closedBall,dist_eq_norm] using (hProf y hy).1
  have htK : ∀ y ∈ tsupport F.val, tt y ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dPi) dPi)) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1 := fun y hy =>
    ⟨⟨hq,hyB y hy,abs_le.mp ((hRd y hy).trans hddPi)⟩,
      mem_closedBall_zero_iff.mpr (hProf y hy).2.2.2⟩
  have hQ3 : ∀ y : R3, ∀ i j : Fin 3, |Qy y i j| ≤ 3 := fun y i j =>
    abs_referenceDensityPrincipalFrameCoefficient_le_three g g2 hg hg2 L q y i j
  -- M3: original Pi at all three endpoints (frozen coefficient, then t = t(y))
  have hGerm : ∀ y ∈ tsupport F.val, ∀ i : Fin 3,
      NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) = PiH i (tt y) ∧
      NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiL i (tt y) ∧
      NMN (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiN i (tt y) :=
    fun y hy i => (hG i (tt y) (htK y hy)).self_of_nhds
  -- M6: continuity inputs of the parent integrated theorem (actual smooth sections)
  have hRc : Continuous R := hRsm.continuous
  have hdRc : Continuous (fderiv ℝ R) := hRsm.continuous_fderiv (by simp)
  have hPc : Continuous (fun y : R3 => ((q,(y,R y)) : Pphys)) :=
    continuous_const.prodMk (continuous_id.prodMk hRc)
  have htc : Continuous tt := hPc.prodMk hdRc
  have hqy : Continuous (fun y : R3 => ((q,y) : ℝ × R3)) := continuous_const.prodMk continuous_id
  have hQc : ∀ i j : Fin 3, ContinuousOn (fun y => Qy y i j) (tsupport F.val) := fun i j =>
    ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.comp
      hqy).continuousOn
  have huc : ContinuousOn u (tsupport F.val) := hUsm.continuous.continuousOn
  have hIn : ∀ x ∈ tsupport F.val,
      ((q,(x,R x)) : Pphys) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dI) dI) ∧
      tt x ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dPi) dPi)) ×ˢ
        closedBall (0 : R3 →L[ℝ] ℝ) 1 ∧
      ∀ i j, |Qy x i j| ≤ 3 := fun x hx =>
    ⟨⟨hq,hyB x hx,abs_le.mp ((hRd x hx).trans hddI)⟩,htK x hx,hQ3 x⟩
  have hRootSelected6 := hIC (volume : Measure R3) (tsupport F.val) hK
    (fun y : R3 => ((q,(y,R y)) : Pphys)) tt Qy u hPc.continuousOn htc.continuousOn hQc huc hIn
  rcases hRootSelected6 with ⟨hWi0,-,-,-⟩
  have hWi : Integrable W (volume.restrict (tsupport F.val)) := hWi0
  -- M6: W vanishes off K, hence it is globally a.e.-strongly measurable
  have hWzero : ∀ y : R3, y ∉ tsupport F.val → W y = 0 := by
    intro y hy
    have hyu : y ∉ tsupport u := fun h => hy (hUsupp h)
    have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hyu
    show qradSignedWeakSelfExpression _ _ _ _ _ _ _ (u y) = 0
    rw [hu0]
    exact qradSignedWeakSelfExpression_zero _ _ _ _ _ _ _
  have hWind : (tsupport F.val).indicator W = W := by
    funext y
    by_cases hy : y ∈ tsupport F.val
    · exact Set.indicator_of_mem hy W
    · rw [Set.indicator_of_notMem hy W, hWzero y hy]
  have hWmeas : AEStronglyMeasurable W (volume : Measure R3) := by
    have h := (aestronglyMeasurable_indicator_iff hKmeas).mpr hWi.aestronglyMeasurable
    rwa [hWind] at h
  -- M5(e): the uniform pointwise r^6 bound on K
  have hBoundK : ∀ y ∈ tsupport F.val, |W y| ≤ Cst * R y^6 * ‖u y‖^2 := by
    intro y hy
    have hRootSelected7 := hPt q hq y (hProf y hy).1 (R y) ((hRd y hy).trans hddS) (tt y)
      (htK y hy) (Qy y) (hQ3 y) n (u y) (hcut y)
    rcases hRootSelected7 with ⟨rL,lL,-,-,-,-,hNorm,hAbs⟩
    exact (congrArg abs hNorm).trans_le hAbs
  -- M7: Root's SAME-density profile integration helper
  have hHelper := integrable_referenceProfile_signed_radius_six_gain hO hD g hg L q δ A p
    hL hδ hA hp (tsupport F.val) Cst θ hCst hθ0 hθ1
    (fun y hy => (hProf y hy).2.1) (fun y hy => (hProf y hy).2.2.1) F W hWmeas hWzero hBoundK
  refine ⟨⟨n,hcut⟩,hGerm,?_,hWzero,hHelper⟩
  -- M5(a–e): pointwise original-Pi identification
  intro y hy
  have hRootSelected8 := hPt q hq y (hProf y hy).1 (R y) ((hRd y hy).trans hddS) (tt y)
    (htK y hy) (Qy y) (hQ3 y) n (u y) (hcut y)
  rcases hRootSelected8 with ⟨rL,lL,hr',hl',hQr,hQa,hNorm,hAbs⟩
  have hGH : ∀ i : Fin 3,
      NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) = PiH i (tt y) :=
    fun i => (hGerm y hy i).1
  have hGL : ∀ i : Fin 3, NML (smoothMultiplierLowerJets
      (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiL i (tt y) :=
    fun i => (hGerm y hy i).2.1
  have hGN : ∀ i : Fin 3, NMN (smoothMultiplierLowerJets
      (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) = PiN i (tt y) :=
    fun i => (hGerm y hy i).2.2
  refine ⟨rL,lL,?_,?_,?_,?_,?_,?_⟩
  · simpa only [ContinuousLinearMap.comp_apply, hGH] using hr'
  · simpa only [ContinuousLinearMap.comp_apply, hGL] using hl'
  · simpa only [ContinuousLinearMap.comp_apply, hGH, hGL] using hQr
  · simpa only [ContinuousLinearMap.comp_apply, hGL, hGN] using hQa
  · refine hNorm.trans ?_
    simp only [ContinuousLinearMap.comp_apply, hGH, hGL]
  · exact (congrArg abs hNorm).trans_le hAbs

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
