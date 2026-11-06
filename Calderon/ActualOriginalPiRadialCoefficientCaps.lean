import Calderon.ActualOriginalPiQradSquaredNormProfile
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


/-- Actual adjoint radial remainder followed by the original Pi multiplier. -/
def referenceOriginalPiAdjointRadialCoefficient (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (secondTaylorRemainder (fun s : ℝ => RAH (t.1.1,(t.1.2.1,s))) t.1.2.2).comp (PiH i t)

/-- The exact reverse-pivot coefficient of the original Pi/radial word. -/
def referenceOriginalPiSharpRadialCoefficient (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (PiL i t).comp (Sh t.1.1 t.1.2.1 t.1.2.2)


lemma referenceOriginalPi_radial_coefficient_germ_transport
    (m : Tpar × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (i : Fin 3) (t : Tpar) (M : ℝ)
    (hG : ∀ᶠ z in 𝓝 t,
      NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz z) = PiH i z ∧
      NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz z)) = PiL i z ∧
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz z)) = PiN i z)
    (hNativeR : ContDiffAt ℝ ∞ (fun z : Pphys × Tpar =>
      (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
        (NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2))) (t.1,t))
    (hNativeL : ContDiffAt ℝ ∞ (fun z : Pphys × Tpar =>
      (NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2))).comp
        (Sh z.1.1 z.1.2.1 z.1.2.2)) (t.1,t))
    (hNormR : ‖(secondTaylorRemainder (fun s : ℝ => RAH (t.1.1,(t.1.2.1,s))) t.1.2.2).comp
      (NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))‖ ≤ M)
    (hNormL : ‖(NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))).comp
      (Sh t.1.1 t.1.2.1 t.1.2.2)‖ ≤ M) :
    ContDiffAt ℝ ∞ (referenceOriginalPiAdjointRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) t ∧
    ContDiffAt ℝ ∞ (referenceOriginalPiSharpRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) t ∧
    ‖referenceOriginalPiAdjointRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t‖ ≤ M ∧
    ‖referenceOriginalPiSharpRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t‖ ≤ M := by
  let Q : Tpar → SmoothCoefficientJets 3 :=
    fun z => commonSupportCoefficientFamily 3 m hm Km hKm hmz z
  let Rn : Tpar → Hi →L[ℝ] Half := fun z =>
    (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp (NMH (Q z))
  let Ln : Tpar → Hi →L[ℝ] Half := fun z =>
    (NML (smoothMultiplierLowerJets (Q z))).comp (Sh z.1.1 z.1.2.1 z.1.2.2)
  have hDiag : ContDiffAt ℝ ∞ (fun z : Tpar => (z.1,z)) t :=
    contDiffAt_fst.prodMk contDiffAt_id
  have hRnRaw := hNativeR.comp (f := fun z : Tpar => (z.1,z)) t hDiag
  have hLnRaw := hNativeL.comp (f := fun z : Tpar => (z.1,z)) t hDiag
  have hRn : ContDiffAt ℝ ∞ Rn t := by
    simpa only [Rn,Q,Function.comp_def] using hRnRaw
  have hLn : ContDiffAt ℝ ∞ Ln t := by
    simpa only [Ln,Q,Function.comp_def] using hLnRaw
  have hREq : Rn =ᶠ[𝓝 t] referenceOriginalPiAdjointRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i := by
    filter_upwards [hG] with z hz
    exact congrArg (fun A : Hi →L[ℝ] Hi =>
      (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp A) hz.1
  have hLEq : Ln =ᶠ[𝓝 t] referenceOriginalPiSharpRadialCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i := by
    filter_upwards [hG] with z hz
    exact congrArg (fun A : Half →L[ℝ] Half => A.comp (Sh z.1.1 z.1.2.1 z.1.2.2)) hz.2.1
  have hRV := hREq.eq_of_nhds
  have hLV := hLEq.eq_of_nhds
  refine ⟨hRn.congr_of_eventuallyEq hREq.symm,hLn.congr_of_eventuallyEq hLEq.symm,?_,?_⟩
  · exact (congrArg norm hRV).symm.le.trans hNormR
  · exact (congrArg norm hLV).symm.le.trans hNormL

include Room in
theorem exists_reference_commonRadius_originalPi_radial_coefficient_caps
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ ∃ M : ℝ, 0 ≤ M ∧
    ∀ t ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ
        closedBall (0 : R3 →L[ℝ] ℝ) 1, ∀ i : Fin 3,
      ContDiffAt ℝ ∞ (referenceOriginalPiAdjointRadialCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) t ∧
      ContDiffAt ℝ ∞ (referenceOriginalPiSharpRadialCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) t ∧
      ‖referenceOriginalPiAdjointRadialCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t‖ ≤ M ∧
      ‖referenceOriginalPiSharpRadialCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t‖ ≤ M := by
  obtain ⟨dP,hdP,hdPρ,m,hm,Km,hKm,hmz,hGerm⟩ :=
    exists_referencePi_commonSupport_native_operator_germs
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨dJ,hdJ,hdJρ,hJoint⟩ :=
    exists_reference_commonRadius_joint_radial_and_gained_coefficient_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel Tpar
  let Kt : Set Tpar := (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)) ×ˢ
    closedBall (0 : R3 →L[ℝ] ℝ) 1
  have hKt : IsCompact Kt :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod
      (isCompact_closedBall _ _)
  obtain ⟨M,hM,hCaps,-⟩ := hJoint m hm Km hKm hmz Kt hKt
  let d := min dP dJ
  have hdP' : d ≤ dP := min_le_left _ _
  have hdJ' : d ≤ dJ := min_le_right _ _
  have hdρ : d ≤ ρ := hdP'.trans hdPρ
  refine ⟨d,lt_min hdP hdJ,hdρ,M,hM,?_⟩
  intro t ht i
  have htP : t ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dP) dP)) ×ˢ
      closedBall (0 : R3 →L[ℝ] ℝ) 1 :=
    ⟨⟨ht.1.1,ht.1.2.1,(neg_le_neg hdP').trans ht.1.2.2.1,ht.1.2.2.2.trans hdP'⟩,ht.2⟩
  have hpJ : t.1 ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dJ) dJ) :=
    ⟨ht.1.1,ht.1.2.1,(neg_le_neg hdJ').trans ht.1.2.2.1,ht.1.2.2.2.trans hdJ'⟩
  have htK : t ∈ Kt :=
    ⟨⟨ht.1.1,ht.1.2.1,(neg_le_neg hdρ).trans ht.1.2.2.1,ht.1.2.2.2.trans hdρ⟩,ht.2⟩
  have hc := hCaps i t.1 hpJ t htK
  exact referenceOriginalPi_radial_coefficient_germ_transport
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    (m i) (hm i) Km hKm (hmz i) i t M (hGerm i t htP)
    hc.1 hc.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOriginalPiAdjointRadialCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOriginalPiSharpRadialCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_originalPi_radial_coefficient_caps
