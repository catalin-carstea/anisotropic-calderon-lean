import Calderon.ActualFullEGainedBandGraph

/-! Source-only Sol author candidate. Full upfront: full-finite-assembly-before-v001.
All maps below use the actual retained coefficient germs. This file assembles the
literal full E/E HIGH graph, smooth paired LOW endpoint, and finite joint
jet caps. The new
ordinary reverse adapters are a declared unqualified dependency; no analytic
callback is added. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

@[instance_reducible] private def fullHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighNormed
@[instance_reducible] private def fullHighSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] fullHighSpace
@[instance_reducible] private def fullLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowNormed
@[instance_reducible] private def fullLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] fullLowSpace
@[instance_reducible] private def fullNegativeNormed : NormedAddCommGroup (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeNormed
@[instance_reducible] private def fullNegativeSpace : NormedSpace ℝ (Hi →L[ℝ] Neg) := inferInstance
attribute [local instance] fullNegativeSpace

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
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

theorem complementaryZeroRow_contDiffOn
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : Tpar =>
      (sh i t+hh i t.1).comp (ZH j t.1)-(ZL j t.1).comp (sh i t+hh i t.1)) (ParamRoom δ) := by
  let NJ3 := referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
  let NJ2 := referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
  let NH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
  let NL := nativeHalfCoefficientMulL hcalc hF hO hD τ0
  have hPiL : ContDiffOn ℝ ∞ (PiL i) (ParamRoom δ) := by
    have hNative : ContDiff ℝ ∞ (fun t => NL (smoothMultiplierLowerJets
        (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t))) := by
      simpa only [piJets,smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
    intro t ht
    exact (hNative.contDiffAt.congr_of_eventuallyEq
      ((W.piGerm i t ⟨hSub ht.1,ht.2⟩).mono (fun z hz => hz.2.1.symm))).contDiffWithinAt
  have hNH (k m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => NH (NJ3 k m t.1)) (ParamRoom δ) := by
    have hNative := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar k m) (W.jacobiSmooth k m) (W.jacobiSupport k m)
      (W.jacobiCompact k m) (W.jacobiZero k m)
    intro t ht
    have hActual := hNative.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm k m t.1 (hSub ht.1)).mono (fun z hz => hz.1.symm))
    exact (hActual.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hNL (k m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar => NL (NJ2 k m t.1)) (ParamRoom δ) := by
    have hNative : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets
        (jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W k m p))) := by
      simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar k m) (W.jacobiSmooth k m) (W.jacobiSupport k m)
          (W.jacobiCompact k m) (W.jacobiZero k m)
    intro t ht
    have hActual := hNative.contDiffAt.congr_of_eventuallyEq
      ((W.jacobiGerm k m t.1 (hSub ht.1)).mono (fun z hz => hz.2.1.symm))
    exact (hActual.comp (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hSh : ContDiffOn ℝ ∞ (fun t : Tpar =>
      sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData t.1) (ParamRoom δ) := by
    intro t ht
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    exact ((contDiffAt_actualAngularRadialRemainder_families_of_segment hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg).2.2.1.comp
        (f := (Prod.fst : Tpar → Pphys)) t contDiffAt_fst).contDiffWithinAt
  have hK : ContDiffOn ℝ ∞ (fun t : Tpar => sh i t+hh i t.1) (ParamRoom δ) := by
    unfold originalRadialReverseHigh jacobiAngularReverseHigh
    exact (hPiL.clm_comp hSh).add (ContDiffOn.sum (fun m _ => (hNL i m).clm_comp contDiffOn_const))
  have hProj : ContDiff ℝ ∞ (fun t : Tpar => (t.1.1,t.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L t.1.1 t.1.2.1)) (ParamRoom δ) :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffOn
  have hr : ContDiffOn ℝ ∞ (fun t : Tpar => t.1.2.2) (ParamRoom δ) := contDiff_fst.snd.snd.contDiffOn
  have hZH : ContDiffOn ℝ ∞ (fun t : Tpar => ZH j t.1) (ParamRoom δ) := by
    unfold zeroCorrectionHigh
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (3/2 : ℝ)).clm_comp
        (contDiffOn_const.clm_comp (hNH j m))))
  have hZL : ContDiffOn ℝ ∞ (fun t : Tpar => ZL j t.1) (ParamRoom δ) := by
    unfold zeroCorrectionHalf
    exact hr.smul (ContDiffOn.sum (fun m _ => (hDr (1/2 : ℝ)).clm_comp
        (contDiffOn_const.clm_comp (hNL j m))))
  exact (hK.clm_comp hZH).sub (hZL.clm_comp hK)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
