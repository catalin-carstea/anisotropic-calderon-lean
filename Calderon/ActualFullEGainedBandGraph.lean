import Calderon.ActualFullEOrdinarySmoothSelection

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

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

private lemma completeBracket_graph
    (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (RH HH sH hH EH : E →L[ℝ] F) (RL HL sL hL EL : F →L[ℝ] N)
    (ZH zH : E →L[ℝ] E) (ZL zL : F →L[ℝ] F)
    (CRR CRH CHR CHH : E →L[ℝ] F)
    (hE : ∀ u, EH u=RH u+HH u+I (ZH u))
    (hEL : ∀ v, EL v=RL v+HL v+J (ZL v))
    (hEc : ∀ u, J (EH u)=EL (I u))
    (hKc : ∀ u, J ((sH+hH) u)=(sL+hL) (I u))
    (hRR : ∀ u, J (CRR u)=sL (RH u)-RL (sH u))
    (hRH : ∀ u, J (CRH u)=sL (HH u)-HL (sH u))
    (hHR : ∀ u, J (CHR u)=hL (RH u)-RL (hH u))
    (hHH : ∀ u, J (CHH u)=hL (HH u)-HL (hH u)) (u : E) :
    J ((CRR+CRH+CHR+CHH+(zL.comp EH-EH.comp zH)+
        ((sH+hH).comp ZH-ZL.comp (sH+hH))) u) =
      sL (EH u)+hL (EH u)+J (zL (EH u))-EL (sH u+hH u+I (zH u)) := by
  let G0 := zL.comp EH-EH.comp zH
  let KZ := (sH+hH).comp ZH-ZL.comp (sH+hH)
  have hG0 : J (G0 u)=J (zL (EH u))-EL (I (zH u)) := by
    simp only [G0,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub,hEc]
  have hKZ : J (KZ u)=(sL+hL) (I (ZH u))-J (ZL ((sH+hH) u)) := by
    simp only [KZ,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub,hKc]
  change J ((CRR+CRH+CHR+CHH+G0+KZ) u) = _
  simp only [ContinuousLinearMap.add_apply,map_add,hRR,hRH,hHR,hHH,hG0,hKZ]
  simp only [hE,hEL,ContinuousLinearMap.add_apply,map_add]
  abel
end Algebra

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

private lemma kernelReverse_endpoint_compatibility (δ0 : ℝ) (W : CoeffRoom δ0)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω) (u : Hi) :
    JL ((sh i t+hh i t.1) u) = (sl i t+hl i t.1) (IH u) := by
  have hP := (W.piGerm i t ht).self_of_nhds
  have hPi (v : Half) : JL (PiL i t v)=PiN i t (JL v) := by
    have h := v017_native_half_negative hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t)) v
    simpa only [piJets,hP.2.1,hP.2.2] using h
  have hSharp := v016_actual_Sh_compat hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData t.1 hSeg u
  have hR : JL (sh i t u)=sl i t (IH u) := by
    simpa only [originalRadialReverseHigh,originalRadialReverseLow,
      ContinuousLinearMap.comp_apply] using
      (hPi _).trans (congrArg (PiN i t) hSharp.symm)
  have hH := (jacobiAngularOperator_endpoint_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    δ0 W i t.1 ht.1 u).2
  simpa only [ContinuousLinearMap.add_apply, map_add] using
    congrArg₂ (fun x y : Neg => x+y) hR hH

attribute [local irreducible] canonicalHigh canonicalLow originalRadialHigh originalRadialLow
  originalRadialReverseHigh originalRadialReverseLow jacobiAngularOperatorHigh jacobiAngularOperatorLow
  jacobiAngularReverseHigh jacobiAngularReverseLow zeroCorrectionHigh zeroCorrectionHalf
  zeroReverseHigh zeroReverseHalf sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

/-- The literal full ordered high graph once its four actual bands are selected.
This private algebra adapter is discharged by the actual room producer below. -/
theorem fullGainedHigh_graph_of_actual_bands
    (hreg : FixedDirichletRegularity)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half) (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hRR : ∀ u, JL (RR δ0 W i j t u)=sl i t (Rh j t u)-Rl j t (sh i t u))
    (hRH : ∀ u, JL (RH hreg δ0 W i j t u)=sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u))
    (hHR : ∀ u, JL (HR hreg Gcoord GN δ0 W i j t u)=hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u))
    (hHH : ∀ u, JL (HH δ0 W i j t.1 u)=hl i t.1 (Hh j t.1 u)-Hl j t.1 (hh i t.1 u)) (u : Hi) :
    JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t u) =
      orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t (EH j t u)-
        EL j t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t u) := by
  have hP := (W.piGerm j t ht).self_of_nhds
  have hEc := canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
    hP.1 hP.2.1
  have hE (v : Hi) : EH j t v=Rh j t v+Hh j t.1 v+IH (ZH j t.1 v) := by
    simp only [canonicalHigh, originalRadialHigh, jacobiAngularOperatorHigh,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have hEL (v : Half) : EL j t v=Rl j t v+Hl j t.1 v+JL (ZL j t.1 v) := by
    simp only [canonicalLow, originalRadialLow, jacobiAngularOperatorLow,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have hFull := completeBracket_graph IH JL (Rh j t) (Hh j t.1) (sh i t) (hh i t.1) (EH j t)
    (Rl j t) (Hl j t.1) (sl i t) (hl i t.1) (EL j t)
    (ZH j t.1) (zH i t.1) (ZL j t.1) (zL i t.1)
    (RR δ0 W i j t) (RH hreg δ0 W i j t) (HR hreg Gcoord GN δ0 W i j t) (HH δ0 W i j t.1)
    hE hEL hEc
    (kernelReverse_endpoint_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W i t ht hSeg)
    hRR hRH hHR hHH u
  simpa only [fullGainedHigh,zeroReverseEHigh,orderedReverseHigh,orderedReverseLow,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply] using hFull


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
