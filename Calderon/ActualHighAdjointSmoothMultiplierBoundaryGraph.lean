import Calderon.ActualHighAdjointSmoothMultiplierBoundaryCommutator
import Calderon.ActualReferenceGaugeHighRadialAdjointDefect
import Calderon.ActualReferenceGaugeTangentDefectHighMultiplierCommutator
import Calderon.ActualReferenceGaugeNormalHighReciprocalCommutation
import Calderon.HighAdjointMultiplierEndpointAlgebra
import Calderon.SequenceLpNaturalStructureData

/-! Every endpoint graph is derived for the SAME actual operators. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceHighSmoothMultiplierBoundaryCommutatorFamily referenceGaugeNormalHighCommutatorFamily
  referenceGaugeNormalHalfCommutatorFamily referenceGaugeNormalThreeHalfMultiplierFamily
  referenceGaugeNormalHalfMultiplierFamily referenceGaugeTangentSecondHighMultiplierCommutatorFamily
  referenceGaugeTangentSecondEndpointFamily referenceAdjointThreeHalfRadialFamily referenceSharpRadialTraceFamily
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL sphereLowerDistributionalTranspose referenceWeakDirichletEnergyFamily

lemma referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily_inclusion
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ) (r : ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,(y,r)),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible)
    (hp : (q,(y,r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,r)) f) =
    referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q f) -
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
      (referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) f) := by
  let p := (q,(y,r))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let S := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Sadj := referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let BH := referenceHighSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p
  let KH := referenceGaugeNormalHighCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let KL := referenceGaugeNormalHalfCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let WH := (referenceGaugeNormalThreeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse
  let WL := (referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse
  let T2 := referenceGaugeTangentSecondEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let D := T2-sphereLowerDistributionalTranspose T2
  let CG := (2 : ℝ) • referenceGaugeTangentSecondHighMultiplierCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p
  have hI (u : SphereSobolev (3/2 : ℝ)) : I (MH u) = ML (I u) :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Z u)
      (NativeOrderOneCoefficientMultiplier.nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJ (v : SphereSobolev (1/2 : ℝ)) : J (ML v) = MN (J v) :=
    congrArg (fun Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => Z v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  have hWM (u : SphereSobolev (3/2 : ℝ)) : WH (MH u) = MH (WH u) :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) => Z u)
      (referenceGaugeNormalThreeHalfMultiplierFamily_inverse_commutes_coefficientMulL
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p Q)
  have hB (u : SphereSobolev (3/2 : ℝ)) : I (BH u) = S (MH u)-ML (S u) :=
    referenceHighSmoothMultiplierBoundaryCommutatorFamily_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel Q p lam Lam hUE hsmall hWeak u
  have hK (u : SphereSobolev (3/2 : ℝ)) : I (KH u) = KL (I u) :=
    referenceGaugeNormalHighCommutatorFamily_half_agreement
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg p lam Lam hUE hsmall hWeak u
  have hW (u : SphereSobolev (3/2 : ℝ)) : I (WH u) = WL (I u) :=
    congrArg (fun Z : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => Z u)
      (referenceGaugeNormalThreeHalfMultiplierFamily_inverse_half_inclusion
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p)
  have hDef (u : SphereSobolev (3/2 : ℝ)) :
      J (Sadj u-S u) = J (I (KH u))+r^2 • D (I (WH u)) := by
    have hLow : J (Sadj u-S u) = J (KL (I u))+r^2 • D (WL (I u)) :=
      referenceAdjointThreeHalfRadialFamily_sub_sharp_lower_defect
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel q hq y hy r hp u
    exact hLow.trans (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z)
      (congrArg J (hK u).symm) (congrArg (fun z : SphereSobolev (1/2 : ℝ) => r^2 • D z) (hW u).symm))
  have hC (u : SphereSobolev (3/2 : ℝ)) : J (I (CG u)) = D (ML (I u))-MN (D (I u)) := by
    have h := referenceGaugeTangentSecondHighMultiplierCommutatorFamily_transpose_defect_inclusion
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p u
    simpa only [CG,ContinuousLinearMap.smul_apply] using h
  have hLaw := highAdjointMultiplierCommutator_gain_of_endpoint_defect
    (X := SphereSobolev (3/2 : ℝ)) (Y := SphereSobolev (1/2 : ℝ))
    (Z := SphereSobolev (-(1/2 : ℝ)))
  try simp (config := { instances := true }) only
    [sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
      sequenceLp_normedSpace_module_eq_natural] at hLaw
  have hActual : I ((BH+KH.comp MH-MH.comp KH+r^2 • CG.comp WH) f) = Sadj (MH f)-ML (Sadj f) :=
    hLaw I J (sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))
      S Sadj MH WH KH BH CG ML MN D (r^2) hI hJ hWM hB hDef hC f
  have hFormula : referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p f =
      (BH+KH.comp MH-MH.comp KH+r^2 • CG.comp WH) f := by
    unfold referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
    rfl
  exact (congrArg I hFormula).trans hActual

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily_inclusion
