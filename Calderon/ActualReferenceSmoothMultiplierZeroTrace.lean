import Calderon.ActualReferenceSmoothMultiplierWeakDefectEnergy
import Calderon.ActualReferenceSharpBoundaryIdentity

/-! Actual half and value traces are zero, derived from the same weak lift and multiplication graphs. No trace-kernel converse. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfSmoothMultiplier
  NativeFullSharpHalfTrace

theorem nativeHalfTraceL_contDiffSMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : BallH1) :
    nativeHalfTraceL hF hO hD τ0
      (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg u) =
      nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
        (nativeHalfTraceL hF hO hD τ0 u) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) m.1 m.2 hM hm hg
  let Mq : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let Cq : SphereL2 →L[ℝ] SphereL2 := sphereContinuousScalarMulL (smoothSphereValue m)
  have ht (v : BallH1) : I (T v) = Z (τ0.valueTraceL v) :=
    sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 v
  have hbulk : τ0.valueTraceL (S u) = Cq (τ0.valueTraceL u) :=
    valueTraceL_contDiffSMulL τ0 m hM hm hg u
  have hmul : I (Mq (T u)) = Z (Cq (Z.symm (I (T u)))) :=
    sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg (T u)
  have hin : Z.symm (I (T u)) = τ0.valueTraceL u :=
    (congrArg (fun v : SphereSobolev 0 => Z.symm v) (ht u)).trans
      (Z.symm_apply_apply (τ0.valueTraceL u))
  have hr : I (Mq (T u)) = Z (Cq (τ0.valueTraceL u)) :=
    hmul.trans (congrArg (fun v : SphereL2 => Z (Cq v)) hin)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  change I (T (S u)) = I (Mq (T u))
  exact (ht (S u)).trans ((congrArg Z hbulk).trans hr.symm)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem nativeHalfTraceL_referenceSmoothMultiplierWeakDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    nativeHalfTraceL hF hO hD τ0
      (referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q hM hm hg p f) = 0 := by
  change nativeHalfTraceL hF hO hD τ0
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (nativeHalfSmoothMulL hF hO hD τ0 (smoothMultiplierDatum Q) hM hm hg f) -
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (smoothMultiplierDatum Q).1 (smoothMultiplierDatum Q).2 hM hm hg
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)) = 0
  rw [map_sub, nativeHalfTraceL_referenceWeakHalfLiftFamily,
    nativeHalfTraceL_contDiffSMulL, nativeHalfTraceL_referenceWeakHalfLiftFamily, sub_self]

theorem valueTraceL_referenceSmoothMultiplierWeakDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    τ0.valueTraceL
      (referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q hM hm hg p f) = 0 := by
  apply (sphereSobolevZeroEquiv hO hD).injective
  rw [map_zero]
  have hHalf := nativeHalfTraceL_referenceSmoothMultiplierWeakDefectFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q hM hm hg p f
  have hInc := congrArg (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)) hHalf
  rw [sphereSobolevInclusionL_nativeHalfTraceL, map_zero] at hInc
  exact hInc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_contDiffSMulL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_referenceSmoothMultiplierWeakDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.valueTraceL_referenceSmoothMultiplierWeakDefectFamily
