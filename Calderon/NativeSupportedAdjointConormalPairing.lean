import Calderon.NativeCoefficientWeakConormalEndpoint
import Calderon.NativeSupportedAdjointWeakSolution
import Calderon.NativeCoefficientAdjointGreen
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Upfront: native-supported-adjoint-conormal-pairing-author-oct14-v001/EXPANSION-v001.json. -/

lemma energyFormH1_test_eq_of_sub_mem_zero (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (U P V : BallH1) (hDiff : P-V ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    (hWeak : ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c U (v : BallH1) = 0) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c U P =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c U V := by
  let z : BallH1Zero := ⟨P-V,hDiff⟩
  let E := TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := b) (c := c) hcoeff U
  have h0 : E (P-V) = 0 := (TauCeti.PDE.energyFormH1L_apply hcoeff U (z : BallH1)).trans (hWeak z)
  have hEq : E P = E V := by
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  exact (TauCeti.PDE.energyFormH1L_apply hcoeff U P).symm.trans
    (hEq.trans (TauCeti.PDE.energyFormH1L_apply hcoeff U V))

lemma valueTraceL_nativeWeakHalfLift (τ0 : UnitBallValueTrace)
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (hF : SphereFischerInner)
    (f : SphereSobolev (1/2:ℝ)) :
    τ0.valueTraceL (nativeWeakHalfLift a b c hcoeff hF f) =
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f) := by
  have h0 := valueTraceL_eq_zero_of_mem_w1p0 τ0 _
    (nativeWeakHalfLift_affine_difference a b c hcoeff hF f)
  rw [map_sub] at h0
  exact (sub_eq_zero.mp h0).symm

lemma nativeSupportedEnergy_adjoint_Green (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (coefficientValue 1 C) v u =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) u v +
      sphereSurfaceMass * ⟪sphereContinuousScalarMulL
        (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
        (τ0.valueTraceL u), τ0.valueTraceL v⟫_ℝ := by
  let G := nativeSupportedDriftSmoothData beta hbeta
  have hb : nativeAdjointDriftField G = beta := nativeAdjointDriftField_supported_eq beta hbeta
  have hd : nativeDriftDivergence G = nativeSupportedDriftDivergence beta :=
    nativeDriftDivergence_supported_eq beta hbeta
  have hOrig : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      (nativeAdjointDriftField G x) (coefficientValue 1 C x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    simpa only [hb] using nativeSupportedOriginalEnergyMemLp a hp C beta hbeta
  have hAdj : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)ᵀ
      (-nativeAdjointDriftField G x) (coefficientValue 1 C x-nativeDriftDivergence G x)) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    simpa only [hb,hd] using nativeSupportedAdjointEnergyMemLp a hp C beta hbeta
  have hG := energyFormH1_adjoint_Green_of_memLp τ0 a G (coefficientValue 1 C)
    hOrig hAdj u v
  have hNeg : (fun x : R3 => -beta x) = (-beta : R3 → R3) := by funext x; rfl
  simpa only [hb,hd,G,hNeg] using hG

lemma nativeNormalizedAdjointGreenPairing (sigma e d t : ℝ) (hSigma : 0 < sigma)
    (hGreen : e = d+sigma*t) : sigma⁻¹*e = sigma⁻¹*d+t := by
  rw [hGreen,mul_add,← mul_assoc,inv_mul_cancel₀ (ne_of_gt hSigma),one_mul]

attribute [local irreducible] nativeWeakHalfLift nativeWeakConormalEndpoint

lemma sphereSobolevDualPairing_nativeSupportedOriginal_eq_adjoint_add_normal
    (τ0 : UnitBallValueTrace) (a : MatrixField)
    (hp : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (hA : (nativeSupportedOriginalZeroEnergyL a hp C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (nativeWeakConormalEndpoint a beta (coefficientValue 1 C)
        (nativeSupportedOriginalEnergyMemLp a hp C beta hbeta) hF f) =
      sphereSobolevDualPairing (1/2:ℝ) f
        (nativeWeakConormalEndpoint (fun x => (a x)ᵀ) (-beta)
          (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
          (nativeSupportedAdjointEnergyMemLp a hp C beta hbeta) hF z) +
      ⟪sphereContinuousScalarMulL
        (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
        (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)),
        τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by
  let ho := nativeSupportedOriginalEnergyMemLp a hp C beta hbeta
  let ha := nativeSupportedAdjointEnergyMemLp a hp C beta hbeta
  let cAdj : R3 → ℝ := fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x
  let U : BallH1 := nativeWeakHalfLift a beta (coefficientValue 1 C) ho hF f
  let V : BallH1 := nativeWeakHalfLift (fun x => (a x)ᵀ) (-beta) cAdj ha hF z
  have hiO : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := a) (b := beta) (c := coefficientValue 1 C) ho).IsInvertible :=
    (nativeZeroCoefficientEnergyL_isInvertible_iff a beta (coefficientValue 1 C) ho).mp hA
  have hiA : (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := fun x => (a x)ᵀ) (b := -beta) (c := cAdj) ha).IsInvertible :=
    (nativeZeroCoefficientEnergyL_isInvertible_iff (fun x => (a x)ᵀ) (-beta) cAdj ha).mp
      (nativeSupportedAdjointZeroEnergyL_isInvertible τ0 a hp C beta hbeta hA)
  have hwO : ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (coefficientValue 1 C) U (v : BallH1) = 0 :=
    fun v => nativeWeakHalfLift_weak_solution a beta (coefficientValue 1 C) ho hF hiO f v
  have hwA : ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a x)ᵀ) (-beta) cAdj V (v : BallH1) = 0 :=
    fun v => nativeWeakHalfLift_weak_solution (fun x => (a x)ᵀ) (-beta) cAdj ha hF hiA z v
  have hTestO := energyFormH1_test_eq_of_sub_mem_zero a beta (coefficientValue 1 C) ho
    U (harmonicFirstOrderLiftCompletion hF z) V
    (nativeWeakHalfLift_affine_difference (fun x => (a x)ᵀ) (-beta) cAdj ha hF z) hwO
  have hTestA := energyFormH1_test_eq_of_sub_mem_zero (fun x => (a x)ᵀ) (-beta) cAdj ha
    V (harmonicFirstOrderLiftCompletion hF f) U
    (nativeWeakHalfLift_affine_difference a beta (coefficientValue 1 C) ho hF f) hwA
  have hPairO := sphereSobolevDualPairing_nativeWeakConormalEndpoint
    a beta (coefficientValue 1 C) ho hF f z
  have hPairA := sphereSobolevDualPairing_nativeWeakConormalEndpoint
    (fun x => (a x)ᵀ) (-beta) cAdj ha hF z f
  have hG := nativeSupportedEnergy_adjoint_Green τ0 a hp C beta hbeta V U
  have hN := nativeNormalizedAdjointGreenPairing sphereSurfaceMass _ _ _ (show 0 < sphereSurfaceMass from measureReal_univ_pos) hG
  have htU : τ0.valueTraceL U = τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f) :=
    valueTraceL_nativeWeakHalfLift τ0 a beta (coefficientValue 1 C) ho hF f
  have htV : τ0.valueTraceL V = τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z) :=
    valueTraceL_nativeWeakHalfLift τ0 (fun x => (a x)ᵀ) (-beta) cAdj ha hF z
  have hLeft := hPairO.trans (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hTestO)
  have hRight := hPairA.trans (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) hTestA)
  have hBoundary : ⟪sphereContinuousScalarMulL
      (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
      (τ0.valueTraceL V),τ0.valueTraceL U⟫_ℝ =
      ⟪sphereContinuousScalarMulL
        (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
        (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)),
        τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by rw [htV,htU]
  exact hLeft.trans (hN.trans (congrArg₂ (fun s t : ℝ => s+t) hRight.symm hBoundary))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_test_eq_of_sub_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.valueTraceL_nativeWeakHalfLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedEnergy_adjoint_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNormalizedAdjointGreenPairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_nativeSupportedOriginal_eq_adjoint_add_normal
