import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.ActualReferenceSmoothMultiplierZeroTrace
import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.NativeHalfCoordinateProductTrace
import Calderon.NativeFullHalfRadialTrace

/-! The extra normal derivative
term is retained as an actual finite sum of boundary multipliers. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic MetricVolume NativeHalfSmoothMultiplier
  NativeFullSharpHalfTrace NativeFullHalfRadialTrace NativeCoefficientBoundaryMultiplier

lemma sphereContinuousScalarMulL_comm_apply (c d : C(UnitSphere, ℝ)) (u : SphereL2) :
    sphereContinuousScalarMulL c (sphereContinuousScalarMulL d u) =
      sphereContinuousScalarMulL d (sphereContinuousScalarMulL c u) := by
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae c (sphereContinuousScalarMulL d u),
    sphereContinuousScalarMul_value_ae d u,
    sphereContinuousScalarMul_value_ae d (sphereContinuousScalarMulL c u),
    sphereContinuousScalarMul_value_ae c u] with x h1 h2 h3 h4
  change sphereContinuousScalarMul c (sphereContinuousScalarMulL d u) x =
    sphereContinuousScalarMul d (sphereContinuousScalarMulL c u) x
  rw [h1,h3]
  change c x * sphereContinuousScalarMul d u x = d x * sphereContinuousScalarMul c u x
  rw [h2,h4]
  ring

lemma nativeHalfSmoothMulL_comm_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m n : SmoothData) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ K)
    (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ K)
    (f : SphereSobolev (1/2 : ℝ)) :
    nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm
      (nativeHalfSmoothMulL hF hO hD τ0 n hK hn hgn f) =
    nativeHalfSmoothMulL hF hO hD τ0 n hK hn hgn
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm f) := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  simp only [sphereSobolevInclusionL_nativeHalfSmoothMulL,
    LinearIsometryEquiv.symm_apply_apply]
  exact congrArg (sphereSobolevZeroEquiv hO hD)
    (sphereContinuousScalarMulL_comm_apply (smoothSphereValue m) (smoothSphereValue n) _)

attribute [local irreducible] nativeHalfCoefficientMulL nativeCoefficientH1ProductL

lemma nativeHalfTraceL_coefficientH1Product
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (u : BallH1) :
    nativeHalfTraceL hF hO hD τ0 (nativeCoefficientH1ProductL hcalc F u) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
        (nativeHalfTraceL hF hO hD τ0 u) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coefficientSmoothData F).1 (coefficientSmoothData F).2 hM hm hg
  let Mq := nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg
  have hp : nativeCoefficientH1ProductL hcalc F u = S u :=
    nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc F hM hm hg u
  have ht : T (S u) = Mq (T u) :=
    nativeHalfTraceL_contDiffSMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg u
  have hmMap : nativeHalfCoefficientMulL hcalc hF hO hD τ0 F = Mq :=
    nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg
  exact (congrArg T hp).trans
    (ht.trans (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      M (T u)) hmMap.symm))

lemma nativeHalfCoefficientMulL_comm_coordinate_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (i : Fin 3) (f : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F f) =
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1) f) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨K,hK,hk,hgk⟩ := exists_smooth_ball_multiplier_bound (coordinateSmoothDatum i)
  let C := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1)
  let Mq : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let Sq := nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg
  let Sc := nativeHalfSmoothMulL hF hO hD τ0 (coordinateSmoothDatum i) hK hk hgk
  have hMMap : Mq = Sq := nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg
  have hCMap : Sc = C := nativeHalfSmoothMulL_coordinate_eq hF hO hD τ0 i hK hk hgk
  have hleft : C (Mq f) = Sc (Sq f) :=
    (congrArg C (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      M f) hMMap)).trans
      (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        M (Sq f)) hCMap.symm)
  have hcomm : Sc (Sq f) = Sq (Sc f) := nativeHalfSmoothMulL_comm_apply hF hO hD τ0
    (coordinateSmoothDatum i) (coefficientSmoothData F) hK hM hk hgk hm hg f
  have hright : Sq (Sc f) = Mq (C f) :=
    (congrArg Sq (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      M f) hCMap)).trans
      (congrArg (fun M : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        M (C f)) hMMap.symm)
  exact hleft.trans (hcomm.trans hright)

def nativeHalfNormalDerivativeMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single i 1)).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierDerivativeJets Q i))

lemma nativeHalfOutwardTraceL_smooth_multiplier
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (U : BallSobolev 2) :
    nativeHalfOutwardTraceL hF hO hD hcalc τ0 (coefficientMultiplier hcalc 2 Q U) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
        (nativeHalfOutwardTraceL hF hO hD hcalc τ0 U) +
      nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) := by
  let T : BallH1 →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0
  let C : Fin 3 → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevLinearCoordinateMulL hF hO hD
    (1/2 : ℝ) (EuclideanSpace.single i 1)
  let Mq : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let Mi : Fin 3 → (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i : Fin 3 => nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (smoothMultiplierDerivativeJets Q i)
  let Nq : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0 Q
  let V : BallSobolev 2 := coefficientMultiplier hcalc 2 Q U
  let d : Fin 3 → BallH1 := fun i : Fin 3 => TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)
  let d' : Fin 3 → BallH1 := fun i : Fin 3 => TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i V)
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hterm (i : Fin 3) : C i (T (d' i)) = Mq (C i (T (d i))) + C i (Mi i (T u)) := by
    let p := nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) (d i)
    let v := nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i) u
    have hd : d' i = p+v := coordinateDerivative_H2SmoothMultiplier hcalc Q i U
    have hp : T p = Mq (T (d i)) := nativeHalfTraceL_coefficientH1Product
      hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (d i)
    have hv : T v = Mi i (T u) := nativeHalfTraceL_coefficientH1Product
      hcalc hF hO hD τ0 (smoothMultiplierDerivativeJets Q i) u
    have hcomm : C i (Mq (T (d i))) = Mq (C i (T (d i))) :=
      nativeHalfCoefficientMulL_comm_coordinate_apply hcalc hF hO hD τ0
        (smoothMultiplierLowerJets Q) i (T (d i))
    exact (congrArg (fun z : BallH1 => C i (T z)) hd).trans
      ((congrArg (C i) (T.map_add p v)).trans
        (((C i).map_add (T p) (T v)).trans
          ((congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x+y)
            (congrArg (C i) hp) (congrArg (C i) hv)).trans
              (congrArg (fun z => z+C i (Mi i (T u))) hcomm))))
  have hN : Nq (T u) = ∑ i : Fin 3, C i (Mi i (T u)) := by
    simp only [Nq,C,Mi,nativeHalfNormalDerivativeMulL,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply]
  have hsum : (∑ i : Fin 3, (Mq (C i (T (d i))) + C i (Mi i (T u)))) =
      Mq (∑ i : Fin 3, C i (T (d i))) + Nq (T u) := by
    let v : Fin 3 → SphereSobolev (1/2 : ℝ) := fun i => C i (T (d i))
    have hMapSum : Mq (∑ i : Fin 3, v i) = ∑ i : Fin 3, Mq (v i) := by
      simp only [Fin.sum_univ_three,map_add]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (fun x y : SphereSobolev (1/2 : ℝ) => x+y) hMapSum.symm hN.symm
  have hLeft : nativeHalfOutwardTraceL hF hO hD hcalc τ0 V =
      ∑ i : Fin 3, C i (T (d' i)) := nativeHalfOutwardTraceL_apply hF hO hD hcalc τ0 V
  have hRight : nativeHalfOutwardTraceL hF hO hD hcalc τ0 U =
      ∑ i : Fin 3, C i (T (d i)) := nativeHalfOutwardTraceL_apply hF hO hD hcalc τ0 U
  exact hLeft.trans ((Finset.sum_congr rfl (fun i hi => hterm i)).trans
    (hsum.trans (congrArg (fun z => Mq z+Nq (T u)) hRight.symm)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereContinuousScalarMulL_comm_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfSmoothMulL_comm_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_coefficientH1Product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfCoefficientMulL_comm_coordinate_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfNormalDerivativeMulL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfOutwardTraceL_smooth_multiplier
