import Calderon.NativeH2RotationTrace
import Calderon.SphereSobolevTangentialDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap NativeFullSharpHalfTrace
  SpectralCoreRegularity

/-! Expansion: EXPANSION-native-H2-tangential-trace-v001.md, obligation E. -/

theorem sphereCoordinateMulL_commute_apply (i j : Fin 3) (u : SphereL2) :
    sphereCoordinateMulL i (sphereCoordinateMulL j u) =
      sphereCoordinateMulL j (sphereCoordinateMulL i u) := by
  apply Lp.ext
  filter_upwards [sphereCoordinateMul_value_ae i (sphereCoordinateMulL j u),
    sphereCoordinateMul_value_ae j (sphereCoordinateMulL i u),
    sphereCoordinateMul_value_ae i u,sphereCoordinateMul_value_ae j u] with x hij hji hi hj
  change sphereCoordinateMul i (sphereCoordinateMulL j u) x =
    sphereCoordinateMul j (sphereCoordinateMulL i u) x
  rw [hij,hji]
  change sphereCoordinate i x * sphereCoordinateMul j u x =
    sphereCoordinate j x * sphereCoordinateMul i u x
  rw [hi,hj]
  ring

theorem sum_sphereCoordinateMulL_sq_apply (u : SphereL2) :
    (∑ j : Fin 3, sphereCoordinateMulL j (sphereCoordinateMulL j u)) = u := by
  have hout : ∀ᵐ x ∂sphereProbability, ∀ j : Fin 3,
      sphereCoordinateMul j (sphereCoordinateMulL j u) x =
        sphereCoordinate j x * sphereCoordinateMul j u x :=
    ae_all_iff.mpr (fun j => sphereCoordinateMul_value_ae j (sphereCoordinateMulL j u))
  have hin : ∀ᵐ x ∂sphereProbability, ∀ j : Fin 3,
      sphereCoordinateMul j u x = sphereCoordinate j x * u x :=
    ae_all_iff.mpr (fun j => sphereCoordinateMul_value_ae j u)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun j : Fin 3 => sphereCoordinateMulL j (sphereCoordinateMulL j u)),hout,hin]
    with x hsum ho hi
  rw [hsum]
  change (∑ j : Fin 3, sphereCoordinateMul j (sphereCoordinateMulL j u) x) = u x
  simp_rw [ho,hi]
  change (∑ j : Fin 3, x.val j * (x.val j * u x)) = u x
  have hterm (j : Fin 3) : x.val j * (x.val j * u x) = (x.val j)^2 * u x := by ring
  simp_rw [hterm]
  rw [← Finset.sum_mul,unitSphere_sum_sq,one_mul]

theorem nativeH2_coordinate_rotation_sum
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (U : BallSobolev 2) (i : Fin 3) :
    (∑ j : Fin 3, sphereCoordinateMulL j
      (sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
        sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U))) =
      strongCoordinateTraceL hcalc τ0 i U -
        sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U) := by
  simp_rw [map_sub]
  rw [Finset.sum_sub_distrib,sum_sphereCoordinateMulL_sq_apply]
  have hc (j : Fin 3) := sphereCoordinateMulL_commute_apply j i
    (strongCoordinateTraceL hcalc τ0 j U)
  simp_rw [hc]
  rw [← map_sum,outwardRadialTraceL_apply]
  rfl

theorem sphereTangentialDerivativeL_nativeHalfTrace_H2
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) (i : Fin 3) :
    sphereTangentialDerivativeL hF hO hD i
      (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) =
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (strongCoordinateTraceL hcalc τ0 i U -
          sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U))) := by
  let b : SphereSobolev (1/2 : ℝ) :=
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M (j : Fin 3) : SphereSobolev (-1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ) (EuclideanSpace.single j 1)
  let Q (j : Fin 3) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
    sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1)
  let R (j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevRotationL (1/2 : ℝ) j i
  let v (j : Fin 3) : SphereL2 :=
    sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
      sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U)
  have hterm (j : Fin 3) : M j (R j b) = J (Z (sphereCoordinateMulL j (v j))) := by
    have hrot : R j b = J (Z (v j)) :=
      sphereSobolevRotationL_nativeHalfTrace_H2 hcalc hF hO hD τ0 U i j
    have hinc : J (Q j (Z (v j))) = M j (J (Z (v j))) :=
      sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-1/2 : ℝ)
        (by norm_num) (EuclideanSpace.single j 1) (Z (v j))
    have hzero : Q j (Z (v j)) = Z (sphereCoordinateMulL j (v j)) :=
      (sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD
        (EuclideanSpace.single j 1) (v j)).trans
          (congrArg (fun L : SphereL2 →L[ℝ] SphereL2 => Z (L (v j)))
            (sphereLinearCoordinateMulL_single j))
    exact (congrArg (M j) hrot).trans (hinc.symm.trans (congrArg J hzero))
  have hsum : sphereTangentialDerivativeL hF hO hD i b =
      ∑ j : Fin 3, M j (R j b) := by
    change (∑ j : Fin 3, (M j).comp (R j)) b = _
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  have hmap : (∑ j : Fin 3, J (Z (sphereCoordinateMulL j (v j)))) =
      J (Z (∑ j : Fin 3, sphereCoordinateMulL j (v j))) := by
    rw [map_sum,map_sum]
  have hvalue : J (Z (∑ j : Fin 3, sphereCoordinateMulL j (v j))) =
      J (Z (strongCoordinateTraceL hcalc τ0 i U -
        sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U))) :=
    congrArg (fun w : SphereL2 => J (Z w))
      (nativeH2_coordinate_rotation_sum hcalc τ0 U i)
  exact hsum.trans ((Finset.sum_congr rfl (fun j hj => hterm j)).trans (hmap.trans hvalue))

theorem sphereSobolevCoefficientL_tangential_nativeHalfTrace_H2
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) (i : Fin 3) (k : ℕ) :
    sphereSobolevCoefficientL (-1/2 : ℝ) k
      (sphereTangentialDerivativeL hF hO hD i
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) =
      sphereHarmonicCoordinate hO hD k
        (strongCoordinateTraceL hcalc τ0 i U -
          sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0 U)) := by
  rw [sphereTangentialDerivativeL_nativeHalfTrace_H2 hcalc hF hO hD τ0 U i,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv]

end OAI.AnisotropicCalderon.SphereHarmonic
