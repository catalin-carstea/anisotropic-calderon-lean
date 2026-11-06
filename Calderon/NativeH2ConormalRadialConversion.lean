import Calderon.NativeBoundaryCoefficientL2Decomposition
import Calderon.NativeNegativeHalfMultiplierL2Inclusion
import Calderon.NativeH2TangentialTrace

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeNegativeHalfSmoothMultiplier

/-! Expansion: EXPANSION-native-H2-conormal-radial-conversion-v001.md, step 2. -/

theorem sphereSobolevInclusionL_eq_of_target_eq (s t u : ℝ)
    (ht : t ≤ s) (hu : u ≤ s) (htu : t = u) :
    sphereSobolevInclusionL s t ht = sphereSobolevInclusionL s u hu := by
  subst u
  rfl

theorem linearMap_comp_add_finite_sum
    {U V W : Type*} [AddCommMonoid U] [Module ℝ U]
    [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W]
    {ι : Type*} (J : V →ₗ[ℝ] W) (Z : U →ₗ[ℝ] V)
    (s : Finset ι) (x : U) (y : ι → U) :
    J (Z (x + ∑ i ∈ s, y i)) = J (Z x) + ∑ i ∈ s, J (Z (y i)) := by
  rw [map_add,map_add,map_sum,map_sum]

theorem nativeH2_conormal_negativeHalf_eq_normal_add_tangent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M)
    {N : Fin 3 → ℝ} (hN : ∀ j, 0 ≤ N j)
    (ht : ∀ j, ∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ N j)
    (hgt : ∀ j, ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ N j)
    (U : BallSobolev 2) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U)) =
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hg
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U))) +
    ∑ j : Fin 3,
      nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
        (hN j) (ht j) (hgt j)
        (sphereTangentialDerivativeL hF hO hD j
          (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) := by
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let r : SphereL2 := outwardRadialTraceL hcalc τ0 U
  let v (j : Fin 3) : SphereL2 := strongCoordinateTraceL hcalc τ0 j U - sphereCoordinateMulL j r
  let b : SphereSobolev (1/2 : ℝ) :=
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)
  let C0 : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (boundaryNormalCoefficientData F))
  let Ct (j : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (boundaryTangentCoefficientData F j))
  let M0 : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hg
  let Mt (j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
      (hN j) (ht j) (hgt j)
  let S (j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereTangentialDerivativeL hF hO hD j
  have hnormal : M0 (J (Z r)) = J (Z (C0 r)) :=
    nativeNegativeHalfSmoothMulL_L2_inclusion hF hO hD τ0
      (boundaryNormalCoefficientData F) hM hm hg r
  have htangent (j : Fin 3) : Mt j (S j b) = J (Z (Ct j (v j))) := by
    have htrace : S j b = J (Z (v j)) := by
      have hchecked : S j b = sphereSobolevInclusionL 0 (-1/2 : ℝ)
          (by norm_num) (Z (v j)) :=
        sphereTangentialDerivativeL_nativeHalfTrace_H2 hcalc hF hO hD τ0 U j
      have hindex : (-1/2 : ℝ) = -(1/2 : ℝ) := by norm_num
      have hinc := sphereSobolevInclusionL_eq_of_target_eq 0 (-1/2 : ℝ) (-(1/2 : ℝ))
        (by norm_num) (by norm_num) hindex
      have happ := congrArg (fun K : SphereSobolev 0 →L[ℝ] SphereSobolev (-1/2 : ℝ) =>
        K (Z (v j))) hinc
      exact hchecked.trans happ
    have hmul : Mt j (J (Z (v j))) = J (Z (Ct j (v j))) :=
      nativeNegativeHalfSmoothMulL_L2_inclusion hF hO hD τ0
        (boundaryTangentCoefficientData F j) (hN j) (ht j) (hgt j) (v j)
    exact (congrArg (Mt j) htrace).trans hmul
  have hcoarse : ordinaryConormalTraceL hcalc τ0 F U = C0 r + ∑ j : Fin 3, Ct j (v j) :=
    ordinaryConormalTraceL_eq_normal_add_tangent hcalc τ0 F U
  have htransport := congrArg (fun z : SphereL2 => J (Z z)) hcoarse
  have hdistrib : J (Z (C0 r + ∑ j : Fin 3, Ct j (v j))) =
      J (Z (C0 r)) + ∑ j : Fin 3, J (Z (Ct j (v j))) :=
    linearMap_comp_add_finite_sum J.toLinearMap Z.toLinearEquiv.toLinearMap
      Finset.univ (C0 r) (fun j : Fin 3 => Ct j (v j))
  have hsum : (∑ j : Fin 3, J (Z (Ct j (v j)))) = ∑ j : Fin 3, Mt j (S j b) :=
    Finset.sum_congr rfl (fun j hj => (htangent j).symm)
  exact htransport.trans (hdistrib.trans
    (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x+y) hnormal.symm hsum))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
