import Calderon.NativeHalfSmoothMultiplier
import Calderon.SphereSobolevPairingInclusion
import Calderon.SphereContinuousScalarMultiplierSymmetry
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeNegativeHalfSmoothMultiplier
open EnergyBridge DirichletFamily SphereHarmonic SpectralCoreRegularity NativeHalfSmoothMultiplier

def nativeNegativeHalfSmoothMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  ContinuousLinearMap.adjoint (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg)

theorem sphereSobolevDualPairing_nativeNegativeHalfSmoothMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : SphereSobolev (-(1/2 : ℝ))) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) v =
    sphereSobolevDualPairing (-(1/2 : ℝ)) u
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg v) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg) v u

theorem norm_nativeNegativeHalfSmoothMulL_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    ‖nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg‖ =
      ‖nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg‖ := by
  exact ContinuousLinearMap.adjoint.norm_map _

theorem sphereSobolevDualPairing_inclusion_nativeHalfSmoothMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u)) v =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg v) := by
  rw [sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num)
    (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) v,
    sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) u
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg v)]
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let C := sphereContinuousScalarMulL (smoothSphereValue m)
  let A := nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  have hA (w : SphereSobolev (1/2 : ℝ)) : I (A w) = Z (C (Z.symm (I w))) :=
    sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg w
  change ⟪I (A u),I v⟫_ℝ = ⟪I u,I (A v)⟫_ℝ
  calc
    ⟪I (A u),I v⟫_ℝ = ⟪C (Z.symm (I u)),Z.symm (I v)⟫_ℝ := by
      rw [hA u]
      exact Z.inner_map_eq_flip _ _
    _ = ⟪Z.symm (I u),C (Z.symm (I v))⟫_ℝ :=
      inner_sphereContinuousScalarMulL_left (smoothSphereValue m) _ _
    _ = ⟪I u,I (A v)⟫_ℝ := by
      have hTransport (x y : SphereL2) :
          ⟪Z x,Z y⟫_ℝ = ⟪x,y⟫_ℝ := Z.inner_map_map x y
      have hLeft : Z (Z.symm (I u)) = I u := Z.apply_symm_apply (I u)
      have hRight : Z (C (Z.symm (I v))) = I (A v) := (hA v).symm
      calc
        ⟪Z.symm (I u),C (Z.symm (I v))⟫_ℝ =
            ⟪Z (Z.symm (I u)),Z (C (Z.symm (I v)))⟫_ℝ :=
          (hTransport (Z.symm (I u)) (C (Z.symm (I v)))).symm
        _ = ⟪I u,Z (C (Z.symm (I v)))⟫_ℝ :=
          congrArg (fun x : SphereSobolev 0 => ⟪x,Z (C (Z.symm (I v)))⟫_ℝ) hLeft
        _ = ⟪I u,I (A v)⟫_ℝ :=
          congrArg (fun y : SphereSobolev 0 => ⟪I u,y⟫_ℝ) hRight

theorem nativeNegativeHalfSmoothMulL_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : SphereSobolev (1/2 : ℝ)) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) := by
  apply ext_inner_right ℝ
  intro v
  change sphereSobolevDualPairing (-(1/2 : ℝ))
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) v =
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u)) v
  rw [sphereSobolevDualPairing_nativeNegativeHalfSmoothMulL]
  exact (sphereSobolevDualPairing_inclusion_nativeHalfSmoothMulL
    hF hO hD τ0 m hM hm hg u v).symm

theorem nativeNegativeHalfSmoothMulL_eq_of_sphereValue_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m n : SmoothData) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
    (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N)
    (hSphere : smoothSphereValue m = smoothSphereValue n) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm =
      nativeNegativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn := by
  have hPositive : nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm =
      nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn :=
    nativeHalfSmoothMulL_eq_of_sphereValue_eq hF hO hD τ0 m n hM hN hm hgm hn hgn hSphere
  exact congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      ContinuousLinearMap.adjoint A) hPositive

end OAI.AnisotropicCalderon.NativeNegativeHalfSmoothMultiplier
