import Calderon.NativeNegativeHalfSmoothMultiplier
import Calderon.SphereContinuousScalarMultiplierProduct
import Calderon.SmoothSphereReciprocal

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeSmoothMultiplierInverse
open EnergyBridge DirichletFamily SphereHarmonic SpectralCoreRegularity
  NativeHalfSmoothMultiplier NativeNegativeHalfSmoothMultiplier

theorem nativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m n : SmoothData) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
    (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N)
    (hmn : ∀ x : UnitSphere, m.1 x.1 * n.1 x.1 = 1) :
    (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm).comp
      (nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn) =
    ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm
    (nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn f) = f
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  rw [sphereSobolevInclusionL_nativeHalfSmoothMulL,
    sphereSobolevInclusionL_nativeHalfSmoothMulL,LinearIsometryEquiv.symm_apply_apply]
  have hL2 := sphereContinuousScalarMulL_comp_eq_id_of_mul_eq_one
    (smoothSphereValue m) (smoothSphereValue n) hmn
  have h := congrArg (fun L : SphereL2 →L[ℝ] SphereL2 =>
    L ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f))) hL2
  change sphereContinuousScalarMulL (smoothSphereValue m)
    (sphereContinuousScalarMulL (smoothSphereValue n)
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f))) = _ at h
  rw [h,ContinuousLinearMap.id_apply,LinearIsometryEquiv.apply_symm_apply]

theorem nativeNegativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m n : SmoothData) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
    (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N)
    (hmn : ∀ x : UnitSphere, m.1 x.1 * n.1 x.1 = 1) :
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm).comp
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn) =
    ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) := by
  have hnm : ∀ x : UnitSphere, n.1 x.1 * m.1 x.1 = 1 := by
    intro x
    rw [mul_comm]
    exact hmn x
  have h := nativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
    hF hO hD τ0 n m hN hM hn hgn hm hgm hnm
  have hAdj := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
      ContinuousLinearMap.adjoint A) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hAdj
  exact hAdj

theorem exists_nativeSmoothMulL_two_sided_inverse
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hpos : ∀ x : UnitSphere, 0 < m.1 x.1) :
    ∃ (n : SmoothData) (N : ℝ) (hN : 0 ≤ N)
      (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
      (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N),
      HasCompactSupport n.1 ∧
      (∀ x : UnitSphere, n.1 x.1 = (m.1 x.1)⁻¹) ∧
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm).comp
        (nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn) =
        ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
      (nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn).comp
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm) =
        ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) ∧
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm).comp
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn) =
        ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) ∧
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn).comp
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm) =
        ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) := by
  obtain ⟨n,N,hnCompact,hN,hnSphere,hn,hgn⟩ :=
    exists_bounded_smoothData_sphere_reciprocal m hpos
  have hmn : ∀ x : UnitSphere, m.1 x.1 * n.1 x.1 = 1 := by
    intro x
    rw [hnSphere x,mul_inv_cancel₀ (hpos x).ne']
  have hnm : ∀ x : UnitSphere, n.1 x.1 * m.1 x.1 = 1 := by
    intro x
    rw [mul_comm]
    exact hmn x
  exact ⟨n,N,hN,hn,hgn,hnCompact,hnSphere,
    nativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
      hF hO hD τ0 m n hM hN hm hgm hn hgn hmn,
    nativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
      hF hO hD τ0 n m hN hM hn hgn hm hgm hnm,
    nativeNegativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
      hF hO hD τ0 m n hM hN hm hgm hn hgn hmn,
    nativeNegativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one
      hF hO hD τ0 n m hN hM hn hgn hm hgm hnm⟩

end OAI.AnisotropicCalderon.NativeSmoothMultiplierInverse
