import Calderon.NativeBoundaryCoefficientDecomposition
import Calderon.NativeSmoothMultiplierInverse
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient ENNReal
namespace OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeHalfSmoothMultiplier NativeNegativeHalfSmoothMultiplier NativeSmoothMultiplierInverse
  NativeFullSharpHalfTrace NativeHarmonicH1LiftCompletion

/-! Expanded before source in EXPANSION-native-boundary-normal-multiplier-inverse-v001.json. -/

lemma nativeNegativeHalfNormalCoefficientMulL_isInvertible
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M) :
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm).IsInvertible := by
  obtain ⟨n,N,hN,hn,hgn,hnCompact,hnSphere,hHalf,hHalf',hNeg,hNeg'⟩ :=
    exists_nativeSmoothMulL_two_sided_inverse hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm
      (boundaryNormalCoefficientData_pos F lam Lam hUE)
  exact ContinuousLinearMap.IsInvertible.of_inverse hNeg hNeg'

lemma exists_nativeBoundaryNormalMultiplier_inverse
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam) :
    ∃ (M : ℝ) (hM : 0 ≤ M)
      (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
      (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M),
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm).IsInvertible := by
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (boundaryNormalCoefficientData F)
  exact ⟨M,hM,hm,hgm,
    nativeNegativeHalfNormalCoefficientMulL_isInvertible hF hO hD τ0 F lam Lam hUE hM hm hgm⟩

lemma exists_bounded_nativeBoundaryNormalReciprocal_data
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M) :
    ∃ (n : SmoothData) (N : ℝ) (hN : 0 ≤ N)
      (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
      (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N),
      HasCompactSupport n.1 ∧
      (∀ x : UnitSphere, n.1 x.val = ((boundaryNormalCoefficientData F).1 x.val)⁻¹) ∧
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm).inverse =
        nativeNegativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn ∧
      ‖(nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm).inverse‖ ≤
        ‖nativeHalfTraceL hF hO hD τ0‖*((2*N)*‖harmonicFirstOrderLiftCompletion hF‖) := by
  obtain ⟨n,N,hN,hn,hgn,hnCompact,hnSphere,hHalf,hHalf',hNeg,hNeg'⟩ :=
    exists_nativeSmoothMulL_two_sided_inverse hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm
      (boundaryNormalCoefficientData_pos F lam Lam hUE)
  have hEq := ContinuousLinearMap.inverse_eq hNeg hNeg'
  refine ⟨n,N,hN,hn,hgn,hnCompact,hnSphere,hEq,?_⟩
  rw [hEq,norm_nativeNegativeHalfSmoothMulL_eq]
  exact norm_nativeHalfSmoothMulL_le hF hO hD τ0 n hN hn hgn

lemma inverse_nativeNegativeHalfNormalCoefficientMulL_apply
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M)
    (u : SphereSobolev (-(1/2 : ℝ))) :
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm).inverse
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgm u) = u := by
  exact (nativeNegativeHalfNormalCoefficientMulL_isInvertible hF hO hD τ0 F lam Lam hUE hM hm hgm).inverse_apply_self u

end OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse

#print axioms OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse.nativeNegativeHalfNormalCoefficientMulL_isInvertible
#print axioms OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse.exists_nativeBoundaryNormalMultiplier_inverse
#print axioms OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse.exists_bounded_nativeBoundaryNormalReciprocal_data
#print axioms OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse.inverse_nativeNegativeHalfNormalCoefficientMulL_apply
