import Calderon.ActualFiniteHarmonicModelConnectionSymmetric

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity ActualReferenceDDSpectralTransport
  ActualNormalizedSphereRotation SmoothSphereRotationProjection ActualReferenceParallelRaising MovingFrameConnection
  BoundedAngularShift
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma normalizedRotation_adjoint_eq_neg (i j : Fin 3) :
    ContinuousLinearMap.adjoint (normalizedRotation hO hD i j) = -normalizedRotation hO hD i j := by
  have hs (u v : SphereL2) :
      ⟪normalizedRotation hO hD i j u,v⟫_ℝ = -⟪u,normalizedRotation hO hD i j v⟫_ℝ := by
    rw [inner_sphereHarmonicDecomposition hO hD (normalizedRotation hO hD i j u) v,
      inner_sphereHarmonicDecomposition hO hD u (normalizedRotation hO hD i j v),← tsum_neg]
    apply tsum_congr
    intro k
    change ⟪sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD i j u),
        sphereHarmonicCoordinate hO hD k v⟫_ℝ =
      -⟪sphereHarmonicCoordinate hO hD k u,
        sphereHarmonicCoordinate hO hD k (normalizedRotation hO hD i j v)⟫_ℝ
    rw [normalizedRotation_coordinate hO hD i j u k,
      normalizedRotation_coordinate hO hD i j v k]
    rw [_root_.real_inner_smul_left (F := harmonicSphereSubspace k)
      (harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k u))
      (sphereHarmonicCoordinate hO hD k v) (inverseDegreeWeight k),
      _root_.real_inner_smul_right (F := harmonicSphereSubspace k)
      (sphereHarmonicCoordinate hO hD k u)
      (harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k v)) (inverseDegreeWeight k)]
    simpa only [mul_neg] using
      congrArg (fun t : ℝ => inverseDegreeWeight k*t)
        (inner_harmonicSphereRotation_skew k i j
          (sphereHarmonicCoordinate hO hD k u) (sphereHarmonicCoordinate hO hD k v))
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.neg_apply,inner_neg_left]
  linarith only [hs u v]

lemma normalizedReferenceAngularConnection_adjoint_eq_neg
    (g : MatrixField) (L lam : ℝ) (x X : R3) :
    ContinuousLinearMap.adjoint (normalizedReferenceAngularConnection hO hD g L lam x X) =
      -normalizedReferenceAngularConnection hO hD g L lam x X := by
  have hAdScalar (r : ℝ) (T : SphereL2 →L[ℝ] SphereL2) :
      ContinuousLinearMap.adjoint (r • T)=r • ContinuousLinearMap.adjoint T := by
    simpa only [starRingEnd_apply,star_trivial] using
      map_smulₛₗ (ContinuousLinearMap.adjoint :
        (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ⋆[ℝ] (SphereL2 →L[ℝ] SphereL2)) r T
  have hAdSum (T : Fin 3 → (SphereL2 →L[ℝ] SphereL2)) :
      ContinuousLinearMap.adjoint (∑ c : Fin 3, T c)=∑ c : Fin 3, ContinuousLinearMap.adjoint (T c) := by
    let Ad : (SphereL2 →L[ℝ] SphereL2) →+ (SphereL2 →L[ℝ] SphereL2) :=
      (ContinuousLinearMap.adjoint :
        (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ⋆[ℝ] (SphereL2 →L[ℝ] SphereL2)).toLinearEquiv.toLinearMap.toAddMonoidHom
    change Ad (∑ c : Fin 3, T c)=∑ c : Fin 3, Ad (T c)
    exact map_sum Ad T Finset.univ
  unfold normalizedReferenceAngularConnection
  rw [hAdScalar,hAdSum]
  simp only [hAdSum,hAdScalar,normalizedRotation_adjoint_eq_neg hO hD,
    smul_neg,Finset.sum_neg_distrib]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
