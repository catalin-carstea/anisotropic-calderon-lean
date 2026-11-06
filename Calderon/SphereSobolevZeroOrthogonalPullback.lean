import Calderon.SphereSobolevOrthogonalPullback

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open OrthogonalSphereMeasure SpectralCoreRegularity

/-! Expanded before source in EXPANSION-native-orthogonal-zero-half-trace-v001.json.
Harmonic projection covariance is derived from the actual unitary pullback. -/

lemma sphereL2OrthogonalPullback_symm_apply (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereL2) :
    sphereL2OrthogonalPullback e.symm (sphereL2OrthogonalPullback e u) = u := by
  apply Lp.ext
  have hIn := Lp.coeFn_compMeasurePreserving u
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)
  have hOut := Lp.coeFn_compMeasurePreserving (sphereL2OrthogonalPullback e u)
    (orthogonalSphereHomeomorph_sphereProbability_preserving e.symm)
  have hInComp := (orthogonalSphereHomeomorph_sphereProbability_preserving e.symm).quasiMeasurePreserving.ae_eq_comp hIn
  filter_upwards [hOut,hInComp] with «ω» h1 h2
  calc
    _ = sphereL2OrthogonalPullback e u (orthogonalSphereHomeomorph e.symm «ω») := h1
    _ = u (orthogonalSphereHomeomorph e (orthogonalSphereHomeomorph e.symm «ω»)) := h2
    _ = u «ω» := by
      apply congrArg u
      apply Subtype.ext
      exact e.apply_symm_apply «ω».val

lemma inner_sphereL2OrthogonalPullback_left (e : R3 ≃ₗᵢ[ℝ] R3) (u v : SphereL2) :
    ⟪sphereL2OrthogonalPullback e u,v⟫_ℝ = ⟪u,sphereL2OrthogonalPullback e.symm v⟫_ℝ := by
  have hv : sphereL2OrthogonalPullback e (sphereL2OrthogonalPullback e.symm v) = v := by
    simpa only [LinearIsometryEquiv.symm_symm] using sphereL2OrthogonalPullback_symm_apply e.symm v
  calc
    _ = ⟪sphereL2OrthogonalPullback e u,
      sphereL2OrthogonalPullback e (sphereL2OrthogonalPullback e.symm v)⟫_ℝ :=
        congrArg (fun w : SphereL2 => ⟪sphereL2OrthogonalPullback e u,w⟫_ℝ) hv.symm
    _ = _ := (sphereL2OrthogonalPullback e).inner_map_map _ _

lemma sphereHarmonicCoordinate_orthogonalPullback
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (u : SphereL2) :
    sphereHarmonicCoordinate hO hD k (sphereL2OrthogonalPullback e u) =
      harmonicSphereOrthogonalPullback e k (sphereHarmonicCoordinate hO hD k u) := by
  apply ext_inner_right ℝ
  intro v
  have hRight : ⟪harmonicSphereOrthogonalPullback e k (sphereHarmonicCoordinate hO hD k u),v⟫_ℝ =
      ⟪sphereHarmonicCoordinate hO hD k u,harmonicSphereOrthogonalPullback e.symm k v⟫_ℝ :=
    inner_sphereL2OrthogonalPullback_left e (sphereHarmonicCoordinate hO hD k u).val v.val
  calc
    _ = ⟪sphereL2OrthogonalPullback e u,v.val⟫_ℝ := SmoothAngularCasimir.sphereHarmonicCoordinate_inner hO hD k _ v
    _ = ⟪u,sphereL2OrthogonalPullback e.symm v.val⟫_ℝ := inner_sphereL2OrthogonalPullback_left e u v.val
    _ = ⟪sphereHarmonicCoordinate hO hD k u,harmonicSphereOrthogonalPullback e.symm k v⟫_ℝ :=
      (SmoothAngularCasimir.sphereHarmonicCoordinate_inner hO hD k u (harmonicSphereOrthogonalPullback e.symm k v)).symm
    _ = _ := hRight.symm

lemma sphereSobolevZeroEquiv_orthogonalPullback
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereL2) :
    sphereSobolevZeroEquiv hO hD (sphereL2OrthogonalPullback e u) =
      sphereSobolevOrthogonalPullbackL 0 e (sphereSobolevZeroEquiv hO hD u) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_zeroEquiv,sphereHarmonicCoordinate_orthogonalPullback,
    sphereSobolevCoefficientL_orthogonalPullback,sphereSobolevCoefficientL_zeroEquiv]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_symm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.inner_sphereL2OrthogonalPullback_left
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereHarmonicCoordinate_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevZeroEquiv_orthogonalPullback
