import Calderon.HarmonicSampling
import Calderon.SpherePositiveDensity
import Mathlib.Analysis.InnerProductSpace.l2Space

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace Topology ENNReal
namespace OAI.AnisotropicCalderon.SphereHilbertDecomposition
open SphereHarmonic HarmonicSampling AngularPolynomial

lemma finiteDimensional_harmonicSphereSubspace (k : ℕ) :
    FiniteDimensional ℝ (harmonicSphereSubspace k) := by
  letI := finiteDimensional_harmonicHomogeneous k
  change FiniteDimensional ℝ ((harmonicHomogeneous k).map polynomialSphereL2)
  infer_instance

lemma completeSpace_harmonicSphereSubspace (k : ℕ) :
    CompleteSpace (harmonicSphereSubspace k) := by
  letI := finiteDimensional_harmonicSphereSubspace k
  infer_instance

lemma orthogonalFamily_harmonicSphereSubspaces (hO : OrthogonalSphereHarmonics) :
    OrthogonalFamily ℝ (fun k : ℕ => harmonicSphereSubspace k)
      (fun k => (harmonicSphereSubspace k).subtypeₗᵢ) := by
  intro i j hij u v
  exact hO i j hij u u.property v v.property

theorem isHilbertSum_harmonicSphereSubspaces (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) :
    IsHilbertSum ℝ (fun k : ℕ => harmonicSphereSubspace k)
      (fun k => (harmonicSphereSubspace k).subtypeₗᵢ) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    completeSpace_harmonicSphereSubspace
  apply IsHilbertSum.mkInternal
  · exact orthogonalFamily_harmonicSphereSubspaces hO
  · change ⊤ ≤ (⨆ k : ℕ, harmonicSphereSubspace k).topologicalClosure
    rw [hD]

def sphereHarmonicDecomposition (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) :
    SphereL2 ≃ₗᵢ[ℝ] lp (fun k : ℕ => harmonicSphereSubspace k) 2 :=
  (isHilbertSum_harmonicSphereSubspaces hO hD).linearIsometryEquiv

set_option backward.isDefEq.respectTransparency false in
theorem hasSum_sphereHarmonicDecomposition (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    HasSum (fun k : ℕ =>
      ((sphereHarmonicDecomposition hO hD u) k : SphereL2)) u := by
  simpa only [HasSum, sphereHarmonicDecomposition,
    LinearIsometryEquiv.symm_apply_apply, Finset.sum, Multiset.sum_eq_foldr,
    Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using
    (isHilbertSum_harmonicSphereSubspaces hO hD).hasSum_linearIsometryEquiv_symm
      (sphereHarmonicDecomposition hO hD u)

theorem tsum_sphereHarmonicDecomposition (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    (∑' k : ℕ, ((sphereHarmonicDecomposition hO hD u) k : SphereL2)) = u :=
  (hasSum_sphereHarmonicDecomposition hO hD u).tsum_eq

theorem norm_sq_sphereHarmonicDecomposition (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    ‖u‖ ^ 2 = ∑' k : ℕ, ‖(sphereHarmonicDecomposition hO hD u) k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (sphereHarmonicDecomposition hO hD u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    LinearIsometryEquiv.norm_map] using h

theorem inner_sphereHarmonicDecomposition (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u v : SphereL2) :
    ⟪u, v⟫_ℝ = ∑' k : ℕ,
      ⟪(sphereHarmonicDecomposition hO hD u) k,
        (sphereHarmonicDecomposition hO hD v) k⟫_ℝ := by
  rw [← (sphereHarmonicDecomposition hO hD).inner_map_map u v]
  exact lp.inner_eq_tsum _ _

theorem sphereHarmonicDecomposition_subtype (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (v : harmonicSphereSubspace k) :
    sphereHarmonicDecomposition hO hD (v : SphereL2) = lp.single 2 k v := by
  apply (sphereHarmonicDecomposition hO hD).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (IsHilbertSum.linearIsometryEquiv_symm_apply_single
    (isHilbertSum_harmonicSphereSubspaces hO hD) v).symm

theorem sphereHarmonicDecomposition_zero_mem_constants (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    ((sphereHarmonicDecomposition hO hD u) 0 : SphereL2) ∈ sphereConstantSpan := by
  rw [← harmonicSphereSubspace_zero_eq]
  exact ((sphereHarmonicDecomposition hO hD u) 0).property

theorem sphereHarmonicDecomposition_polynomial_norm_sq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    ‖(sphereHarmonicDecomposition hO hD (polynomialSphereL2 p)) k‖ ^ 2 =
      normalizedFischerSquare k p := by
  have h := sphereHarmonicDecomposition_subtype hO hD k
    ⟨polynomialSphereL2 p, polynomialSphereL2_mem k p hp⟩
  rw [h]
  simpa using polynomialSphereL2_norm_sq hF k p hp

end OAI.AnisotropicCalderon.SphereHilbertDecomposition
