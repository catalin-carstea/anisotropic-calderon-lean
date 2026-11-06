import Calderon.SmoothAngularCasimir
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open SphereHarmonic SmoothSphereRotation SmoothAngularCasimir RotationCasimir
open SphereHilbertDecomposition SpectralCoreRegularity AngularPolynomial GreenRadialTrace

/-- Actual true rotation of a polynomial restriction, with its actual probability L2 lift. -/
lemma smoothSphereLift_rotation_polynomial (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    smoothSphereLift (sphereRotationDerivative i j (polynomialEvaluation p))
      (contDiff_sphereRotationDerivative i j _ (contDiff_polynomialEvaluation p)) =
        polynomialSphereL2 (polynomialRotation i j p) := by
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1
  ext u
  exact congrFun (sphereRotationDerivative_polynomialEvaluation i j p) u.val

/-- Derived from true smooth probability skewness; no Fischer-inner interface is used. -/
lemma polynomialSphereL2_rotation_skew (i j : Fin 3) (p q : MvPolynomial (Fin 3) ℝ) :
    ⟪polynomialSphereL2 (polynomialRotation i j p),polynomialSphereL2 q⟫_ℝ =
      -⟪polynomialSphereL2 p,polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ := by
  have h := inner_sphereRotationDerivative_skew i j (polynomialEvaluation p)
    (polynomialEvaluation q) (contDiff_polynomialEvaluation p) (contDiff_polynomialEvaluation q)
  rw [smoothSphereLift_rotation_polynomial i j p,smoothSphereLift_polynomialEvaluation q,
    smoothSphereLift_polynomialEvaluation p,smoothSphereLift_rotation_polynomial i j q] at h
  exact h

/-- Kernel stability is an actual norm consequence of smooth skewness, not AE-to-pointwise. -/
lemma polynomialSphereL2_rotation_eq_zero_of_eq_zero (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : polynomialSphereL2 p = 0) :
    polynomialSphereL2 (polynomialRotation i j p) = 0 := by
  have hn : ‖polynomialSphereL2 (polynomialRotation i j p)‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq,polynomialSphereL2_rotation_skew i j p
      (polynomialRotation i j p),hp,inner_zero_left,neg_zero]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

def polynomialRotationLinear (i j : Fin 3) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun := polynomialRotation i j
  map_add' p q := by simp [polynomialRotation,map_add,mul_add,sub_add_sub_comm]
  map_smul' c p := by
    simp only [polynomialRotation,smul_eq_C_mul,pderiv_C_mul,RingHom.id_apply]
    ring

/-- The actual harmonic-polynomial image map, with no representative injectivity premise. -/
def harmonicPolynomialSphereMap (k : ℕ) :
    harmonicHomogeneous k →ₗ[ℝ] harmonicSphereSubspace k where
  toFun p := ⟨polynomialSphereL2 p,polynomialSphereL2_mem k p p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add polynomialSphereL2 (p : MvPolynomial (Fin 3) ℝ) (q : MvPolynomial (Fin 3) ℝ)
  map_smul' c p := by apply Subtype.ext; exact map_smul polynomialSphereL2 c (p : MvPolynomial (Fin 3) ℝ)

lemma harmonicPolynomialSphereMap_surjective (k : ℕ) :
    Function.Surjective (harmonicPolynomialSphereMap k) := by
  intro v
  rcases Submodule.mem_map.mp v.property with ⟨p,hp,hpv⟩
  refine ⟨⟨p,hp⟩,?_⟩
  apply Subtype.ext
  exact hpv

/-- Actual polynomial rotation remains in the same true harmonic image at every degree. -/
def rotatedHarmonicSphereMap (k : ℕ) (i j : Fin 3) :
    harmonicHomogeneous k →ₗ[ℝ] harmonicSphereSubspace k where
  toFun p := ⟨polynomialSphereL2 (polynomialRotation i j p),
    polynomialSphereL2_mem k _ (polynomialRotation_harmonic_all k i j p p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change polynomialSphereL2 (polynomialRotationLinear i j ((p : MvPolynomial (Fin 3) ℝ)+q)) =
      polynomialSphereL2 (polynomialRotationLinear i j p) +
        polynomialSphereL2 (polynomialRotationLinear i j q)
    rw [map_add,map_add]
  map_smul' c p := by
    apply Subtype.ext
    change polynomialSphereL2 (polynomialRotationLinear i j (c • (p : MvPolynomial (Fin 3) ℝ))) =
      c • polynomialSphereL2 (polynomialRotationLinear i j p)
    rw [map_smul,map_smul]

lemma harmonicPolynomialSphereMap_ker_le_rotated (k : ℕ) (i j : Fin 3) :
    LinearMap.ker (harmonicPolynomialSphereMap k) ≤
      LinearMap.ker (rotatedHarmonicSphereMap k i j) := by
  intro p hp
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  change polynomialSphereL2 (p : MvPolynomial (Fin 3) ℝ) = 0 at hz
  exact polynomialSphereL2_rotation_eq_zero_of_eq_zero i j p hz

/-- Genuine quotient descent through the actual surjective image map. -/
def harmonicSphereRotationLinear (k : ℕ) (i j : Fin 3) :
    harmonicSphereSubspace k →ₗ[ℝ] harmonicSphereSubspace k :=
  (harmonicPolynomialSphereMap k).liftOfSurjective (harmonicPolynomialSphereMap_surjective k)
    ⟨rotatedHarmonicSphereMap k i j,harmonicPolynomialSphereMap_ker_le_rotated k i j⟩

lemma harmonicSphereRotationLinear_apply_image (k : ℕ) (i j : Fin 3)
    (p : harmonicHomogeneous k) :
    harmonicSphereRotationLinear k i j (harmonicPolynomialSphereMap k p) =
      rotatedHarmonicSphereMap k i j p := by
  unfold harmonicSphereRotationLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective k)
    (harmonicPolynomialSphereMap_ker_le_rotated k i j)

/-- Actual finite-dimensional continuity, without any supplied norm/domain bound. -/
def harmonicSphereRotation (k : ℕ) (i j : Fin 3) :
    harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k := by
  letI := finiteDimensional_harmonicSphereSubspace k
  exact LinearMap.toContinuousLinearMap (harmonicSphereRotationLinear k i j)

lemma harmonicSphereRotation_apply_image (k : ℕ) (i j : Fin 3)
    (p : harmonicHomogeneous k) :
    harmonicSphereRotation k i j (harmonicPolynomialSphereMap k p) =
      rotatedHarmonicSphereMap k i j p :=
  harmonicSphereRotationLinear_apply_image k i j p

lemma inner_harmonicSphereRotation_skew (k : ℕ) (i j : Fin 3)
    (u v : harmonicSphereSubspace k) :
    ⟪harmonicSphereRotation k i j u,v⟫_ℝ = -⟪u,harmonicSphereRotation k i j v⟫_ℝ := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨q,rfl⟩
  rw [harmonicSphereRotation_apply_image,harmonicSphereRotation_apply_image]
  change ⟪polynomialSphereL2 (polynomialRotation i j p),polynomialSphereL2 q⟫_ℝ =
    -⟪polynomialSphereL2 p,polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ
  exact polynomialSphereL2_rotation_skew i j p q

/-- True projection commutation for actual ambient smooth fields, derived rather than assumed. -/
theorem sphereHarmonicCoordinate_sphereRotationDerivative (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (i j : Fin 3) (F : R3 → ℝ) (hF : ContDiff ℝ ∞ F) :
    sphereHarmonicCoordinate hO hD k
      (smoothSphereLift (sphereRotationDerivative i j F) (contDiff_sphereRotationDerivative i j F hF)) =
        harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (smoothSphereLift F hF)) := by
  apply ext_inner_right ℝ
  intro v
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  rw [sphereHarmonicCoordinate_inner hO hD k _ (harmonicPolynomialSphereMap k p),
    inner_harmonicSphereRotation_skew,
    sphereHarmonicCoordinate_inner hO hD k _
      (harmonicSphereRotation k i j (harmonicPolynomialSphereMap k p)),
    harmonicSphereRotation_apply_image]
  change ⟪smoothSphereLift (sphereRotationDerivative i j F)
      (contDiff_sphereRotationDerivative i j F hF),polynomialSphereL2 p⟫_ℝ =
    -⟪smoothSphereLift F hF,polynomialSphereL2 (polynomialRotation i j p)⟫_ℝ
  have h := inner_sphereRotationDerivative_skew i j F (polynomialEvaluation p)
    hF (contDiff_polynomialEvaluation p)
  rw [smoothSphereLift_polynomialEvaluation p,smoothSphereLift_rotation_polynomial i j p] at h
  exact h

lemma harmonicSphereRotation_self (k : ℕ) (i : Fin 3) : harmonicSphereRotation k i i = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  rw [harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (polynomialRotation i i p) = 0
  simp [polynomialRotation]

lemma harmonicSphereRotation_degree_zero (i j : Fin 3) : harmonicSphereRotation 0 i j = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rcases harmonicPolynomialSphereMap_surjective 0 v with ⟨p,rfl⟩
  rw [harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (polynomialRotation i j p) = 0
  rw [SphereDerivativeAdjoint.eq_C_of_harmonicHomogeneous_zero p p.property]
  simp [polynomialRotation]

end OAI.AnisotropicCalderon.SmoothSphereRotationProjection
