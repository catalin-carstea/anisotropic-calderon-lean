import Calderon.CovariantProjectedEnergy
import Calderon.SphereDerivativeAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.HarmonicDerivativeOperator
open SphereHarmonic SmoothSphereRotationProjection SphereDerivativeAdjoint SphereHilbertDecomposition

local instance (k : ℕ) : CompleteSpace (harmonicSphereSubspace k) :=
  completeSpace_harmonicSphereSubspace k

def harmonicPolynomialDerivativeMap (m : ℕ) (i : Fin 3) :
    harmonicHomogeneous (m+1) →ₗ[ℝ] harmonicSphereSubspace m where
  toFun p := ⟨polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ)),
    polynomialSphereL2_mem m _ (pderiv_harmonicHomogeneous_succ m i p p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change polynomialSphereL2 (pderiv i ((p : MvPolynomial (Fin 3) ℝ)+q)) = _
    rw [map_add,map_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change polynomialSphereL2 (pderiv i (c • (p : MvPolynomial (Fin 3) ℝ))) =
      c • polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ))
    rw [smul_eq_C_mul,pderiv_C_mul,← smul_eq_C_mul,map_smul]

lemma harmonicPolynomialSphereMap_ker_le_derivative (hF : SphereFischerInner)
    (m : ℕ) (i : Fin 3) :
    LinearMap.ker (harmonicPolynomialSphereMap (m+1)) ≤
      LinearMap.ker (harmonicPolynomialDerivativeMap m i) := by
  intro p hp
  have hz : polynomialSphereL2 (p : MvPolynomial (Fin 3) ℝ) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  have hpz := (polynomialSphereL2_eq_zero_iff hF (m+1) p p.property).mp hz
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin 3) ℝ)) = 0
  rw [hpz,map_zero,map_zero]

def harmonicDerivativeLinear (hF : SphereFischerInner) (m : ℕ) (i : Fin 3) :
    harmonicSphereSubspace (m+1) →ₗ[ℝ] harmonicSphereSubspace m :=
  (harmonicPolynomialSphereMap (m+1)).liftOfSurjective
    (harmonicPolynomialSphereMap_surjective (m+1))
    ⟨harmonicPolynomialDerivativeMap m i,harmonicPolynomialSphereMap_ker_le_derivative hF m i⟩

lemma harmonicDerivativeLinear_apply_image (hF : SphereFischerInner) (m : ℕ) (i : Fin 3)
    (p : harmonicHomogeneous (m+1)) :
    harmonicDerivativeLinear hF m i (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialDerivativeMap m i p := by
  unfold harmonicDerivativeLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective (m+1))
    (harmonicPolynomialSphereMap_ker_le_derivative hF m i)

/-- Genuine ambient differentiation of the harmonic extension on one positive degree. -/
def harmonicDerivative (hF : SphereFischerInner) (m : ℕ) (i : Fin 3) :
    harmonicSphereSubspace (m+1) →L[ℝ] harmonicSphereSubspace m := by
  letI := finiteDimensional_harmonicSphereSubspace (m+1)
  exact (harmonicDerivativeLinear hF m i).toContinuousLinearMap

lemma harmonicDerivative_apply_image (hF : SphereFischerInner) (m : ℕ) (i : Fin 3)
    (p : harmonicHomogeneous (m+1)) :
    harmonicDerivative hF m i (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialDerivativeMap m i p := harmonicDerivativeLinear_apply_image hF m i p

def harmonicPolynomialDerivativeAdjointMap (k : ℕ) (i : Fin 3) :
    harmonicHomogeneous k →ₗ[ℝ] harmonicSphereSubspace (k+1) where
  toFun p := ⟨polynomialSphereL2 (sphereDerivativeAdjoint k i p),
    polynomialSphereL2_mem (k+1) _ (sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change polynomialSphereL2 (sphereDerivativeAdjoint k i ((p : MvPolynomial (Fin 3) ℝ)+q)) = _
    rw [sphereDerivativeAdjoint_add,map_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change polynomialSphereL2 (sphereDerivativeAdjoint k i (c • (p : MvPolynomial (Fin 3) ℝ))) =
      c • polynomialSphereL2 (sphereDerivativeAdjoint k i (p : MvPolynomial (Fin 3) ℝ))
    rw [smul_eq_C_mul,sphereDerivativeAdjoint_C_mul,← smul_eq_C_mul,map_smul]

lemma harmonicPolynomialSphereMap_ker_le_derivativeAdjoint (hF : SphereFischerInner)
    (k : ℕ) (i : Fin 3) :
    LinearMap.ker (harmonicPolynomialSphereMap k) ≤
      LinearMap.ker (harmonicPolynomialDerivativeAdjointMap k i) := by
  intro p hp
  have hz : polynomialSphereL2 (p : MvPolynomial (Fin 3) ℝ) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  have hpz := (polynomialSphereL2_eq_zero_iff hF k p p.property).mp hz
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change polynomialSphereL2 (sphereDerivativeAdjoint k i (p : MvPolynomial (Fin 3) ℝ)) = 0
  rw [hpz,sphereDerivativeAdjoint_zero,map_zero]

def harmonicDerivativeAdjointLinear (hF : SphereFischerInner) (k : ℕ) (i : Fin 3) :
    harmonicSphereSubspace k →ₗ[ℝ] harmonicSphereSubspace (k+1) :=
  (harmonicPolynomialSphereMap k).liftOfSurjective (harmonicPolynomialSphereMap_surjective k)
    ⟨harmonicPolynomialDerivativeAdjointMap k i,harmonicPolynomialSphereMap_ker_le_derivativeAdjoint hF k i⟩

lemma harmonicDerivativeAdjointLinear_apply_image (hF : SphereFischerInner) (k : ℕ) (i : Fin 3)
    (p : harmonicHomogeneous k) :
    harmonicDerivativeAdjointLinear hF k i (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialDerivativeAdjointMap k i p := by
  unfold harmonicDerivativeAdjointLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective k)
    (harmonicPolynomialSphereMap_ker_le_derivativeAdjoint hF k i)

/-- Actual probability-sphere adjoint, constructed before proving its adjoint identity. -/
def harmonicDerivativeAdjoint (hF : SphereFischerInner) (k : ℕ) (i : Fin 3) :
    harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace (k+1) := by
  letI := finiteDimensional_harmonicSphereSubspace k
  exact (harmonicDerivativeAdjointLinear hF k i).toContinuousLinearMap

lemma harmonicDerivativeAdjoint_apply_image (hF : SphereFischerInner) (k : ℕ) (i : Fin 3)
    (p : harmonicHomogeneous k) :
    harmonicDerivativeAdjoint hF k i (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialDerivativeAdjointMap k i p := harmonicDerivativeAdjointLinear_apply_image hF k i p

theorem inner_harmonicDerivativeAdjoint (hF : SphereFischerInner) (k : ℕ) (i : Fin 3)
    (u : harmonicSphereSubspace k) (v : harmonicSphereSubspace (k+1)) :
    ⟪harmonicDerivativeAdjoint hF k i u,v⟫_ℝ = ⟪u,harmonicDerivative hF k i v⟫_ℝ := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  rcases harmonicPolynomialSphereMap_surjective (k+1) v with ⟨q,rfl⟩
  rw [harmonicDerivativeAdjoint_apply_image,harmonicDerivative_apply_image]
  exact sphereDerivativeAdjoint_inner_adjoint hF k i p q p.property q.property

theorem harmonicDerivativeAdjoint_eq_adjoint (hF : SphereFischerInner) (k : ℕ) (i : Fin 3) :
    harmonicDerivativeAdjoint hF k i = ContinuousLinearMap.adjoint (harmonicDerivative hF k i) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [inner_harmonicDerivativeAdjoint,ContinuousLinearMap.adjoint_inner_left]

end OAI.AnisotropicCalderon.HarmonicDerivativeOperator
