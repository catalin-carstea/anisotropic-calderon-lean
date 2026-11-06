import Calderon.ActualTSMixedWeakReference

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "EndFC" => Module.End ℝ FC

/-- A coefficient action dominated pointwise in support by a known local normalizer is local. -/
theorem finiteCoreSupportPreserving_of_zero_imp (A B : EndFC)
    (hB : FiniteCoreSupportPreserving hO hD B)
    (hAB : ∀ (F : FC) (x : R3), (B F).val x = 0 → (A F).val x = 0) :
    FiniteCoreSupportPreserving hO hD A := by
  intro F
  have hs : Function.support (A F).val ⊆ Function.support (B F).val := by
    intro x hx hz
    exact hx (hAB F x hz)
  exact (closure_mono hs).trans (hB F)

/-- Support transport across the exact difference decomposition, before geometric specialization. -/
theorem finiteCoreSupportPreserving_of_sub (A B : EndFC)
    (hDiff : FiniteCoreSupportPreserving hO hD (A-B))
    (hB : FiniteCoreSupportPreserving hO hD B) :
    FiniteCoreSupportPreserving hO hD A := by
  have hSum : FiniteCoreSupportPreserving hO hD ((A-B)+B) :=
    finiteCoreSupportPreserving_add hO hD (A-B) B hDiff hB
  exact Eq.mp (congrArg (fun T : EndFC => FiniteCoreSupportPreserving hO hD T)
    (sub_add_cancel A B)) hSum

variable (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

/-- The exact principal scalar coefficient is local. -/
theorem finiteCoreSupportPreserving_nativePrincipalCoefficient (i j : Fin 3) :
    FiniteCoreSupportPreserving hO hD
      (nativePrincipalCoefficient hO hD g g2 hg L q dr Ar p hg2 hdr hAr i j) := by
  unfold nativePrincipalCoefficient
  exact finiteCoreSupportPreserving_coreScalar hO hD _ _

/-- The complete original first coefficient acts on the genuine finite Bessel normalizer. -/
theorem finiteCoreSupportPreserving_nativeB (j : Fin 3) :
    FiniteCoreSupportPreserving hO hD (nativeB hO hD hF g g2 hg L q dr Ar p j hg2 hdr hAr) := by
  apply finiteCoreSupportPreserving_of_zero_imp hO hD _
    (coreWeightOperator hO hD (besselWeight 1))
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
  intro F x hx
  change ActualNormalizedSecondModelCoefficients.modelFirstNormalizedCoefficient
    hF hO hD g g2 hg L q dr Ar p j x
    ((coreWeightOperator hO hD (besselWeight 1) F).val x) = 0
  rw [hx,map_zero]

/-- The complete first adjoint-defect coefficient retains its exact normalized action. -/
theorem finiteCoreSupportPreserving_nativeV (j : Fin 3) :
    FiniteCoreSupportPreserving hO hD (nativeV hO hD hF g g2 hg L q dr Ar p j hg2 hdr hAr) := by
  apply finiteCoreSupportPreserving_of_zero_imp hO hD _
    (coreWeightOperator hO hD (besselWeight 1))
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
  intro F x hx
  change ActualNormalizedSecondModelDefectCoefficients.modelDefectFirstNormalizedCoefficient
    hF hO hD g g2 hg L q dr Ar p j x
    ((coreWeightOperator hO hD (besselWeight 1) F).val x) = 0
  rw [hx,map_zero]


/-- The full zero coefficient uses its checked second-normalized angular graph. -/
theorem finiteCoreSupportPreserving_nativeC :
    FiniteCoreSupportPreserving hO hD (nativeC hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) := by
  apply finiteCoreSupportPreserving_of_zero_imp hO hD _
    (coreWeightOperator hO hD (besselWeight 2))
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
  intro F x hx
  rw [nativeC_secondAngularCoefficient_apply,hx,map_zero]

/-- The full zero adjoint-defect coefficient retains all density, connection and angular terms. -/
theorem finiteCoreSupportPreserving_nativeW :
    FiniteCoreSupportPreserving hO hD (nativeW hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) := by
  apply finiteCoreSupportPreserving_of_zero_imp hO hD _
    (coreWeightOperator hO hD (besselWeight 2))
    (finiteCoreSupportPreserving_coreWeightOperator hO hD _)
  intro F x hx
  rw [nativeW_secondAngularCoefficient_apply,hx,map_zero]

/-- Exact original U locality, including DD, mixed, pure angular and weighted drift contributions. -/
theorem finiteCoreSupportPreserving_nativeU :
    FiniteCoreSupportPreserving hO hD (nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) := by
  rw [nativeU_eq_modelSecondOrder]
  exact finiteCoreSupportPreserving_modelSecondOrder hO hD _ _ _ _
    (fun i => finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
    (fun i j => finiteCoreSupportPreserving_nativePrincipalCoefficient hO hD g g2 hg hg2 L q dr Ar p hdr hAr i j)
    (fun i => finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
    (finiteCoreSupportPreserving_nativeC hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)

attribute [local irreducible] nativeU nativeUdag

/-- Exact original U-adjoint locality via its complete first-order adjoint defect. -/
theorem finiteCoreSupportPreserving_nativeUdag :
    FiniteCoreSupportPreserving hO hD (nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) := by
  have hDiff : FiniteCoreSupportPreserving hO hD
      (nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr-
        nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) := by
    rw [nativeUdag_sub_eq_modelFirstOrder]
    exact finiteCoreSupportPreserving_modelFirstOrder hO hD _ _ _
      (fun i => finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
      (fun i => finiteCoreSupportPreserving_nativeV hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
      (finiteCoreSupportPreserving_nativeW hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
  exact finiteCoreSupportPreserving_of_sub hO hD
    (nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr)
    (nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr) hDiff
    (finiteCoreSupportPreserving_nativeU hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
