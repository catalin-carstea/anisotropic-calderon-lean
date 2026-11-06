import Calderon.ActualModelSFullWeakReference

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ScalarBaseAdjoint ActualScalarPrincipalAdjoint
  NormalizedPrincipalMetric ReferenceDensityBounds ConformalDepth PrincipalCommutator

/-- The scalar matrix in the checked scalar/S estimate is exactly the original U principal matrix. -/
theorem actualPrincipalMatrix_referenceDifference (g g2 : MatrixField)
    (L q dr Ar : ℝ) (p : ℕ) (x : R3) (i j : Fin 3) :
    actualPrincipalMatrix g L q dr Ar p (referenceNormalizedPrincipalDifference g g2 L q) x i j =
      referenceRadius dr Ar p L x*referenceNormalizedPrincipalMatrix g g2 L q x i j := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := referenceMetric (dilatedMetric g q) L x
  let N : Matrix (Fin 3) (Fin 3) ℝ := normalizedPrincipalMatrix A (dilatedMetric g2 q x)
  change referenceRadius dr Ar p L x*(A⁻¹ i j+(N i j-A⁻¹ i j)) =
    referenceRadius dr Ar p L x*N i j
  ring

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)
local notation "aa" i:max j:max => nativePrincipalCoefficient hO hD g g2 hg L q dr Ar p hg2 hdr hAr i j
local notation "bb" i:max => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "cc" => nativeC hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr

/-- The nine original ordered scalar principal words, as a finite-core endomorphism. -/
def nativeScalarPrincipalPart : Module.End ℝ FC :=
  ∑ i : Fin 3, ∑ j : Fin 3, (aa i j)*(dd i)*(dd j)

/-- Explicit first/zero U remainder in original B/C coefficients; it is not defined by subtraction. -/
def nativeUFirstZeroPart : Module.End ℝ FC :=
  (∑ i : Fin 3, (bb i)*(dd i))+(cc)

/-- Literal scalar coefficient action, with the original normalized difference specialized exactly. -/
theorem nativePrincipalCoefficient_apply_actualScalar
    (i j : Fin 3) (F : FC) (x : R3) :
    ((aa i j) F).val x =
      actualPrincipalMatrix g L q dr Ar p (referenceNormalizedPrincipalDifference g g2 L q) x i j • F.val x := by
  change (referenceRadius dr Ar p L x*referenceNormalizedPrincipalMatrix g g2 L q x i j) • F.val x = _
  rw [actualPrincipalMatrix_referenceDifference]

/-- Exact physical scalar-second-base dictionary; ordered coordinate derivatives are unchanged. -/
theorem nativeScalarPrincipalPart_apply_eq_scalarSecondBase (F : FC) (x : R3) :
    (nativeScalarPrincipalPart hO hD g g2 hg hg2 L q dr Ar p hdr hAr F).val x =
      scalarSecondBase coordinateDirection
        (actualPrincipalMatrix g L q dr Ar p (referenceNormalizedPrincipalDifference g g2 L q)) F.val x := by
  simp only [nativeScalarPrincipalPart,scalarSecondBase,Fin.sum_univ_three,
    LinearMap.add_apply,Module.End.mul_apply,Submodule.coe_add,Pi.add_apply,
    nativePrincipalCoefficient_apply_actualScalar]
  rfl

/-- The original full U is exactly scalar principal plus the explicit first/zero part. -/
theorem nativeU_eq_scalarPrincipal_add_firstZero :
    nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr =
      nativeScalarPrincipalPart hO hD g g2 hg hg2 L q dr Ar p hdr hAr+
        nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr := by
  rw [nativeU_eq_modelSecondOrder]
  unfold ActualModelCommutatorWords.modelSecondOrder nativeScalarPrincipalPart nativeUFirstZeroPart
  exact add_assoc _ _ _

/-- The explicit lower-base U part retains the original input support. -/
theorem finiteCoreSupportPreserving_nativeUFirstZeroPart :
    FiniteCoreSupportPreserving hO hD
      (nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr) := by
  unfold nativeUFirstZeroPart
  apply finiteCoreSupportPreserving_add
  · apply finiteCoreSupportPreserving_sum
    intro i _hi
    exact finiteCoreSupportPreserving_mul hO hD _ _
      (finiteCoreSupportPreserving_nativeB hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr i)
      (finiteCoreSupportPreserving_coreDirectionalDerivative hO hD _)
  · exact finiteCoreSupportPreserving_nativeC hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
