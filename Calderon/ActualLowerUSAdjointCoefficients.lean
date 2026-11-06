import Calderon.ActualUAdjointScalarSplit
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficients
import Calderon.ActualFiniteHarmonicModelWPolynomialIdentity

/-!
Author: delegated GPT-6.1 Sol, 3 November 2026.
Upfront: ../bound-route-analysis.md, section Exact finite weak-row plan.
Narrow algebraic dictionaries only. No analytic cap premise or proof admission.
Authored against the assignment's single pinned 4554-provider context.
This source has not been compiled by its author; Root owns the diagnostic/check.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualPhysicalMixedFirst NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ReferenceDensityBounds
  PrincipalCommutator ConformalDepth ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftWeightedCoefficients

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)
local notation "bb" i:max => nativeB hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "vv" i:max => nativeV hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "cc" => nativeC hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "ww" => nativeW hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "hRef" => referenceNormalizedPrincipalDifference g g2 L q
local notation "mu" => (fun x => referenceDensityFamily g L (q,x))
local notation "aa" => actualPrincipalMatrix g L q dr Ar p hRef
local notation "s1" i:max => coreScalar hO hD
  (fun x => adjointFirstCoefficient coordinateDirection mu aa x i)
  (contDiff_modelAdjointFirstCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i)
local notation "s0" => coreScalar hO hD
  (fun x => adjointZeroCoefficient coordinateDirection mu aa x)
  (contDiff_modelAdjointZeroCoefficient g g2 hg hg2 L q dr Ar p hdr hAr)
local notation "bs" i:max => coreScalar hO hD (nativeFirstScalarCoefficient g g2 L q dr Ar p i)
  (contDiff_nativeFirstScalarCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i)
local notation "bd" i:max => coreScalar hO hD (nativeFirstDegreeCoefficient g g2 L q dr Ar p i)
  (contDiff_nativeFirstDegreeCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i)
local notation "bc" i:max j:max => coreScalar hO hD (nativeFirstConnectionCoefficient g g2 L q dr Ar p i j)
  (contDiff_nativeFirstConnectionCoefficient g g2 hg hg2 L q dr Ar p hdr hAr i j)
local notation "mc" a:max i:max => coreScalar hO hD
  (physicalMixedFirstCoefficient g L q hRef a i)
  (contDiff_physicalMixedFirstCoefficient g hg L q hRef
    (fun j k => contDiff_referenceNormalizedPrincipalDifference_entry g g2 hg hg2 L q j k) a i)
local notation "yy" => nativeReferenceWeightedAdjointDerivativeRawAction hO hD g hg L q dr Ar p hRef
  (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g g2 hg hg2 L q)
  hdr hAr
local notation "wp" => nativeWPolynomialPart hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "dv" => coreScalar hO hD (ActualNormalizedSecondDriftNativeAdjunction.normalizedSecondDriftDensityDivergence g g2 L q dr Ar p)
  (ActualNormalizedSecondDriftNativeAdjunction.contDiff_normalizedSecondDriftDensityDivergence g g2 hg hg2 L q dr Ar p hdr hAr)

/-- Exact first-base coefficient of the literal U lower adjoint, retaining the
subtracted scalar density-adjoint first correction. -/
def nativeULowerAdjointFirstCoefficient (i : Fin 3) : Module.End ℝ FC :=
  bb i + vv i - s1 i

/-- Exact zero-base coefficient after the scalar a0 cancellation. The existing
weighted derivative and drift-density terms remain explicit. -/
def nativeULowerAdjointZeroCoefficient : Module.End ℝ FC :=
  cc + yy + wp - dv

local notation "df" => nativeULowerAdjointFirstCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "dz" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

/-- Density a1 and raising contributions cancel exactly. The connection sign
is retained and the remaining mixed angular action is the original lowering. -/
theorem nativeULowerAdjointFirstCoefficient_eq_full_angular (i : Fin 3) :
    df i = -bs i - (bd i) * coreDegree hO hD +
      (∑ c : Fin 3, (bc i c) * nativeReferenceConnectionAction hO hD g hg L q c) -
      ∑ a : Fin 3, (mc a i) * coreDerivative hO hD hF a := by
  unfold nativeULowerAdjointFirstCoefficient
  rw [nativeB_eq_full_angular_coefficients hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr i,
    nativeV_eq_full_angular_coefficients hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr i]
  simp only [mul_add, Finset.sum_add_distrib, smul_mul_assoc]
  module

/-- The zero scalar-adjoint coefficient cancels with its literal term inside W;
all weighted density derivatives and the drift divergence survive. -/
theorem nativeULowerAdjointZeroCoefficient_eq_original :
    dz = cc + ww - s0 := by
  rw [nativeW_eq_polynomial_and_density_parts hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr]
  unfold nativeULowerAdjointZeroCoefficient
  module

/-- Pointwise original first/zero output dictionary. This is exactly the existing
nativeUAdjointFirstZeroOut, without an invented raw adjoint or residual field. -/
theorem nativeUAdjointFirstZeroOut_eq_lower_adjoint_coefficients
    (F : FC) (x : R3) :
    nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x =
      (∑ i : Fin 3, (df i ((dd i) F)).val x) + (dz F).val x := by
  have hFirst (i : Fin 3) :
      (df i ((dd i) F)).val x =
        ((bb i) ((dd i) F)).val x + ((vv i) ((dd i) F)).val x -
          adjointFirstCoefficient coordinateDirection mu aa x i •
            directionalFDeriv (coordinateDirection i) F.val x := by
    rfl
  have hZero : (dz F).val x = (cc F).val x + (ww F).val x -
      adjointZeroCoefficient coordinateDirection mu aa x • F.val x := by
    rw [nativeULowerAdjointZeroCoefficient_eq_original hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr]
    rfl
  simp_rw [hFirst]
  rw [hZero]
  simp only [nativeUAdjointFirstZeroOut, nativeUFirstZeroPart,
    nativeUAdjointDefectFirstZeroPart, actualScalarAdjointFirstZeroOut,
    LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, Finset.sum_apply]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
