import Calderon.ActualFiniteHarmonicModelReferenceAdjointZeroRaw
import Calderon.ActualFiniteHarmonicModelReferenceEnergyRepresentative
import Calderon.ActualFiniteHarmonicCoreScalarCentral
import Calderon.ActualFiniteModelSupport
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSShiftedAdjointDictionary
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualModelCommutatorWords
  SpectralWeightedGraph AmbientReferenceRaising ConformalDepth ReferenceDensityBounds

private lemma shifted_zero_word {A : Type*} [Ring A] (d G p N : A) (hp : Commute d p) :
    d*(-G+p*(N-1))+p*d = d*(-G+p*N) := by
  rw [← hp.eq]
  noncomm_ring

private lemma modelFirstOrder_add_zero {A : Type*} [Ring A]
    (d H : Fin 3 → A) (H0 Z : A) :
    modelFirstOrder d H H0+Z=modelFirstOrder d H (H0+Z) := by
  unfold modelFirstOrder
  exact add_assoc _ _ _

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)

local notation "D" => coreDerivative hO hD hF
local notation "G" => nativeReferenceConnectionAction hO hD g hg L q
local notation "P" => nativeReferenceProfileScalar hO hD g hg L q dr Ar p hdr hAr
local notation "N" => coreDegree hO hD
local notation "H0" => nativeReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr
local notation "Z0" => coreDefectAction hO hD hF g hg L q dr Ar p hdr hAr

/-- The full shifted zero coefficient, with the profile-degree offset combined exactly. -/
def shiftedReferenceAdjointZeroCoefficient :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, D a*(-G a+P a*N)

/-- Literal endomorphism equality for the original Z field. -/
theorem nativeZ_eq_coreDefectAction :
    nativeZ hO hD hF g hg L q dr Ar p hdr hAr=Z0 := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  exact nativeZField_eq_coreAction hO hD hF g hg L q dr Ar p hdr hAr F

/-- The original adjoint zero coefficient plus the entire Z shift. -/
theorem adjoint_zero_add_defect_eq_shifted :
    H0+Z0=shiftedReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr := by
  rw [nativeReferenceAdjointZeroCoefficient_eq_raw hO hD hF g hg L q dr Ar p hdr hAr]
  change (∑ a : Fin 3, D a*(-G a+P a*(N-1)))+
    (∑ a : Fin 3, P a*D a)=∑ a : Fin 3, D a*(-G a+P a*N)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hc : Commute (D a) (P a) := by
    change Commute (coreDerivative hO hD hF a) (coreScalar hO hD _ _)
    exact scalarCentral_coreDerivative hO hD hF a _ _
  exact shifted_zero_word (D a) (G a) (P a) N hc

/-- The actual first-adjoint coefficient has exactly the negative derivative/frame sign. -/
theorem native_adjoint_first_coefficient_eq (j : Fin 3) :
    nativeReferenceAdjointFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr j=
      -(∑ a : Fin 3, D a*nativeReferenceFrameScalar hO hD g hg L q a j) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [nativeReferenceAdjointFirstCoefficient,coreDerivative,
    LinearMap.sum_apply,LinearMap.neg_apply,Module.End.mul_apply,LinearMap.smul_apply,
    Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_neg,Pi.smul_apply,Pi.neg_apply,
    Finset.sum_apply,_root_.neg_one_smul ℝ,Finset.sum_neg_distrib]

/-- Complete original T-adjoint-plus-Z operator with its literal shifted zero coefficient. -/
theorem native_shifted_adjoint_eq_modelFirstOrder :
    nativeTdag hO hD hF g hg L q dr Ar p hdr hAr+
      nativeZ hO hD hF g hg L q dr Ar p hdr hAr=
    modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
      (nativeReferenceAdjointFirstCoefficient hO hD hF g hg L q dr Ar p hdr hAr)
      (shiftedReferenceAdjointZeroCoefficient hO hD hF g hg L q dr Ar p hdr hAr) := by
  rw [nativeTdag_eq_modelFirstOrder hO hD hF g hg L q dr Ar p hdr hAr,
    nativeZ_eq_coreDefectAction hO hD hF g hg L q dr Ar p hdr hAr,
    modelFirstOrder_add_zero,
    adjoint_zero_add_defect_eq_shifted hO hD hF g hg L q dr Ar p hdr hAr]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSShiftedAdjointDictionary
