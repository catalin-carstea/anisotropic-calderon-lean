import Calderon.ActualUScalarPrincipalSplit
import Calderon.ActualScalarSAdjointCross

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ScalarBaseAdjoint ActualScalarPrincipalAdjoint
  NormalizedPrincipalMetric ReferenceDensityBounds ConformalDepth PrincipalCommutator

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Preserve both lower fields when splitting a signed mixed pairing. -/
lemma signed_inner_split (a ad b bd u ud f fd : E)
    (hu : u = a+b) (hud : ud = ad+bd) :
    ⟪u,f⟫_ℝ-⟪ud,fd⟫_ℝ =
      (⟪a,f⟫_ℝ-⟪ad,fd⟫_ℝ)+(⟪b,f⟫_ℝ-⟪bd,fd⟫_ℝ) := by
  rw [hu,hud,inner_add_left,inner_add_left]
  ring

end Algebra

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hF : SphereFischerInner) (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
  (hg2 : IsAdmissibleMetric g2) (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "FC" => smoothCompactFiniteSphereCore hO hD
local notation "dd" i:max => coreDirectionalDerivative hO hD (coordinateDirection i)
local notation "vv" i:max => nativeV hO hD hF g g2 hg L q dr Ar p i hg2 hdr hAr
local notation "ww" => nativeW hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr
local notation "hRef" => referenceNormalizedPrincipalDifference g g2 L q
local notation "aa" => actualPrincipalMatrix g L q dr Ar p hRef
local notation "mu" => (fun y => referenceDensityFamily g L (q,y))

/-- Original explicit V/W first-order adjoint defect; no residual is defined by subtraction. -/
def nativeUAdjointDefectFirstZeroPart : Module.End ℝ FC :=
  (∑ i : Fin 3, (vv i)*(dd i))+(ww)

/-- Scalar adjoint defect in the exact density-derivative coefficient formula. -/
def actualScalarAdjointFirstZeroOut (u : R3 → SphereL2) (x : R3) : SphereL2 :=
  adjointZeroCoefficient coordinateDirection mu aa x • u x+
    ∑ i : Fin 3, adjointFirstCoefficient coordinateDirection mu aa x i •
      directionalFDeriv (coordinateDirection i) u x

/-- The explicit physical adjoint lower part retains B/C, V/W and scalar density derivatives. -/
def nativeUAdjointFirstZeroOut (F : FC) (x : R3) : SphereL2 :=
  (nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x+
  (nativeUAdjointDefectFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x-
  actualScalarAdjointFirstZeroOut g g2 L q dr Ar p F.val x

private lemma end_eq_add_of_sub_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B D : Module.End ℝ V) (h : A-B=D) : A=B+D := by
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm D B)

attribute [local irreducible] nativeU nativeUdag

/-- Exact complete U-adjoint split before scalar physical specialization. -/
theorem nativeUdag_eq_U_add_explicit_defect :
    nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr =
      nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr+
        nativeUAdjointDefectFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr := by
  apply end_eq_add_of_sub_eq
  exact nativeUdag_sub_eq_modelFirstOrder hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr

include hg hg2 hdr hAr in
/-- The scalar adjoint coefficient theorem uses only original smooth admissible metrics. -/
theorem actualScalarAdjointFirstZeroOut_eq_difference (F : FC) (x : R3) :
    actualScalarAdjointFirstZeroOut g g2 L q dr Ar p F.val x =
      scalarSecondBaseAdjoint coordinateDirection mu aa F.val x-
        scalarSecondBase coordinateDirection aa F.val x := by
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hh (i j : Fin 3) : ContDiff ℝ ∞ (fun y => hRef y i j) :=
    NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry
      g g2 hg hg2 L q i j
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun y => aa y i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q dr Ar p hRef hdr hAr hh i j
  have hs : ∀ᶠ y in 𝓝 x, (aa y).IsHermitian :=
    Filter.Eventually.of_forall (fun y =>
      ActualPerturbedDefect.actualPrincipalMatrix_isHermitian g hg L q dr Ar p hRef y
        (NormalizedPrincipalMetric.referenceNormalizedPrincipalDifference_isHermitian
          g g2 hg hg2 L q y))
  exact (scalarSecondBaseAdjoint_coefficient_form coordinateDirection mu aa F.val
    hm ha F.property.1 x (referenceDensityFamily_pos g hg L (q,x)).ne' hs).symm

/-- Original U physical value with the explicit B/C lower field. -/
theorem nativeU_apply_eq_scalar_add_firstZero (F : FC) (x : R3) :
    (nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x =
      scalarSecondBase coordinateDirection aa F.val x+
        (nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x := by
  have he := congrArg (fun T : Module.End ℝ FC => (T F).val x)
    (nativeU_eq_scalarPrincipal_add_firstZero hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
  simpa only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,
    nativeScalarPrincipalPart_apply_eq_scalarSecondBase] using he

/-- Exact U-adjoint physical scalar adjoint plus all explicit first/zero fields. -/
theorem nativeUdag_apply_eq_scalarAdjoint_add_firstZero (F : FC) (x : R3) :
    (nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x =
      scalarSecondBaseAdjoint coordinateDirection mu aa F.val x+
        nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x := by
  have he := congrArg (fun T : Module.End ℝ FC => (T F).val x)
    (nativeUdag_eq_U_add_explicit_defect hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr)
  simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply] at he
  rw [he,nativeU_apply_eq_scalar_add_firstZero]
  unfold nativeUAdjointFirstZeroOut
  rw [actualScalarAdjointFirstZeroOut_eq_difference hO hD g g2 hg hg2 L q dr Ar p hdr hAr]
  abel

/-- Exact signed full U/S density split; no lower mixed term or adjoint defect is discarded. -/
theorem nativeU_scalar_signed_pairing_split (F : FC) (x : R3) (Sf Sd : SphereL2) :
    ⟪(nativeU hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x,Sf⟫_ℝ-
      ⟪(nativeUdag hO hD hF g g2 hg L q dr Ar p hg2 hdr hAr F).val x,Sd⟫_ℝ =
      (⟪scalarSecondBase coordinateDirection aa F.val x,Sf⟫_ℝ-
        ⟪scalarSecondBaseAdjoint coordinateDirection mu aa F.val x,Sd⟫_ℝ)+
      (⟪(nativeUFirstZeroPart hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F).val x,Sf⟫_ℝ-
        ⟪nativeUAdjointFirstZeroOut hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x,Sd⟫_ℝ) :=
  signed_inner_split _ _ _ _ _ _ _ _
    (nativeU_apply_eq_scalar_add_firstZero hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x)
    (nativeUdag_apply_eq_scalarAdjoint_add_firstZero hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr F x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
