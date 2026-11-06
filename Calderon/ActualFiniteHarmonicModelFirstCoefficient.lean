import Calderon.ActualFiniteHarmonicModelReference
import Calderon.ActualFiniteHarmonicModelCoefficientCore
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph BoundedAngularShift ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceDDSpectralTransport ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ActualPhysicalMixedFirst
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ReferenceDensityBounds
  NormalizedPrincipalMetric PrincipalCommutator ConformalDepth

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeFirstCoefficientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeFirstCoefficientFunction

def nativeBField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (coreWeightOperator hO hD (besselWeight 1) F x)

def nativeVField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (coreWeightOperator hO hD (besselWeight 1) F x)

lemma contDiff_modelAdjointFirstCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => adjointFirstCoefficient coordinateDirection
      (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp
      (contDiff_const.prodMk contDiff_id)
  have hmi : ContDiff ℝ ∞ (fun x : R3 => (referenceDensityFamily g1 L (lam,x))⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp
      (contDiff_const.prodMk contDiff_id)
  have hh := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have ha (i : Fin 3) : ContDiff ℝ ∞ (fun x : R3 =>
      actualPrincipalMatrix g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) x j i) := by
    unfold actualPrincipalMatrix
    exact hr.mul
      (((contDiff_referenceInverseEntryFamily g1 hg1 L j i).comp
        (contDiff_const.prodMk contDiff_id)).add
          ((contDiff_apply_apply ℝ ℝ j i).comp hh))
  unfold adjointFirstCoefficient
  exact (contDiff_const.mul hmi).mul
    (ContDiff.sum fun i _ => contDiff_directionalFDeriv (coordinateDirection i) _
      (hm.mul (ha i)))

def coreModelFirstCoefficientAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hK : ContDiff ℝ ∞ K :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      hδ hR h hh j
  have hKg (x : R3) : PreservesSphereSpectralGraphs hO hD (K x) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
      hO hD g1 hg1 L lam δ R p h j x
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j
  have hJ : ContDiff ℝ ∞ J :=
    contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR j
  have hJg (x : R3) : PreservesSphereSpectralGraphs hO hD (J x) := by
    unfold J normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  exact coreCoefficientAction hO hD K hK hKg +
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam h a j)
      (hm a) * coreNormalizedRaising hO hD hF a) +
    coreCoefficientAction hO hD J hJ hJg

def coreModelDefectFirstCoefficientAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hK : ContDiff ℝ ∞ K :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      hδ hR h hh j
  have hKg (x : R3) : PreservesSphereSpectralGraphs hO hD (K x) :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
      hO hD g1 hg1 L lam δ R p h j x
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j
  have hJ : ContDiff ℝ ∞ J :=
    contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR j
  have hJg (x : R3) : PreservesSphereSpectralGraphs hO hD (J x) := by
    unfold J normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hKa : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.adjoint (K x)) :=
    contDiff_angularAdjoint K hK
  have hKag (x : R3) : PreservesSphereSpectralGraphs hO hD
      (ContinuousLinearMap.adjoint (K x)) :=
    preservesSphereSpectralGraphs_adjoint hO hD (K x) (hKg x)
  exact coreScalar hO hD
      (fun x => adjointFirstCoefficient coordinateDirection
        (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p h) x j)
      (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j) *
        coreCoefficientAction hO hD (fun _ => inverseDegreeMultiplier hO hD) contDiff_const
          (fun _ => preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD) -
    coreCoefficientAction hO hD K hK hKg -
    coreCoefficientAction hO hD (fun x => ContinuousLinearMap.adjoint (K x)) hKa hKag -
    (∑ a : Fin 3, coreScalar hO hD (physicalMixedFirstCoefficient g1 L lam h a j)
      (hm a) * (coreNormalizedDerivative hO hD hF a + coreNormalizedRaising hO hD hF a)) -
    (2 : ℝ) • coreCoefficientAction hO hD J hJ hJg

lemma nativeBField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F =
      ((coreModelFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        coreWeightOperator hO hD (besselWeight 1)) F : R3 → SphereL2) := by
  funext x
  simp only [nativeBField, modelFirstNormalizedCoefficient, coreModelFirstCoefficientAction,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, coreCoefficientAction, coreScalar,
    coreNormalizedRaising, coreNormalizedDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

lemma nativeVField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F =
      ((coreModelDefectFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        coreWeightOperator hO hD (besselWeight 1)) F : R3 → SphereL2) := by
  funext x
  simp only [nativeVField, modelDefectFirstNormalizedCoefficient, coreModelDefectFirstCoefficientAction,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, coreCoefficientAction, coreScalar,
    coreNormalizedRaising, coreNormalizedDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]

def nativeB
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F, by
    rw [nativeBField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F]
    exact ((coreModelFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coreWeightOperator hO hD (besselWeight 1)) F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeBField hO hD hF g1 g2 hg1 L lam δ R p j (F+G) =
      nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F +
      nativeBField hO hD hF g1 g2 hg1 L lam δ R p j G
    simp only [nativeBField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeBField hO hD hF g1 g2 hg1 L lam δ R p j (c • F) =
      c • nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F
    simp only [nativeBField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

def nativeV
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F, by
    rw [nativeVField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F]
    exact ((coreModelDefectFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coreWeightOperator hO hD (besselWeight 1)) F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeVField hO hD hF g1 g2 hg1 L lam δ R p j (F+G) =
      nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F +
      nativeVField hO hD hF g1 g2 hg1 L lam δ R p j G
    simp only [nativeVField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeVField hO hD hF g1 g2 hg1 L lam δ R p j (c • F) =
      c • nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F
    simp only [nativeVField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
