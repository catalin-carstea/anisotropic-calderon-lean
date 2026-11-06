import Calderon.ActualFiniteHarmonicModelFirstCoefficient
import Calderon.ActualFiniteHarmonicModelZeroCoefficient
import Calderon.NormalizedPrincipalMetricSmooth
import Calderon.ActualMixedDensityScalarZeroFactorSmoothness

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualScalarPrincipalAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothSphereFields SmoothAngularApplication

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeErrorCoreFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeErrorCoreFunction

def nativeUField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def nativeUdagField
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def coreModelPrincipalAction
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 =>
      referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j) :=
    by
      exact OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm.contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
        g1 g2 hg1 hg2 L lam δ R p hδ hR i j
  exact ∑ i : Fin 3, ∑ j : Fin 3,
    coreScalar hO hD
      (fun x => referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j)
      (ha i j) * coreDirectionalDerivative hO hD (coordinateDirection i) *
        coreDirectionalDerivative hO hD (coordinateDirection j)

lemma coreModelPrincipal_apply
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreModelPrincipalAction hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      ScalarBaseAdjoint.scalarSecondBase coordinateDirection
        (fun y => referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (F : R3 → SphereL2) x := by
  simp only [coreModelPrincipalAction, ScalarBaseAdjoint.scalarSecondBase,
    LinearMap.sum_apply, Module.End.mul_apply, coreScalar, coreDirectionalDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk, Submodule.coe_sum,
    Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]

def coreModelErrorAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := 
  coreModelPrincipalAction hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR +
    (∑ j : Fin 3, nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coreDirectionalDerivative hO hD (coordinateDirection j)) +
    nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

def coreModelErrorAdjointAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := 
  coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR +
    (∑ j : Fin 3, nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coreDirectionalDerivative hO hD (coordinateDirection j)) +
    nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

lemma modelError_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  rw [normalizedSecondModelError_representative_principal_first
    hO hD hF g1 g2 hg1 L lam δ R p hδ hR F r x,
    nativeCField_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x]
  have hfirst : coreModelFirstBaseAction hO hD hF g1 g2 hg1 L lam δ R p F x =
      ∑ j : Fin 3, nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x := by
    unfold coreModelFirstBaseAction
    apply Finset.sum_congr rfl
    intro j _
    have hc := coreWeightOperator_directionalDerivative_commute hO hD
      (besselWeight 1) (coordinateDirection j)
    have he := congrArg
      (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x) hc.eq
    change coreWeightOperator hO hD (besselWeight 1)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x =
      coreDirectionalDerivative hO hD (coordinateDirection j)
        (coreWeightOperator hO hD (besselWeight 1) F) x at he
    change modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (coreDirectionalDerivative hO hD (coordinateDirection j)
          (coreWeightOperator hO hD (besselWeight 1) F) x) =
      modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight 1)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F) x)
    exact congrArg (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x)
      he.symm
  rw [hfirst, ← coreModelPrincipal_apply hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR F x]
  simp only [coreModelErrorAction, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, nativeC, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, Submodule.coe_add, Submodule.coe_sum, Finset.sum_apply, Pi.add_apply]

lemma modelErrorAdjoint_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreModelErrorAdjointAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  have hd := normalizedSecondModelErrorDefect_full_coefficient_form
    hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR
    (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x
  unfold normalizedSecondModelErrorDefect at hd
  rw [modelError_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x,
    nativeWField_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x] at hd
  have hweight : ambientBesselField hO hD 1 (by norm_num)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) =
      (fun y => coreWeightOperator hO hD (besselWeight 1) F y) :=
    funext (fun y =>
      (coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) y).symm)
  unfold modelDefectFirstBaseField at hd
  rw [hweight] at hd
  have hfirst :
      (∑ j : Fin 3, modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (directionalFDeriv (coordinateDirection j)
          (fun y => coreWeightOperator hO hD (besselWeight 1) F y) x)) =
      ∑ j : Fin 3, nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x := by
    apply Finset.sum_congr rfl
    intro j _
    have hc := coreWeightOperator_directionalDerivative_commute hO hD
      (besselWeight 1) (coordinateDirection j)
    have he := congrArg
      (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x) hc.eq
    change coreWeightOperator hO hD (besselWeight 1)
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x =
      coreDirectionalDerivative hO hD (coordinateDirection j)
        (coreWeightOperator hO hD (besselWeight 1) F) x at he
    change modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (coreDirectionalDerivative hO hD (coordinateDirection j)
          (coreWeightOperator hO hD (besselWeight 1) F) x) =
      modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight 1)
          (coreDirectionalDerivative hO hD (coordinateDirection j) F) x)
    exact congrArg (modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x)
      he.symm
  rw [hfirst] at hd
  have he := (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)
  rw [he]
  simp only [coreModelErrorAdjointAction, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, nativeW, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk, Submodule.coe_add, Submodule.coe_sum, Finset.sum_apply, Pi.add_apply]
  abel

lemma nativeUField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeUField hO hD hF g1 g2 hg1 L lam δ R p F =
      (coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F : R3 → SphereL2) := by
  funext x
  exact modelError_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
    (coreAmbientRepresentative hO hD F) x

lemma nativeUdagField_eq_coreAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F =
      (coreModelErrorAdjointAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F : R3 → SphereL2) := by
  funext x
  exact modelErrorAdjoint_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F
    (coreAmbientRepresentative hO hD F) x

def nativeU
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeUField hO hD hF g1 g2 hg1 L lam δ R p F, by
    rw [nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F]
    exact (coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeUField hO hD hF g1 g2 hg1 L lam δ R p (F+G) =
      nativeUField hO hD hF g1 g2 hg1 L lam δ R p F +
      nativeUField hO hD hF g1 g2 hg1 L lam δ R p G
    simp only [nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeUField hO hD hF g1 g2 hg1 L lam δ R p (c • F) =
      c • nativeUField hO hD hF g1 g2 hg1 L lam δ R p F
    simp only [nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

def nativeUdag
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F, by
    rw [nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F]
    exact (coreModelErrorAdjointAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p (F+G) =
      nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F +
      nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p G
    simp only [nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p (c • F) =
      c • nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F
    simp only [nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

lemma nativeUField_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    normalizedSecondModelError hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeUField hO hD hF g1 g2 hg1 L lam δ R p F x := by
  rw [modelError_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x]
  exact congrFun (nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).symm x

lemma nativeUdagField_representative
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    normalizedSecondModelErrorAdjoint hF hO hD g1 g2 hg1 L lam δ R p (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F x := by
  rw [modelErrorAdjoint_representative hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F r x]
  exact congrFun (nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F).symm x

theorem compact_nativeU_adjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR G x⟫_ℝ := by
  let K : Set R3 := tsupport (F : R3 → SphereL2) ∪ tsupport (G : R3 → SphereL2)
  have hK : IsCompact K := F.property.2.1.union G.property.2.1
  have hzF : ∀ x ∉ K, ∀ theta : UnitSphere, coreAmbientFunction hO hD F (x,theta.val) = 0 := by
    intro x hx theta
    exact representativeAmbient_zero_outside hO hD (coreAmbientRepresentative hO hD F)
      x theta.val (fun hxF => hx (Or.inl hxF))
  have hzG : ∀ x ∉ K, ∀ theta : UnitSphere, coreAmbientFunction hO hD G (x,theta.val) = 0 := by
    intro x hx theta
    exact representativeAmbient_zero_outside hO hD (coreAmbientRepresentative hO hD G)
      x theta.val (fun hxG => hx (Or.inr hxG))
  have h := compact_normalizedSecondModelError_adjoint
    hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR
    (coreAmbientFunction hO hD F) (coreAmbientFunction hO hD G)
    (contDiff_coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD G)
    K hK hzF hzG
  change (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeUField hO hD hF g1 g2 hg1 L lam δ R p F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p G x⟫_ℝ
  simpa only [nativeUField, nativeUdagField, ambientSphereL2_coreAmbientFunction hO hD] using h

theorem compact_nativeUZ_adjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪(nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
          nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, (nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR *
        nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) G x⟫_ℝ := by
  change (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR
        (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR G) x⟫_ℝ
  rw [compact_nativeU_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) G]
  exact compact_nativeZ_adjoint hO hD hF g1 hg1 L lam δ R p hδ hR F
    (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR G)

lemma nativeU_coefficient_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      ScalarBaseAdjoint.scalarSecondBase coordinateDirection
        (fun y => referenceRadius δ R p L y • referenceNormalizedPrincipalMatrix g1 g2 L lam y)
        (F : R3 → SphereL2) x +
      (∑ j : Fin 3, nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x) +
      nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  change nativeUField hO hD hF g1 g2 hg1 L lam δ R p F x = _
  rw [congrFun (nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F) x]
  simp only [coreModelErrorAction, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, Submodule.coe_add, Submodule.coe_sum,
    Finset.sum_apply, Pi.add_apply,
    coreModelPrincipal_apply hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR F x]

lemma nativeUdag_sub_coefficient_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x -
      nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      (∑ j : Fin 3, nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x) +
      nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  change nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F x -
    nativeUField hO hD hF g1 g2 hg1 L lam δ R p F x = _
  rw [congrFun (nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F) x,
    congrFun (nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F) x]
  simp only [coreModelErrorAdjointAction, LinearMap.add_apply, LinearMap.sum_apply,
    Module.End.mul_apply, Submodule.coe_add, Submodule.coe_sum, Finset.sum_apply, Pi.add_apply]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
