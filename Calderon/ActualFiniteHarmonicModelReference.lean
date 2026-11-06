import Calderon.ActualFiniteHarmonicAmbient
import Calderon.ActualFiniteHarmonicModelDefect
import Calderon.ActualNormalizedSecondModelDefectCoefficients
import Calderon.ActualReferenceConnectionAngular
import Calderon.ActualReferenceDecomposition
import Calderon.ActualReferenceAdjointDecomposition
import Calderon.ActualReferenceParallelRaising

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph SmoothSphereFields AmbientAngularShift AmbientReferenceRaising
  ActualReferenceDecomposition ActualReferenceConnectionAngular ActualPhysicalMixedProfile
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelCoefficients
  ActualNormalizedSecondModelDefectCoefficients ReferenceDensityBounds PrincipalCommutator
  NormalizedPrincipalMetric ConformalDepth

open SmoothMetricFrame MovingFrameConnection

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private abbrev nativeReferenceFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeReferenceFunction

def nativeTField
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  referenceAllModeRaising hF hO hD g1 hg1 L lam (fun y => Real.log (referenceRadius δ R p L y)) (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def nativeTdagField
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  referenceAllModeAdjointExpression hF hO hD g1 hg1 L lam
    (fun y => Real.log (referenceRadius δ R p L y))
    (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F)

def coreReferenceHorizontal
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  (∑ j : Fin 3, coreScalar hO hD
    (fun y => referenceMetricGramFrame g1 L (lam,y) a j)
    ((contDiff_piLp_apply (p := 2) (i := j) :
      ContDiff ℝ ∞ (fun v : R3 => v j)).comp
        (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)) *
      coreDirectionalDerivative hO hD (coordinateDirection j)) +
  (1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
    coreScalar hO hD
      (fun y => referenceFrameConnectionCoefficient g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) a) b c)
      (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
        g1 hg1 L lam _ (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a) b c) *
    coreRotation hO hD b c

lemma coreReferenceHorizontal_apply
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreReferenceHorizontal hO hD g1 hg1 L lam a F x =
      coreFrameHorizontalAction hO hD
        (fun y => referenceFrameConnectionCoefficient g1 L lam y
          (referenceMetricGramFrame g1 L (lam,y) a))
        (fun y => referenceMetricGramFrame g1 L (lam,y) a) F x := by
  simp only [coreReferenceHorizontal, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, coreScalar, coreDirectionalDerivative,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  unfold coreFrameHorizontalAction
  rw [fderiv_apply_eq_coordinate_sum]

lemma coreReferenceHorizontal_representative
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceHorizontalField g1 hg1 L lam a (representativeAmbient hO hD r)
      (contDiff_representativeAmbient hO hD r) x =
      coreReferenceHorizontal hO hD g1 hg1 L lam a F x := by
  rw [referenceHorizontalField_representative hO hD g1 hg1 L lam a F r x,
    coreReferenceHorizontal_apply hO hD g1 hg1 L lam a F x]

def coreReferenceInput
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (a : Fin 3) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreReferenceHorizontal hO hD g1 hg1 L lam a +
  coreScalar hO hD
    (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
    (contDiff_referenceFrameDerivative g1 hg1 L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)) * coreDegree hO hD

lemma coreReferenceInput_representative
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (a : Fin 3) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceWeightedInputField hO hD g1 hg1 L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y))
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreReferenceInput hO hD g1 hg1 L lam δ R p a hδ hR F x := by
  rw [referenceWeightedInputField_representative hO hD g1 hg1 L lam 1 a _ F r x,
    one_smul]
  simp only [coreReferenceInput, LinearMap.add_apply, Module.End.mul_apply, coreScalar,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_add, Pi.add_apply, coreReferenceHorizontal_apply]

lemma coreReferenceWeightedBessel_representative
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (a : Fin 3) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceWeightedBesselField hO hD g1 hg1 L lam 1 a
      (fun y => Real.log (referenceRadius δ R p L y))
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreWeightOperator hO hD (besselWeight 1)
        (coreReferenceInput hO hD g1 hg1 L lam δ R p a hδ hR F) x := by
  apply spectralGraph_output_unique hO hD (besselWeight 1)
    (coreReferenceInput hO hD g1 hg1 L lam δ R p a hδ hR F x)
  · simpa only [SpectralWeightedGraph.sphereBesselGraph,
      coreReferenceInput_representative hO hD g1 hg1 L lam δ R p a hδ hR F r x] using
      referenceWeightedBesselField_graph hO hD g1 hg1 L lam 1 a
        (fun y => Real.log (referenceRadius δ R p L y))
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x
  · exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreReferenceInput hO hD g1 hg1 L lam δ R p a hδ hR F) x

lemma coreReferenceHorizontalBessel_representative
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceHorizontalBesselField hO hD g1 hg1 L lam 1 (by norm_num) a
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreWeightOperator hO hD (besselWeight 1)
        (coreReferenceHorizontal hO hD g1 hg1 L lam a F) x := by
  apply spectralGraph_output_unique hO hD (besselWeight 1)
    (coreReferenceHorizontal hO hD g1 hg1 L lam a F x)
  · simpa only [SpectralWeightedGraph.sphereBesselGraph,
      coreReferenceHorizontal_representative hO hD g1 hg1 L lam a F r x] using
      referenceHorizontalBesselField_graph hO hD g1 hg1 L lam 1 (by norm_num) a
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x
  · exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreReferenceHorizontal hO hD g1 hg1 L lam a F) x

def coreReferenceRaisingAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreRaising hO hD hF a *
    coreReferenceInput hO hD g1 hg1 L lam δ R p a hδ hR

def coreReferenceAdjointAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreNormalizedDerivative hO hD hF a *
    ((-1 : ℝ) • (coreWeightOperator hO hD (besselWeight 1) *
      coreReferenceHorizontal hO hD g1 hg1 L lam a) +
    coreScalar hO hD
      (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
      (contDiff_referenceFrameDerivative g1 hg1 L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)) *
      (coreWeightOperator hO hD (besselWeight 2) -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1)))

lemma referenceRaising_representative
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeRaising hF hO hD g1 hg1 L lam
      (fun y => Real.log (referenceRadius δ R p L y))
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreReferenceRaisingAction hO hD hF g1 hg1 L lam δ R p hδ hR F x := by
  simp only [referenceAllModeRaising, coreReferenceRaisingAction,
    LinearMap.sum_apply, Module.End.mul_apply, coreRaising, coreNormalizedRaising,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [coreReferenceWeightedBessel_representative hO hD g1 hg1 L lam δ R p a hδ hR F r x]

lemma referenceAdjoint_representative
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD)
    (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeAdjointExpression hF hO hD g1 hg1 L lam
      (fun y => Real.log (referenceRadius δ R p L y))
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreReferenceAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR F x := by
  simp only [referenceAllModeAdjointExpression, coreReferenceAdjointAction,
    LinearMap.sum_apply, Module.End.mul_apply, coreNormalizedDerivative, coreScalar,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk,
    Submodule.coe_sum, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [coreReferenceHorizontalBessel_representative hO hD g1 hg1 L lam a F r x,
    ← coreWeightOperator_eq_ambientBesselField hO hD F r 2 (by norm_num) x,
    ← coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) x]

lemma nativeTField_eq_coreAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeTField hO hD hF g1 hg1 L lam δ R p F =
      (coreReferenceRaisingAction hO hD hF g1 hg1 L lam δ R p hδ hR F : R3 → SphereL2) := by
  funext x
  exact referenceRaising_representative hO hD hF g1 hg1 L lam δ R p hδ hR F
    (coreAmbientRepresentative hO hD F) x

lemma nativeTdagField_eq_coreAction
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeTdagField hO hD hF g1 hg1 L lam δ R p F =
      (coreReferenceAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR F : R3 → SphereL2) := by
  funext x
  exact referenceAdjoint_representative hO hD hF g1 hg1 L lam δ R p hδ hR F
    (coreAmbientRepresentative hO hD F) x

def nativeT
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeTField hO hD hF g1 hg1 L lam δ R p F, by
    rw [nativeTField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F]
    exact (coreReferenceRaisingAction hO hD hF g1 hg1 L lam δ R p hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeTField hO hD hF g1 hg1 L lam δ R p (F+G) =
      nativeTField hO hD hF g1 hg1 L lam δ R p F +
      nativeTField hO hD hF g1 hg1 L lam δ R p G
    simp only [nativeTField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeTField hO hD hF g1 hg1 L lam δ R p (c • F) =
      c • nativeTField hO hD hF g1 hg1 L lam δ R p F
    simp only [nativeTField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

def nativeTdag
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) where
  toFun F := ⟨nativeTdagField hO hD hF g1 hg1 L lam δ R p F, by
    rw [nativeTdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F]
    exact (coreReferenceAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR F).property⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    change nativeTdagField hO hD hF g1 hg1 L lam δ R p (F+G) =
      nativeTdagField hO hD hF g1 hg1 L lam δ R p F +
      nativeTdagField hO hD hF g1 hg1 L lam δ R p G
    simp only [nativeTdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_add, Submodule.coe_add]
  map_smul' := by
    intro c F
    apply Subtype.ext
    change nativeTdagField hO hD hF g1 hg1 L lam δ R p (c • F) =
      c • nativeTdagField hO hD hF g1 hg1 L lam δ R p F
    simp only [nativeTdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR,
      map_smul, Submodule.coe_smul, RingHom.id_apply]

lemma nativeTField_representative
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeRaising hF hO hD g1 hg1 L lam (fun y => Real.log (referenceRadius δ R p L y)) (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x = nativeTField hO hD hF g1 hg1 L lam δ R p F x := by
  unfold nativeTField coreAmbientFunction
  rw [referenceRaising_representative hO hD hF g1 hg1 L lam δ R p hδ hR F r x,
    referenceRaising_representative hO hD hF g1 hg1 L lam δ R p hδ hR F
      (coreAmbientRepresentative hO hD F) x]

theorem compact_nativeT_adjoint
    (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeT hO hD hF g1 hg1 L lam δ R p hδ hR F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR G x⟫_ℝ := by
  have hK : IsCompact (tsupport (F : R3 → SphereL2)) := F.property.2.1
  have hJ : IsCompact (tsupport (G : R3 → SphereL2)) := G.property.2.1
  have hf := contDiff_log_referenceRadius_profile δ R L p hδ hR
  have h := ActualReferenceFullAdjunction.compact_referenceAllModeRaising_adjointExpression
    hF hO hD g1 hg1 L lam (fun y => Real.log (referenceRadius δ R p L y)) hf
    (coreAmbientFunction hO hD F) (coreAmbientFunction hO hD G)
    (contDiff_coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD G)
    (tsupport (F : R3 → SphereL2)) (tsupport (G : R3 → SphereL2)) hK hJ
    (fun x hx theta => representativeAmbient_zero_outside hO hD
      (coreAmbientRepresentative hO hD F) x theta.val hx)
    (fun x hx theta => representativeAmbient_zero_outside hO hD
      (coreAmbientRepresentative hO hD G) x theta.val hx)
  change (∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪nativeTField hO hD hF g1 hg1 L lam δ R p F x, G x⟫_ℝ) =
    ∫ x, referenceDensityFamily g1 L (lam,x) *
      ⟪F x, nativeTdagField hO hD hF g1 hg1 L lam δ R p G x⟫_ℝ
  simpa only [nativeTField, nativeTdagField,
    ambientSphereL2_coreAmbientFunction hO hD] using h

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
