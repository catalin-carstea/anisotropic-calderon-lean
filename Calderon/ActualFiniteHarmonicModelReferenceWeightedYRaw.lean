import Calderon.ActualFiniteHarmonicModelReferenceWeightedFirstRotation
import Calderon.ActualFiniteHarmonicModelReferenceWeights

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDNormalizedCoefficient AmbientReferenceRaising PrincipalCommutator
  ReferenceDensityBounds NaturalAngularAdjoint ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeReferenceWeightedYFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeReferenceWeightedYFunction

def nativeReferenceWeightedAdjointDerivativeRawAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := by
  let mu := fun y : R3 => referenceDensityFamily g L (lam,y)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have hmui : ContDiff ℝ ∞ (fun y : R3 => (mu y)⁻¹) :=
    (contDiff_referenceDensityFamily_inv g hg L).comp (contDiff_const.prodMk contDiff_id)
  let sigma (j : Fin 3) := nativeReferenceWeightedFirstScalarCoefficient g L lam δ R p h j
  let d (j : Fin 3) := nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j
  let tau (j s t : Fin 3) := nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t
  have hsigma (j : Fin 3) : ContDiff ℝ ∞ (sigma j) :=
    contDiff_nativeReferenceWeightedFirstScalarCoefficient g hg L lam δ R p h hh hδ hR j
  have hd (j : Fin 3) : ContDiff ℝ ∞ (d j) :=
    contDiff_nativeReferenceWeightedFirstDegreeCoefficient g hg L lam δ R p h hh hδ hR j
  have htau (j s t : Fin 3) : ContDiff ℝ ∞ (tau j s t) :=
    contDiff_nativeReferenceWeightedFirstRotationCoefficient g hg L lam δ R p h hh hδ hR j s t
  exact (-1 : ℝ) • (coreScalar hO hD (fun y => (mu y)⁻¹) hmui *
    (∑ j : Fin 3, (
      coreScalar hO hD
        (directionalFDeriv (coordinateDirection j) (fun y => mu y*sigma j y))
        (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (hsigma j))) +
      coreScalar hO hD
        (directionalFDeriv (coordinateDirection j) (fun y => mu y*d j y))
        (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (hd j))) * coreDegree hO hD -
      (∑ s : Fin 3, ∑ t : Fin 3,
        coreScalar hO hD
          (directionalFDeriv (coordinateDirection j) (fun y => mu y*tau j s t y))
          (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (htau j s t))) *
          coreRotation hO hD s t))))

lemma nativeReferenceWeightedAdjointDerivativeRawAction_scalarCentral
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) :
    ScalarCentral hO hD (nativeReferenceWeightedAdjointDerivativeRawAction hO hD g hg L lam δ R p h hh hδ hR) := by
  unfold nativeReferenceWeightedAdjointDerivativeRawAction
  dsimp only
  apply scalarCentral_smul hO hD
  apply scalarCentral_mul hO hD
  · exact scalarCentral_coreScalar hO hD _ _
  · apply scalarCentral_sum hO hD Finset.univ
    intro j hj
    apply scalarCentral_sub hO hD
    · apply scalarCentral_add hO hD
      · exact scalarCentral_coreScalar hO hD _ _
      · exact scalarCentral_mul hO hD _ _
          (scalarCentral_coreScalar hO hD _ _)
          (scalarCentral_coreWeightOperator hO hD (fun k => (k : ℝ)))
    · apply scalarCentral_sum hO hD Finset.univ
      intro s hs
      apply scalarCentral_sum hO hD Finset.univ
      intro t ht
      exact scalarCentral_mul hO hD _ _
        (scalarCentral_coreScalar hO hD _ _)
        (scalarCentral_coreRotation hO hD s t)

lemma weightedAngularAdjointDerivative_referenceWeightedFirst_coreWeight_two_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let mu := fun y : R3 => referenceDensityFamily g L (lam,y)
    ((-(mu x)⁻¹) • (∑ j : Fin 3,
      (weightedAngularAdjointDerivative (coordinateDirection j) mu
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g hg L lam δ R p h j) x).comp
        (inverseDegreeMultiplier hO hD)))
      (coreWeightOperator hO hD (besselWeight 2) F x) =
      nativeReferenceWeightedAdjointDerivativeRawAction hO hD g hg L lam δ R p h hh hδ hR F x := by
  dsimp only
  have hi : inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 2) F x) =
      coreWeightOperator hO hD (besselWeight 1) F x := by
    have hUV : (coreWeightOperator hO hD (besselWeight 1) F x,
        coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
      rw [← coreWeight_one_twice_apply hO hD F x]
      exact coreWeightOperator_graph hO hD (besselWeight 1)
        (coreWeightOperator hO hD (besselWeight 1) F) x
    exact inverseDegreeMultiplier_of_besselGraph hO hD _ _ hUV
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  rw [hi]
  simp_rw [weightedAngularAdjointDerivative_referenceWeightedFirst_coreWeight_one_apply
    hO hD g hg L lam δ R p h hh hδ hR]
  unfold nativeReferenceWeightedAdjointDerivativeRawAction
  dsimp only
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.sub_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_smul,Submodule.coe_sum,Submodule.coe_add,Submodule.coe_sub,
    Pi.smul_apply,Pi.add_apply,Pi.sub_apply,Finset.sum_apply,smul_smul,neg_one_mul]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
