import Calderon.ActualFiniteHarmonicModelReferenceWeightedYRaw
import Calderon.ActualFiniteHarmonicModelGeneratorScalarExpansions
import Calderon.ActualFiniteHarmonicModelReferenceWeights

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDNormalizedCoefficient AmbientReferenceRaising PrincipalCommutator
  ReferenceDensityBounds NaturalAngularAdjoint ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev weightedYAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] weightedYAngularFunction

def nativeWeightedYAngularPart
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
        (directionalFDeriv (coordinateDirection j) (fun y => mu y*d j y))
        (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (hd j))) * coreDegree hO hD -
      (∑ s : Fin 3, ∑ t : Fin 3,
        coreScalar hO hD
          (directionalFDeriv (coordinateDirection j) (fun y => mu y*tau j s t y))
          (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (htau j s t))) *
          coreRotation hO hD s t))))

def nativeWeightedYScalarPart
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
    (∑ j : Fin 3, coreScalar hO hD
      (directionalFDeriv (coordinateDirection j) (fun y => mu y*sigma j y))
      (contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.mul (hsigma j)))))

def nativeWeightedYAngularPartMass
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField) (x : R3) : ℝ :=
  let mu := fun y : R3 => referenceDensityFamily g L (lam,y)
  |(mu x)⁻¹| * (∑ j : Fin 3,
    (|directionalFDeriv (coordinateDirection j) (fun y => mu y*nativeReferenceWeightedFirstDegreeCoefficient g L lam δ R p h j y) x|+
    (∑ s : Fin 3, ∑ t : Fin 3, |directionalFDeriv (coordinateDirection j)
      (fun y => mu y*nativeReferenceWeightedFirstRotationCoefficient g L lam δ R p h j s t y) x|)))

lemma nativeWeightedY_eq_scalar_add_angular
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) :
    nativeReferenceWeightedAdjointDerivativeRawAction hO hD g hg L lam δ R p h hh hδ hR =
      nativeWeightedYScalarPart hO hD g hg L lam δ R p h hh hδ hR+
      nativeWeightedYAngularPart hO hD g hg L lam δ R p h hh hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  unfold nativeReferenceWeightedAdjointDerivativeRawAction nativeWeightedYScalarPart nativeWeightedYAngularPart
  dsimp only
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.sum_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,Submodule.coe_sum,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,smul_add,smul_sub,Finset.smul_sum]
  module

lemma hasCoreScalarExpansionBound_nativeWeightedYAngularPart
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeWeightedYAngularPart hO hD g hg L lam δ R p h hh hδ hR) x
      (nativeWeightedYAngularPartMass g L lam δ R p h x) := by
  unfold nativeWeightedYAngularPart nativeWeightedYAngularPartMass
  dsimp only
  have hn (B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) : (-1 : ℝ) • B = -B := neg_one_smul ℝ B
  rw [hn]
  apply hasCoreScalarExpansionBound_neg hO hD
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro j _
  apply hasCoreScalarExpansionBound_sub hO hD
  · exact hasCoreScalarExpansionBound_single hO hD _ (Sum.inr (Sum.inr (Sum.inr true))) _ _ x
  · apply hasCoreScalarExpansionBound_sum hO hD
    intro s _
    apply hasCoreScalarExpansionBound_sum hO hD
    intro t _
    exact hasCoreScalarExpansionBound_single hO hD _ (Sum.inr (Sum.inr (Sum.inl (s,t)))) _ _ x

lemma commute_nativeWeightedYScalarPart
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R)
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (hA : ScalarCentral hO hD A) :
    Commute A (nativeWeightedYScalarPart hO hD g hg L lam δ R p h hh hδ hR) := by
  unfold nativeWeightedYScalarPart
  dsimp only
  have hn (B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) : (-1 : ℝ) • B = -B := neg_one_smul ℝ B
  rw [hn]
  have hm (B C : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
      (hB : Commute A B) (hC : Commute A C) : Commute A (-(B*C)) := by
    have he := (hB.mul_right hC).eq
    change A*(-(B*C))=(-(B*C))*A
    apply LinearMap.ext
    intro F
    change A (-((B*C) F)) = -((B*C) (A F))
    rw [map_neg]
    exact congrArg Neg.neg (congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F) he)
  apply hm
  · exact hA _ _
  · apply Commute.sum_right
    intro j _
    exact hA _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
