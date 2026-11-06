import Calderon.ActualFiniteHarmonicModelHorizontalProfileRepresentative
import Calderon.ActualFiniteHarmonicModelFullErrorHorizontalEnergy
import Calderon.AmbientReferenceCoercivity

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph
  SmoothSphereFields AmbientReferenceRaising AmbientReferenceCoercivity ActualReferenceFullAdjunction
  ReferenceDensityBounds ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceEnergyRepresentativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceEnergyRepresentativeFunction

lemma nativeReferenceRaising_representative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeRaising hF hO hD g hg L lam (referenceLogRadius δ R p L)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      nativeT hO hD hF g hg L lam δ R p hδ hR F x := by
  exact nativeTField_representative hO hD hF g hg L lam δ R p hδ hR F r x

lemma nativeReferenceLowering_representative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeLowering hF hO hD g hg L lam (referenceLogRadius δ R p L)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      nativeTdag hO hD hF g hg L lam δ R p hδ hR F x+nativeZ hO hD hF g hg L lam δ R p hδ hR F x := by
  have he := ActualReferenceDecomposition.referenceAllModeLowering_sub_adjointExpression hF hO hD g hg L lam (fun y => Real.log (referenceRadius δ R p L y))
    (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x
  have ha := referenceAdjoint_representative hO hD hF g hg L lam δ R p hδ hR F r x
  rw [← nativeTdag_eq_coreReferenceAdjointAction hO hD hF g hg L lam δ R p hδ hR] at ha
  have hz := nativeZField_representative hO hD hF g hg L lam δ R p hδ hR F r x
  have he' := sub_eq_iff_eq_add.mp he
  rw [ha,hz] at he'
  change referenceAllModeLowering hF hO hD g hg L lam (fun y => Real.log (referenceRadius δ R p L y))
    (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
    nativeTdag hO hD hF g hg L lam δ R p hδ hR F x+nativeZField hO hD hF g hg L lam δ R p F x
  exact he'.trans (add_comm _ _)

lemma referenceAllModeRaisingEnergy_representative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) :
    referenceAllModeRaisingEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) =
      ∫ x : R3, referenceDensityFamily g L (lam,x)*‖nativeT hO hD hF g hg L lam δ R p hδ hR F x‖^2 := by
  unfold referenceAllModeRaisingEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun y : SphereL2 => referenceDensityFamily g L (lam,x)*‖y‖^2)
    (nativeReferenceRaising_representative hO hD hF g hg L lam δ R p hδ hR F r x))

lemma referenceAllModeLoweringEnergy_representative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) :
    referenceAllModeLoweringEnergy hF hO hD g hg L lam (referenceLogRadius δ R p L)
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) =
      ∫ x : R3, referenceDensityFamily g L (lam,x)*
        ‖nativeTdag hO hD hF g hg L lam δ R p hδ hR F x+nativeZ hO hD hF g hg L lam δ R p hδ hR F x‖^2 := by
  unfold referenceAllModeLoweringEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun y : SphereL2 => referenceDensityFamily g L (lam,x)*‖y‖^2)
    (nativeReferenceLowering_representative hO hD hF g hg L lam δ R p hδ hR F r x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
