import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.AmbientReferenceProfileEnergy

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient SpectralWeightedGraph
  SmoothSphereFields AmbientReferenceRaising AmbientReferenceProfileEnergy FourTermProfileEnergy
  SectionFiveErrorForms HarmonicProjectedCoercivity ReferenceWeightedApproximation ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev horizontalRepresentativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] horizontalRepresentativeFunction

lemma coreReferenceHorizontalBessel_real_representative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam s : ℝ) (hs : s ≤ 2) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceHorizontalBesselField hO hD g hg L lam s hs a
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      coreWeightOperator hO hD (besselWeight s) (coreReferenceHorizontal hO hD g hg L lam a F) x := by
  apply spectralGraph_output_unique hO hD (besselWeight s) (coreReferenceHorizontal hO hD g hg L lam a F x)
  · simpa only [SpectralWeightedGraph.sphereBesselGraph,coreReferenceHorizontal_representative hO hD g hg L lam a F r x] using
      referenceHorizontalBesselField_graph hO hD g hg L lam s hs a
        (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x
  · exact coreWeightOperator_graph hO hD (besselWeight s) (coreReferenceHorizontal hO hD g hg L lam a F) x

lemma referenceAllModeProfileEnergyDensity_representative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) (x : R3) :
    referenceAllModeProfileEnergyDensity hO hD g hg lam δ R L p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) x =
      finiteCoreReferenceProfileEnergy hO hD g hg L lam (actualReferenceBeta g L lam δ R p x) F x := by
  unfold referenceAllModeProfileEnergyDensity fourTermEnergyDensity finiteCoreReferenceProfileEnergy sourceNormSquareIntegrand
  simp_rw [coreReferenceHorizontal_representative hO hD g hg L lam,
    coreReferenceHorizontalBessel_real_representative hO hD g hg L lam (1/2:ℝ) (by norm_num),
    ← coreWeightOperator_eq_ambientBesselField hO hD F r 1 (by norm_num) x,
    ← coreWeightOperator_eq_ambientBesselField hO hD F r (3/2:ℝ) (by norm_num) x]
  rfl

lemma referenceAllModeProfileEnergy_representative
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam δ R L : ℝ) (p : ℕ)
    (F : smoothCompactFiniteSphereCore hO hD) (r : FiniteHarmonicAmbientRepresentative hO hD F) :
    referenceAllModeProfileEnergy hO hD g hg lam δ R L p
      (representativeAmbient hO hD r) (contDiff_representativeAmbient hO hD r) =
      ∫ x : R3, referenceDensityFamily g L (lam,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L lam (actualReferenceBeta g L lam δ R p x) F x := by
  unfold referenceAllModeProfileEnergy
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun y : ℝ => referenceDensityFamily g L (lam,x)*y)
    (referenceAllModeProfileEnergyDensity_representative hO hD g hg lam δ R L p F r x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
