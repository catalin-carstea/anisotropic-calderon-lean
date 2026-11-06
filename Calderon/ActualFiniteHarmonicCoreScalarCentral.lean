import Calderon.ActualFiniteHarmonicModelCoefficientCore
import Calderon.ActualFiniteHarmonicCore

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BoundedAngularShift AngularShiftGraph HarmonicDerivativeOperator PrincipalCommutator
  SmoothSphereRotationProjection ActualReferenceDDSpectralTransport

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev scalarCentralFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] scalarCentralFunction

def ScalarCentral (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) : Prop :=
  ∀ (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c), Commute A (coreScalar hO hD c hc)

lemma scalarCentral_add (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) (hB : ScalarCentral hO hD B) :
    ScalarCentral hO hD (A+B) := by
  intro c hc
  exact (hA c hc).add_left (hB c hc)

lemma scalarCentral_sub (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) (hB : ScalarCentral hO hD B) :
    ScalarCentral hO hD (A-B) := by
  intro c hc
  change (A-B) * coreScalar hO hD c hc = coreScalar hO hD c hc * (A-B)
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hAx := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) (hA c hc).eq
  have hBx := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) (hB c hc).eq
  change A (coreScalar hO hD c hc F) x = c x • A F x at hAx
  change B (coreScalar hO hD c hc F) x = c x • B F x at hBx
  change A (coreScalar hO hD c hc F) x - B (coreScalar hO hD c hc F) x =
    c x • (A F x-B F x)
  rw [hAx, hBx, smul_sub]

lemma scalarCentral_mul (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) (hB : ScalarCentral hO hD B) :
    ScalarCentral hO hD (A*B) := by
  intro c hc
  exact (hA c hc).mul_left (hB c hc)

lemma scalarCentral_smul (r : ℝ) (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A) : ScalarCentral hO hD (r • A) := by
  intro c hc
  exact (hA c hc).smul_left r

lemma scalarCentral_sum {ι : Type*} (s : Finset ι) (A : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ∀ i ∈ s, ScalarCentral hO hD (A i)) :
    ScalarCentral hO hD (∑ i ∈ s, A i) := by
  intro c hc
  exact Commute.sum_left s A (coreScalar hO hD c hc) (fun i hi => hA i hi c hc)

lemma scalarCentral_coreScalar (b : R3 → ℝ) (hb : ContDiff ℝ ∞ b) :
    ScalarCentral hO hD (coreScalar hO hD b hb) := by
  intro c hc
  change coreScalar hO hD b hb * coreScalar hO hD c hc =
    coreScalar hO hD c hc * coreScalar hO hD b hb
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change b x • (c x • F x) = c x • (b x • F x)
  exact smul_comm (b x) (c x) (F x)

lemma scalarCentral_coreBlockOperator (K : ∀ k, harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :
    ScalarCentral hO hD (coreBlockOperator hO hD K) := by
  intro c hc
  change coreBlockOperator hO hD K * coreScalar hO hD c hc =
    coreScalar hO hD c hc * coreBlockOperator hO hD K
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
      (coreBlockOperator hO hD K (coreScalar hO hD c hc F) x) =
    sphereHarmonicCoordinate hO hD k (c x • coreBlockOperator hO hD K F x)
  rw [coreBlockOperator_coordinate, map_smul, coreBlockOperator_coordinate]
  change K k (sphereHarmonicCoordinate hO hD k (c x • F x)) =
    c x • K k (sphereHarmonicCoordinate hO hD k (F x))
  rw [map_smul, map_smul]

lemma scalarCentral_coreWeightOperator (w : ℕ → ℝ) :
    ScalarCentral hO hD (coreWeightOperator hO hD w) := by
  exact scalarCentral_coreBlockOperator hO hD _

lemma scalarCentral_coreRotation (i j : Fin 3) :
    ScalarCentral hO hD (coreRotation hO hD i j) := by
  exact scalarCentral_coreBlockOperator hO hD _

lemma scalarCentral_coreNormalizedDerivative (hF : SphereFischerInner) (i : Fin 3) :
    ScalarCentral hO hD (coreNormalizedDerivative hO hD hF i) := by
  intro c hc
  change coreNormalizedDerivative hO hD hF i * coreScalar hO hD c hc =
    coreScalar hO hD c hc * coreNormalizedDerivative hO hD hF i
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change normalizedDerivative hF hO hD i (c x • F x) =
    c x • normalizedDerivative hF hO hD i (F x)
  exact map_smul (normalizedDerivative hF hO hD i) (c x) (F x)

lemma scalarCentral_coreNormalizedRaising (hF : SphereFischerInner) (i : Fin 3) :
    ScalarCentral hO hD (coreNormalizedRaising hO hD hF i) := by
  intro c hc
  change coreNormalizedRaising hO hD hF i * coreScalar hO hD c hc =
    coreScalar hO hD c hc * coreNormalizedRaising hO hD hF i
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change normalizedRaising hF hO hD i (c x • F x) =
    c x • normalizedRaising hF hO hD i (F x)
  exact map_smul (normalizedRaising hF hO hD i) (c x) (F x)

lemma scalarCentral_coreDerivative (hF : SphereFischerInner) (i : Fin 3) :
    ScalarCentral hO hD (coreDerivative hO hD hF i) := by
  exact scalarCentral_mul hO hD _ _
    (scalarCentral_coreNormalizedDerivative hO hD hF i)
    (scalarCentral_coreWeightOperator hO hD _)

lemma scalarCentral_coreRaising (hF : SphereFischerInner) (i : Fin 3) :
    ScalarCentral hO hD (coreRaising hO hD hF i) := by
  exact scalarCentral_mul hO hD _ _
    (scalarCentral_coreNormalizedRaising hO hD hF i)
    (scalarCentral_coreWeightOperator hO hD _)

lemma scalarCentral_coreCoefficientAction (A : R3 → SphereL2 →L[ℝ] SphereL2) (hA : ContDiff ℝ ∞ A)
    (hgraph : ∀ x, PreservesSphereSpectralGraphs hO hD (A x)) :
    ScalarCentral hO hD (coreCoefficientAction hO hD A hA hgraph) := by
  intro c hc
  change coreCoefficientAction hO hD A hA hgraph * coreScalar hO hD c hc =
    coreScalar hO hD c hc * coreCoefficientAction hO hD A hA hgraph
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change A x (c x • F x) = c x • A x (F x)
  exact map_smul (A x) (c x) (F x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
