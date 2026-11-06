import Calderon.ActualFiniteHarmonicModelRaisingCommute
import Calderon.ActualFiniteHarmonicModelRotationLieCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore SpectralWeightedGraph
  SpectralCoreRegularity HarmonicDerivativeOperator SmoothSphereRotationProjection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularCommutingPairsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularCommutingPairsFunction

lemma coreDerivative_commute (hF : SphereFischerInner) (a b : Fin 3) :
    Commute (coreDerivative hO hD hF a) (coreDerivative hO hD hF b) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change coreDerivative hO hD hF a (coreDerivative hO hD hF b F) x =
    coreDerivative hO hD hF b (coreDerivative hO hD hF a F) x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreDerivative hO hD hF a (coreDerivative hO hD hF b F) x) =
    sphereHarmonicCoordinate hO hD k (coreDerivative hO hD hF b (coreDerivative hO hD hF a F) x)
  rw [coreDerivative_graph hO hD hF a (coreDerivative hO hD hF b F) x k,
    coreDerivative_graph hO hD hF b (coreDerivative hO hD hF a F) x k,
    coreDerivative_graph hO hD hF b F x (k+1),coreDerivative_graph hO hD hF a F x (k+1)]
  exact harmonicDerivative_composition_commute hF k a b _

lemma coreDegree_coreRotation_commute (a b : Fin 3) :
    Commute (coreDegree hO hD) (coreRotation hO hD a b) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change coreDegree hO hD (coreRotation hO hD a b F) x =
    coreRotation hO hD a b (coreDegree hO hD F) x
  have hd (U : smoothCompactFiniteSphereCore hO hD) (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (coreDegree hO hD U x) =
        (k : ℝ) • sphereHarmonicCoordinate hO hD k (U x) :=
    coreWeightOperator_graph hO hD (fun k => (k : ℝ)) U x k
  have hr (U : smoothCompactFiniteSphereCore hO hD) (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (coreRotation hO hD a b U x) =
        harmonicSphereRotation k a b (sphereHarmonicCoordinate hO hD k (U x)) :=
    coreBlockOperator_coordinate hO hD (fun k => harmonicSphereRotation k a b) U x k
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreDegree hO hD (coreRotation hO hD a b F) x) =
    sphereHarmonicCoordinate hO hD k (coreRotation hO hD a b (coreDegree hO hD F) x)
  rw [hd,hr,hr,hd,map_smul]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
