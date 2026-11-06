import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore AngularShiftGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeDegreeShiftFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeDegreeShiftFunction
lemma coreDegree_raising_commutator
    (hF : SphereFischerInner) (a : Fin 3) :
    ActualModelCommutatorWords.commutator (coreDegree hO hD) (coreRaising hO hD hF a) =
      coreRaising hO hD hF a := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change coreDegree hO hD (coreRaising hO hD hF a F) x -
    coreRaising hO hD hF a (coreDegree hO hD F) x = coreRaising hO hD hF a F x
  have hd (U : smoothCompactFiniteSphereCore hO hD) (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (coreDegree hO hD U x) =
        (k : ℝ) • sphereHarmonicCoordinate hO hD k (U x) :=
    coreWeightOperator_graph hO hD (fun k => (k : ℝ)) U x k
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (coreDegree hO hD (coreRaising hO hD hF a F) x -
      coreRaising hO hD hF a (coreDegree hO hD F) x) =
    sphereHarmonicCoordinate hO hD k (coreRaising hO hD hF a F x)
  rw [map_sub]
  cases k with
  | zero =>
    rw [hd,(coreRaising_graph hO hD hF a F x).1,
      (coreRaising_graph hO hD hF a (coreDegree hO hD F) x).1]
    simp only [Nat.cast_zero,zero_smul,sub_zero]
  | succ k =>
    rw [hd,(coreRaising_graph hO hD hF a F x).2 k,
      (coreRaising_graph hO hD hF a (coreDegree hO hD F) x).2 k,hd,map_smul]
    rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

lemma coreDerivative_degree_commutator
    (hF : SphereFischerInner) (a : Fin 3) :
    ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreDegree hO hD) =
      coreDerivative hO hD hF a := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change coreDerivative hO hD hF a (coreDegree hO hD F) x -
    coreDegree hO hD (coreDerivative hO hD hF a F) x = coreDerivative hO hD hF a F x
  have hd (U : smoothCompactFiniteSphereCore hO hD) (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (coreDegree hO hD U x) =
        (k : ℝ) • sphereHarmonicCoordinate hO hD k (U x) :=
    coreWeightOperator_graph hO hD (fun k => (k : ℝ)) U x k
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (coreDerivative hO hD hF a (coreDegree hO hD F) x -
      coreDegree hO hD (coreDerivative hO hD hF a F) x) =
    sphereHarmonicCoordinate hO hD k (coreDerivative hO hD hF a F x)
  rw [map_sub,coreDerivative_graph hO hD hF a (coreDegree hO hD F) x k,hd,hd,
    coreDerivative_graph hO hD hF a F x k,map_smul]
  rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
