import Calderon.ActualFiniteHarmonicModelReferenceWeights
import Calderon.ActualFiniteHarmonicCoreDerivative
import Calderon.ActualFiniteHarmonicCoreRaising

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity ActualFiniteHarmonicCore
  SpectralWeightedGraph BoundedAngularShift AngularShiftGraph PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeShiftWeightFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeShiftWeightFunction
lemma coreWeight_one_derivative_apply_eq_normalized_shift
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x =
      normalizedDerivative hF hO hD i
        (coreWeightOperator hO hD (besselWeight 2) F x -
          coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hshift : coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x =
      coreDerivative hO hD hF i U x - coreDerivative hO hD hF i F x := by
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext m
    rw [map_sub]
    change sphereHarmonicCoordinate hO hD m
        (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) =
      sphereHarmonicCoordinate hO hD m (coreDerivative hO hD hF i U x) -
        sphereHarmonicCoordinate hO hD m (coreDerivative hO hD hF i F x)
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) m,
      (coreDerivative_graph hO hD hF i F x) m,(coreDerivative_graph hO hD hF i U x) m,
      (coreWeightOperator_graph hO hD (besselWeight 1) F x) (m+1),map_smul]
    simp only [besselWeight,Real.rpow_one,Nat.cast_add,Nat.cast_one]
    module
  have hDU : coreDerivative hO hD hF i U x = normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  calc
    _ = coreDerivative hO hD hF i U x - coreDerivative hO hD hF i F x := hshift
    _ = normalizedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x) -
        normalizedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight 1) F x) := by rw [hDU]; rfl
    _ = _ := (map_sub (normalizedDerivative hF hO hD i) _ _).symm


lemma coreWeight_one_raising_apply_eq_normalized_shift
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x =
      normalizedRaising hF hO hD i
        (coreWeightOperator hO hD (besselWeight 2) F x +
          coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hshift : coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x =
      coreRaising hO hD hF i U x + coreRaising hO hD hF i F x := by
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    rw [map_add]
    change sphereHarmonicCoordinate hO hD k
        (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) =
      sphereHarmonicCoordinate hO hD k (coreRaising hO hD hF i U x) +
        sphereHarmonicCoordinate hO hD k (coreRaising hO hD hF i F x)
    cases k with
    | zero =>
      rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) 0,
        (coreRaising_graph hO hD hF i F x).1,(coreRaising_graph hO hD hF i U x).1]
      simp
    | succ m =>
      rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) (m+1),
        (coreRaising_graph hO hD hF i F x).2 m,(coreRaising_graph hO hD hF i U x).2 m,
        (coreWeightOperator_graph hO hD (besselWeight 1) F x) m,map_smul]
      simp only [besselWeight,Real.rpow_one,Nat.cast_add,Nat.cast_one]
      module
  have hRU : coreRaising hO hD hF i U x = normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  calc
    _ = coreRaising hO hD hF i U x + coreRaising hO hD hF i F x := hshift
    _ = normalizedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x) +
        normalizedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight 1) F x) := by rw [hRU]; rfl
    _ = _ := (map_add (normalizedRaising hF hO hD i) _ _).symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
