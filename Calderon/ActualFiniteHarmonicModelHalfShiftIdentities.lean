import Calderon.ActualFiniteHarmonicModelShiftWeights
import Calderon.ActualFiniteHarmonicModelReferenceZeroBalanced

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore SpectralWeightedGraph
  BoundedAngularShift BalancedAngularShift SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeHalfShiftIdentityFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeHalfShiftIdentityFunction
lemma coreWeight_half_derivative_apply_eq_balanced_shift
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x =
      balancedDerivative hF hO hD i
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x -
          coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hUH : (U x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x
  have h0 : halfDegreeMultiplier hO hD (coreDerivative hO hD hF i F x) =
      balancedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) :=
    (balancedDerivative_of_graph hF hO hD i (F x)
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) _
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreDerivative_graph hO hD hF i F x)).symm
  have h1 : halfDegreeMultiplier hO hD (coreDerivative hO hD hF i U x) =
      balancedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) :=
    (balancedDerivative_of_graph hF hO hD i (U x)
      (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) _ hUH
      (coreDerivative_graph hO hD hF i U x)).symm
  have hBetween :
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x,
        coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x) k,
      smul_smul,← besselWeight_add]
    norm_num
  have hW : halfDegreeMultiplier hO hD
      (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) =
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreDerivative hO hD hF i F) x :=
    halfDegreeMultiplier_of_positive_half_graph hO hD _ _ hBetween
  have hU : coreDerivative hO hD hF i U x = normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  have hShift : coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x =
      coreDerivative hO hD hF i U x - coreDerivative hO hD hF i F x := by
    calc
      _ = normalizedDerivative hF hO hD i
          (coreWeightOperator hO hD (besselWeight 2) F x -
            coreWeightOperator hO hD (besselWeight 1) F x) :=
        coreWeight_one_derivative_apply_eq_normalized_shift hO hD hF i F x
      _ = normalizedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x) -
          normalizedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight 1) F x) :=
        map_sub (normalizedDerivative hF hO hD i) _ _
      _ = _ := by rw [← hU]; rfl
  have he := congrArg (halfDegreeMultiplier hO hD) hShift
  rw [map_sub,hW,h1,h0] at he
  exact he.trans (map_sub (balancedDerivative hF hO hD i) _ _).symm


lemma coreWeight_half_raising_apply_eq_balanced_shift
    (hF : SphereFischerInner) (i : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x =
      balancedRaising hF hO hD i
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x +
          coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hUH : (U x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x
  have h0 : halfDegreeMultiplier hO hD (coreRaising hO hD hF i F x) =
      balancedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) :=
    (balancedRaising_of_graph hF hO hD i (F x)
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) _
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreRaising_graph hO hD hF i F x)).symm
  have h1 : halfDegreeMultiplier hO hD (coreRaising hO hD hF i U x) =
      balancedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) :=
    (balancedRaising_of_graph hF hO hD i (U x)
      (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) _ hUH
      (coreRaising_graph hO hD hF i U x)).symm
  have hBetween :
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x,
        coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x) k,
      smul_smul,← besselWeight_add]
    norm_num
  have hW : halfDegreeMultiplier hO hD
      (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x) =
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (coreRaising hO hD hF i F) x :=
    halfDegreeMultiplier_of_positive_half_graph hO hD _ _ hBetween
  have hU : coreRaising hO hD hF i U x = normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  have hShift : coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF i F) x =
      coreRaising hO hD hF i U x + coreRaising hO hD hF i F x := by
    calc
      _ = normalizedRaising hF hO hD i
          (coreWeightOperator hO hD (besselWeight 2) F x +
            coreWeightOperator hO hD (besselWeight 1) F x) :=
        coreWeight_one_raising_apply_eq_normalized_shift hO hD hF i F x
      _ = normalizedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x) +
          normalizedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight 1) F x) :=
        map_add (normalizedRaising hF hO hD i) _ _
      _ = _ := by rw [← hU]; rfl
  have he := congrArg (halfDegreeMultiplier hO hD) hShift
  rw [map_add,hW,h1,h0] at he
  exact he.trans (map_add (balancedRaising hF hO hD i) _ _).symm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
