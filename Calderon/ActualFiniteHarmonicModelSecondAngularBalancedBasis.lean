import Calderon.ActualFiniteHarmonicModelHalfShiftIdentities
import Calderon.ActualReferenceDDSpectralTransport

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualNormalizedSphereRotation ActualReferenceDDSpectralTransport SectionFiveErrorForms SpectralCoreRegularity
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWBalancedBasisFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWBalancedBasisFunction
lemma normalizedDerivative_second_weight_inner_threehalf_half
    (hF : SphereFischerInner) (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪balancedDerivative hF hO hD i (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hUH : (U x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x
  have hU : coreDerivative hO hD hF i U x = normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  have ht := balancedDerivative_inner_realization hF hO hD i (U x)
    (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) (coreDerivative hO hD hF i U x)
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    hUH (coreDerivative_graph hO hD hF i U x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  rw [hU] at ht
  exact ht


lemma normalizedRaising_second_weight_inner_threehalf_half
    (hF : SphereFischerInner) (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight 2) F x),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD i (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hUH : (U x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x
  have hU : coreRaising hO hD hF i U x = normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 2) F x) := by
    change normalizedRaising hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x) = _
    rw [coreWeight_one_twice_apply hO hD F x]
  have ht := balancedRaising_inner_realization hF hO hD i (U x)
    (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) (coreRaising hO hD hF i U x)
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    hUH (coreRaising_graph hO hD hF i U x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  rw [hU] at ht
  exact ht


lemma normalizedRotation_derivative_shift_inner_threehalf_half
    (hF : SphereFischerInner) (a b c : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedRotation hO hD b c (normalizedDerivative hF hO hD a
        (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)),G x⟫_ℝ =
      ⟪normalizedRotation hO hD b c (balancedDerivative hF hO hD a
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x - coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let S : smoothCompactFiniteSphereCore hO hD := coreDerivative hO hD hF a F
  have hBetween :
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x,
        coreWeightOperator hO hD (besselWeight 1) S x) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) S x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) S x) k,
      smul_smul,← besselWeight_add]
    norm_num
  have ha := preservesSphereSpectralGraphs_normalizedRotation hO hD b c (besselWeight (1/2 : ℝ))
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x)
    (coreWeightOperator hO hD (besselWeight 1) S x) hBetween
  have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ))
    (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x))
    (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 1) S x))
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    ha (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  simpa only [S,coreWeight_one_derivative_apply_eq_normalized_shift,
    coreWeight_half_derivative_apply_eq_balanced_shift] using ht


lemma normalizedRaising_rotation_second_weight_inner_threehalf_half
    (hF : SphereFischerInner) (a b c : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedRaising hF hO hD a (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 2) F x)),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x)),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let S : smoothCompactFiniteSphereCore hO hD := coreRotation hO hD b c F
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hrot : S x = normalizedRotation hO hD b c (U x) :=
    coreRotation_apply_eq_normalizedRotation hO hD b c F x
  have hBetween1 : (U x,coreWeightOperator hO hD (besselWeight 2) F x) ∈
      sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) U x
  have hBetweenHalf : (U x,coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈
      sphereBesselGraph hO hD (1/2 : ℝ) := by
    rw [← coreWeight_half_one_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x
  have hW1 : coreWeightOperator hO hD (besselWeight 1) S x =
      normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight 2) F x) := by
    have ha := preservesSphereSpectralGraphs_normalizedRotation hO hD b c (besselWeight 1)
      (U x) (coreWeightOperator hO hD (besselWeight 2) F x) hBetween1
    have hw := coreWeightOperator_graph hO hD (besselWeight 1) S x
    rw [hrot] at hw
    exact spectralGraph_output_unique hO hD (besselWeight 1) (normalizedRotation hO hD b c (U x)) _ _ hw ha
  have hWH : coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x =
      normalizedRotation hO hD b c (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) := by
    have ha := preservesSphereSpectralGraphs_normalizedRotation hO hD b c (besselWeight (1/2 : ℝ))
      (U x) (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) hBetweenHalf
    have hw := coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) S x
    rw [hrot] at hw
    exact spectralGraph_output_unique hO hD (besselWeight (1/2 : ℝ)) (normalizedRotation hO hD b c (U x)) _ _ hw ha
  have ht := balancedRaising_inner_realization hF hO hD a (S x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x) (coreRaising hO hD hF a S x)
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) S x)
    (coreRaising_graph hO hD hF a S x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  change ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) S x),G x⟫_ℝ =
    ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x),
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ at ht
  rw [hW1,hWH] at ht
  exact ht


lemma normalizedDerivative_double_shift_inner_threehalf_half
    (hF : SphereFischerInner) (a b : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedDerivative hF hO hD b (normalizedDerivative hF hO hD a
        (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)),G x⟫_ℝ =
      ⟪balancedDerivative hF hO hD b (balancedDerivative hF hO hD a
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x - coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let S : smoothCompactFiniteSphereCore hO hD := coreDerivative hO hD hF a F
  have ht := balancedDerivative_inner_realization hF hO hD b (S x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x) (coreDerivative hO hD hF b S x)
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) S x)
    (coreDerivative_graph hO hD hF b S x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  change ⟪normalizedDerivative hF hO hD b (coreWeightOperator hO hD (besselWeight 1) S x),G x⟫_ℝ =
    ⟪balancedDerivative hF hO hD b (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x),
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ at ht
  simpa only [S,coreWeight_one_derivative_apply_eq_normalized_shift,
    coreWeight_half_derivative_apply_eq_balanced_shift] using ht


lemma normalizedRaising_double_shift_inner_threehalf_half
    (hF : SphereFischerInner) (a b : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪normalizedRaising hF hO hD a (normalizedRaising hF hO hD b
        (coreWeightOperator hO hD (besselWeight 2) F x + coreWeightOperator hO hD (besselWeight 1) F x)),G x⟫_ℝ =
      ⟪balancedRaising hF hO hD a (balancedRaising hF hO hD b
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x + coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x)),coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  let S : smoothCompactFiniteSphereCore hO hD := coreRaising hO hD hF b F
  have ht := balancedRaising_inner_realization hF hO hD a (S x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x) (coreRaising hO hD hF a S x)
    (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) S x)
    (coreRaising_graph hO hD hF a S x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  change ⟪normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) S x),G x⟫_ℝ =
    ⟪balancedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) S x),
      coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ at ht
  simpa only [S,coreWeight_one_raising_apply_eq_normalized_shift,
    coreWeight_half_raising_apply_eq_balanced_shift] using ht

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
