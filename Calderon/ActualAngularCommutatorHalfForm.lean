import Calderon.ActualAngularDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualAngularCommutatorHalfForm
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  ActualReferenceDDSpectralTransport ActualPhysicalPureAngular AngularDerivativeBesselField
  ActualAngularDerivativeRaisingCommutator

lemma preservesSphereSpectralGraphs_normalizedRaising_derivative
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) : PreservesSphereSpectralGraphs hO hD
      ((normalizedRaising hF hO hD j).comp (normalizedDerivative hF hO hD i)) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k
      (normalizedRaising hF hO hD j (normalizedDerivative hF hO hD i U)) =
    w k • sphereHarmonicCoordinate hO hD k
      (normalizedRaising hF hO hD j (normalizedDerivative hF hO hD i u))
  cases k with
  | zero =>
    have hz (v : SphereL2) : sphereHarmonicCoordinate hO hD 0
        (normalizedRaising hF hO hD j v) = 0 :=
      (normalizedRaisingOutput_graph hF hO hD j v).1
    rw [hz,hz,smul_zero]
  | succ m =>
    rw [normalizedRaising_derivative_coordinate,normalizedRaising_derivative_coordinate,hU (m+1)]
    simp only [map_smul,smul_smul]
    module

lemma preservesSphereSpectralGraphs_derivativeRaisingFirstMultiplier
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    PreservesSphereSpectralGraphs hO hD (derivativeRaisingFirstMultiplier hO hD) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k (derivativeRaisingFirstMultiplier hO hD U) =
    w k • sphereHarmonicCoordinate hO hD k (derivativeRaisingFirstMultiplier hO hD u)
  have hc (v : SphereL2) : sphereHarmonicCoordinate hO hD k
      (derivativeRaisingFirstMultiplier hO hD v) =
        derivativeRaisingFirstWeight k • sphereHarmonicCoordinate hO hD k v :=
    boundedSpectralMultiplier_mem hO hD derivativeRaisingFirstWeight 1 (by norm_num)
      abs_derivativeRaisingFirstWeight_le_one v k
  rw [hc U,hc u,hU k,smul_comm]

lemma preservesSphereSpectralGraphs_derivativeRaisingSecondMultiplier
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    PreservesSphereSpectralGraphs hO hD (derivativeRaisingSecondMultiplier hO hD) := by
  intro w u U hU k
  change sphereHarmonicCoordinate hO hD k (derivativeRaisingSecondMultiplier hO hD U) =
    w k • sphereHarmonicCoordinate hO hD k (derivativeRaisingSecondMultiplier hO hD u)
  have hc (v : SphereL2) : sphereHarmonicCoordinate hO hD k
      (derivativeRaisingSecondMultiplier hO hD v) =
        derivativeRaisingSecondWeight k • sphereHarmonicCoordinate hO hD k v :=
    boundedSpectralMultiplier_mem hO hD derivativeRaisingSecondWeight 2 (by norm_num)
      abs_derivativeRaisingSecondWeight_le_two v k
  rw [hc U,hc u,hU k,smul_comm]

theorem preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) : PreservesSphereSpectralGraphs hO hD
      (normalizedDerivativeRaisingCommutator hF hO hD i j) := by
  unfold normalizedDerivativeRaisingCommutator
  apply preservesSphereSpectralGraphs_sub
  · apply preservesSphereSpectralGraphs_add
    · by_cases hij : i=j
      · simp only [hij,ite_true]
        exact preservesSphereSpectralGraphs_add hO hD _ _
          (preservesSphereSpectralGraphs_smul hO hD _ _ (preservesSphereSpectralGraphs_id hO hD))
          (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
      · simp only [hij,ite_false]
        intro w u U hU k
        simp
    · exact preservesSphereSpectralGraphs_comp hO hD _ _
        (preservesSphereSpectralGraphs_derivativeRaisingFirstMultiplier hO hD)
        (preservesSphereSpectralGraphs_normalizedRaising_derivative hF hO hD i j)
  · exact preservesSphereSpectralGraphs_comp hO hD _ _
      (preservesSphereSpectralGraphs_derivativeRaisingSecondMultiplier hO hD)
      (preservesSphereSpectralGraphs_normalizedRaising_derivative hF hO hD j i)

theorem ambientDerivativeRaising_commutator_inner_half
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (G V : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hV : ContDiff ℝ ∞ V) (x : R3) :
    ⟪normalizedDerivative hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x) -
      normalizedRaising hF hO hD j (ambientDerivativeBesselField hF hO hD i G hG x),ambientSphereL2 V hV x⟫_ℝ =
    ⟪normalizedDerivativeRaisingCommutator hF hO hD i j
      (ambientBesselField hO hD (1/2) (by norm_num) G hG x),
      ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ := by
  rw [ambientDerivativeRaising_commutator_eq_normalized]
  have hGhalf :
      (ambientBesselField hO hD (1/2) (by norm_num) G hG x,
        ambientBesselField hO hD 1 (by norm_num) G hG x) ∈ sphereBesselGraph hO hD (1/2) := by
    convert ambientBesselField_between_graph hO hD (1/2) 1 (by norm_num) (by norm_num) G hG x using 1 <;> norm_num
  exact spectralGraph_inner_symm hO hD (besselWeight (1/2)) _ _ _ _
    (preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hF hO hD i j
      (besselWeight (1/2)) _ _ hGhalf)
    (ambientBesselField_graph hO hD (1/2) (by norm_num) V hV x)

theorem abs_ambientDerivativeRaising_commutator_inner_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (G V : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (hV : ContDiff ℝ ∞ V) (x : R3) :
    |⟪normalizedDerivative hF hO hD i (ambientRaisingBesselField hF hO hD j G hG x) -
      normalizedRaising hF hO hD j (ambientDerivativeBesselField hF hO hD i G hG x),ambientSphereL2 V hV x⟫_ℝ| ≤
      15*‖ambientBesselField hO hD (1/2) (by norm_num) G hG x‖*
        ‖ambientBesselField hO hD (1/2) (by norm_num) V hV x‖ := by
  rw [ambientDerivativeRaising_commutator_inner_half]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((normalizedDerivativeRaisingCommutator hF hO hD i j).le_of_opNorm_le
        (norm_normalizedDerivativeRaisingCommutator_le hF hO hD i j) _)
      (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualAngularCommutatorHalfForm
