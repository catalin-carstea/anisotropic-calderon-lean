import Calderon.ActualFiniteHarmonicModelShiftWeights
import Calderon.ActualAngularDerivativeRaisingCommutator
import Calderon.ActualFiniteHarmonicAmbient

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient BoundedAngularShift BoundedSpectralMultiplier
  ActualAngularDerivativeRaisingCommutator ActualReferenceDDSpectralTransport AngularShiftGraph
  ActualPhysicalPureAngular AmbientAngularShift AngularDerivativeBesselField SmoothSphereFields SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeDRCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeDRCommutatorFunction
lemma preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator
    (hF : SphereFischerInner) (i j : Fin 3) :
    PreservesSphereSpectralGraphs hO hD (normalizedDerivativeRaisingCommutator hF hO hD i j) := by
  have hMultiplier (m : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hm : ∀ k, |m k| ≤ M) :
      PreservesSphereSpectralGraphs hO hD (boundedSpectralMultiplier hO hD m M hM hm) := by
    intro w u U hU k
    rw [boundedSpectralMultiplier_mem hO hD m M hM hm U k,
      boundedSpectralMultiplier_mem hO hD m M hM hm u k,hU k]
    simp only [smul_smul]
    rw [mul_comm]
  have hRD (a b : Fin 3) : PreservesSphereSpectralGraphs hO hD
      ((normalizedRaising hF hO hD b).comp (normalizedDerivative hF hO hD a)) := by
    have hz (u : SphereL2) : sphereHarmonicCoordinate hO hD 0
        (normalizedRaising hF hO hD b (normalizedDerivative hF hO hD a u)) = 0 := by
      change sphereHarmonicCoordinate hO hD 0
        (normalizedRaisingOutput hF hO hD b (normalizedDerivative hF hO hD a u)) = 0
      exact (normalizedRaisingOutput_graph hF hO hD b (normalizedDerivative hF hO hD a u)).1
    intro w u U hU k
    simp only [ContinuousLinearMap.comp_apply]
    cases k with
    | zero => simp only [hz,smul_zero]
    | succ m =>
      rw [normalizedRaising_derivative_coordinate hF hO hD a b U m,
        normalizedRaising_derivative_coordinate hF hO hD a b u m,hU (m+1)]
      simp only [map_smul,smul_smul]
      congr 1
      ring
  have hId := preservesSphereSpectralGraphs_id hO hD
  have hDiag : PreservesSphereSpectralGraphs hO hD
      (if i=j then (2 : ℝ) • ContinuousLinearMap.id ℝ SphereL2+inverseDegreeMultiplier hO hD else 0) := by
    by_cases hi : i=j
    · simp only [if_pos hi]
      exact preservesSphereSpectralGraphs_add hO hD _ _
        (preservesSphereSpectralGraphs_smul hO hD (2 : ℝ) _ hId)
        (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
    · simp only [if_neg hi]
      intro w u U hU k
      simp only [ContinuousLinearMap.zero_apply,map_zero,smul_zero]
  unfold normalizedDerivativeRaisingCommutator
  exact preservesSphereSpectralGraphs_sub hO hD _ _
    (preservesSphereSpectralGraphs_add hO hD _ _ hDiag
      (preservesSphereSpectralGraphs_comp hO hD _ _
        (hMultiplier derivativeRaisingFirstWeight 1 (by norm_num) abs_derivativeRaisingFirstWeight_le_one) (hRD i j)))
    (preservesSphereSpectralGraphs_comp hO hD _ _
      (hMultiplier derivativeRaisingSecondWeight 2 (by norm_num) abs_derivativeRaisingSecondWeight_le_two) (hRD j i))


lemma coreDerivative_coreRaising_commutator_apply
    (hF : SphereFischerInner) (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (ActualModelCommutatorWords.commutator
        (coreDerivative hO hD hF i) (coreRaising hO hD hF j)) F x =
      normalizedDerivativeRaisingCommutator hF hO hD i j
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  have hW (s : ℝ) (hs : s ≤ 2) :
      ambientBesselField hO hD s hs (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F) x =
        coreWeightOperator hO hD (besselWeight s) F x :=
    (coreWeightOperator_eq_ambientBesselField hO hD F (coreAmbientRepresentative hO hD F) s hs x).symm
  have ht := ambientDerivativeRaising_commutator_eq_normalized hF hO hD i j
    (coreAmbientFunction hO hD F) (contDiff_coreAmbientFunction hO hD F) x
  unfold ambientRaisingBesselField AngularDerivativeBesselField.ambientDerivativeBesselField at ht
  simp only [hW 1 (by norm_num),hW 2 (by norm_num)] at ht
  change normalizedDerivative hF hO hD i
      (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF j F) x) -
    normalizedRaising hF hO hD j
      (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF i F) x) = _
  rw [coreWeight_one_raising_apply_eq_normalized_shift hO hD hF j F x,
    coreWeight_one_derivative_apply_eq_normalized_shift hO hD hF i F x]
  exact ht


lemma abs_inner_coreDerivative_coreRaising_commutator_le_half
    (hF : SphereFischerInner) (i j : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪(ActualModelCommutatorWords.commutator
        (coreDerivative hO hD hF i) (coreRaising hO hD hF j)) F x,G x⟫_ℝ| ≤
      15 * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  rw [coreDerivative_coreRaising_commutator_apply hO hD hF i j F x]
  let C := normalizedDerivativeRaisingCommutator hF hO hD i j
  let uh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let u1 := coreWeightOperator hO hD (besselWeight 1) F x
  let vh := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have hub : (uh,u1) ∈ sphereBesselGraph hO hD (1/2 : ℝ) := by
    intro k
    rw [(coreWeightOperator_graph hO hD (besselWeight 1) F x) k,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) k,smul_smul,
      ← SectionFiveErrorForms.besselWeight_add]
    norm_num
  have hC := preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hO hD hF i j
  have ht := spectralGraph_inner_symm hO hD (besselWeight (1/2 : ℝ)) (C uh) (C u1) (G x) vh
    (hC _ uh u1 hub) (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
  rw [ht]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (C.le_of_opNorm_le (norm_normalizedDerivativeRaisingCommutator_le hF hO hD i j) uh) (norm_nonneg vh))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
