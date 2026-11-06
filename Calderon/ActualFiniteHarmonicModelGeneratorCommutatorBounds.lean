import Calderon.ActualFiniteHarmonicModelRotationCommutatorBounds
import Calderon.ActualFiniteHarmonicModelAngularCommutingPairs
import Calderon.ActualFiniteHarmonicModelDegreeShiftCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma exists_coreAngularGenerator_commutator_bounds
    (hF : SphereFischerInner) (i j : CoreAngularGeneratorIndex) (x : R3) :
    ∃ V, HasCoreAngularFirstOrderBounds hO hD
      (commutator (coreAngularGenerator hO hD hF i) (coreAngularGenerator hO hD hF j)) V
      (4*coreAngularGeneratorBound hO hD) x := by
  let M := coreAngularGeneratorBound hO hD
  have hb := coreAngularGeneratorBound_bounds hO hD
  have hM : 15 ≤ M := hb.1
  let P (T U : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :=
    ∃ V, HasCoreAngularFirstOrderBounds hO hD (ActualModelCommutatorWords.commutator T U) V (4*M) x
  have hz (T U : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (h : Commute T U) : P T U :=
    ⟨0,hasCoreAngularFirstOrderBounds_commutator_of_commute hO hD T U h (4*M) (by linarith) x⟩
  have hs (T U : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (h : P T U) : P U T := by
    obtain ⟨V,hV⟩ := h
    exact ⟨-V,hasCoreAngularFirstOrderBounds_commutator_swap hO hD T U V (4*M) x hV⟩
  have hdn (a : Fin 3) : P (coreDerivative hO hD hF a) (coreDegree hO hD) := by
    refine ⟨coreRaising hO hD hF a,?_⟩
    rw [coreDerivative_degree_commutator hO hD hF a]
    exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_coreDerivative hO hD hF a x) (by linarith [hb.2.1])
  have hnr (a : Fin 3) : P (coreDegree hO hD) (coreRaising hO hD hF a) := by
    refine ⟨coreDerivative hO hD hF a,?_⟩
    rw [coreDegree_raising_commutator hO hD hF a]
    exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_coreRaising hO hD hF a x) (by linarith [hb.2.1])
  have hdr (a b : Fin 3) : P (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
    refine ⟨_,hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_derivative_raising_commutator hO hD hF a b x) ?_⟩
    linarith
  have hrd (a b c : Fin 3) : P (coreRotation hO hD a b) (coreDerivative hO hD hF c) := by
    obtain ⟨V,hV⟩ := exists_coreRotation_coreDerivative_commutator_bounds hO hD hF a b c x
    exact ⟨V,hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x hV (by change 2*M ≤ 4*M; linarith)⟩
  have hrr (a b c : Fin 3) : P (coreRotation hO hD a b) (coreRaising hO hD hF c) := by
    obtain ⟨V,hV⟩ := exists_coreRotation_coreRaising_commutator_bounds hO hD hF a b c x
    exact ⟨V,hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x hV (by change 2*M ≤ 4*M; linarith)⟩
  change P (coreAngularGenerator hO hD hF i) (coreAngularGenerator hO hD hF j)
  rcases i with a | (a | (ab | ni)) <;> rcases j with b | (b | (cd | nj))
  · exact hz _ _ (coreDerivative_commute hO hD hF a b)
  · exact hdr a b
  · exact hs _ _ (hrd cd.1 cd.2 a)
  · cases nj with
    | false => exact hz _ _ (Commute.one_right _)
    | true => exact hdn a
  · exact hs _ _ (hdr b a)
  · exact hz _ _ (coreRaising_commute hO hD hF a b)
  · exact hs _ _ (hrr cd.1 cd.2 a)
  · cases nj with
    | false => exact hz _ _ (Commute.one_right _)
    | true => exact hs _ _ (hnr a)
  · exact hrd ab.1 ab.2 b
  · exact hrr ab.1 ab.2 b
  · exact exists_coreRotation_coreRotation_commutator_bounds hO hD ab.1 ab.2 cd.1 cd.2 x
  · cases nj with
    | false => exact hz _ _ (Commute.one_right _)
    | true => exact hz _ _ (coreDegree_coreRotation_commute hO hD ab.1 ab.2).symm
  · cases ni with
    | false => exact hz _ _ (Commute.one_left _)
    | true => exact hs _ _ (hdn b)
  · cases ni with
    | false => exact hz _ _ (Commute.one_left _)
    | true => exact hnr b
  · cases ni with
    | false => exact hz _ _ (Commute.one_left _)
    | true => exact hz _ _ (coreDegree_coreRotation_commute hO hD cd.1 cd.2)
  · cases ni <;> cases nj
    · exact hz _ _ (Commute.one_left _)
    · exact hz _ _ (Commute.one_left _)
    · exact hz _ _ (Commute.one_right _)
    · exact hz _ _ (Commute.refl _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
