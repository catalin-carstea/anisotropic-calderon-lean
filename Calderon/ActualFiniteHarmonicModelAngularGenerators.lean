import Calderon.ActualFiniteHarmonicModelAngularShiftBounds
import Calderon.ActualFiniteHarmonicModelDegreeRotationBounds
import Calderon.ActualFiniteHarmonicModelAngularFiniteBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSphereRotation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

abbrev CoreAngularGeneratorIndex := Fin 3 ⊕ (Fin 3 ⊕ ((Fin 3 × Fin 3) ⊕ Bool))

def coreAngularGenerator (hF : SphereFischerInner) : CoreAngularGeneratorIndex →
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD)
  | Sum.inl a => coreDerivative hO hD hF a
  | Sum.inr (Sum.inl a) => coreRaising hO hD hF a
  | Sum.inr (Sum.inr (Sum.inl (a,b))) => coreRotation hO hD a b
  | Sum.inr (Sum.inr (Sum.inr true)) => coreDegree hO hD
  | Sum.inr (Sum.inr (Sum.inr false)) => 1

def coreAngularGeneratorAdjoint (hF : SphereFischerInner) : CoreAngularGeneratorIndex →
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD)
  | Sum.inl a => coreRaising hO hD hF a
  | Sum.inr (Sum.inl a) => coreDerivative hO hD hF a
  | Sum.inr (Sum.inr (Sum.inl (a,b))) => -coreRotation hO hD a b
  | Sum.inr (Sum.inr (Sum.inr true)) => coreDegree hO hD
  | Sum.inr (Sum.inr (Sum.inr false)) => 1

def coreAngularGeneratorBound : ℝ :=
  20+2*(2 : ℝ)^(1/2 : ℝ)+‖inverseDegreeMultiplier hO hD‖+
    ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖+
    ∑ a : Fin 3, ∑ b : Fin 3, ‖normalizedRotation hO hD a b‖

lemma coreAngularGeneratorBound_bounds :
    15 ≤ coreAngularGeneratorBound hO hD ∧
    4+2*(2 : ℝ)^(1/2 : ℝ) ≤ coreAngularGeneratorBound hO hD ∧
    ‖inverseDegreeMultiplier hO hD‖ ≤ coreAngularGeneratorBound hO hD ∧
    ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖ ≤ coreAngularGeneratorBound hO hD ∧
    ∀ a b : Fin 3, ‖normalizedRotation hO hD a b‖ ≤ coreAngularGeneratorBound hO hD := by
  have hp : 0 ≤ (2 : ℝ)^(1/2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hI : 0 ≤ ‖inverseDegreeMultiplier hO hD‖ := norm_nonneg _
  have hQ : 0 ≤ ‖ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD‖ := norm_nonneg _
  have hs : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖normalizedRotation hO hD a b‖ :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))
  have hr (a b : Fin 3) : ‖normalizedRotation hO hD a b‖ ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ‖normalizedRotation hO hD i j‖ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _)) (Finset.mem_univ a))
  unfold coreAngularGeneratorBound
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
  intro a b
  have ht := hr a b
  linarith

lemma hasCoreAngularFirstOrderBounds_coreAngularGenerator
    (hF : SphereFischerInner) (i : CoreAngularGeneratorIndex) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (coreAngularGenerator hO hD hF i)
      (coreAngularGeneratorAdjoint hO hD hF i) (coreAngularGeneratorBound hO hD) x := by
  have hb := coreAngularGeneratorBound_bounds hO hD
  rcases i with a | (a | (ab | b))
  · exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_coreDerivative hO hD hF a x) hb.2.1
  · exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_coreRaising hO hD hF a x) hb.2.1
  · exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
      (hasCoreAngularFirstOrderBounds_coreRotation hO hD ab.1 ab.2 x) (hb.2.2.2.2 ab.1 ab.2)
  · cases b with
    | false =>
      exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
        (hasCoreAngularFirstOrderBounds_one hO hD x) hb.2.2.1
    | true =>
      exact hasCoreAngularFirstOrderBounds_mono hO hD _ _ _ _ x
        (hasCoreAngularFirstOrderBounds_coreDegree hO hD x) hb.2.2.2.1

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
