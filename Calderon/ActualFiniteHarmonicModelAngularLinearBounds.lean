import Calderon.ActualFiniteHarmonicModelAngularBoundRules

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularLinearBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularLinearBoundsFunction

lemma hasCoreAngularFirstOrderBounds_add
    (A Astar B Bstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x) :
    HasCoreAngularFirstOrderBounds hO hD (A+B) (Astar+Bstar) (CA+CB) x := by
  refine ⟨add_nonneg hA.1 hB.1,?_,?_,?_,?_⟩
  · intro F G
    simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left,inner_add_right,
      hA.2.1,hB.2.1]
  · intro F G
    simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left]
    exact (abs_add_le _ _).trans (by
      have ht := add_le_add (hA.2.2.1 F G) (hB.2.2.1 F G)
      simpa only [add_mul] using ht)
  · intro F
    simp only [LinearMap.add_apply,map_add,Submodule.coe_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (by
      have ht := add_le_add (hA.2.2.2.1 F) (hB.2.2.2.1 F)
      simpa only [add_mul] using ht)
  · intro F
    simp only [LinearMap.add_apply,map_add,Submodule.coe_add,Pi.add_apply]
    exact (norm_add_le _ _).trans (by
      have ht := add_le_add (hA.2.2.2.2 F) (hB.2.2.2.2 F)
      simpa only [add_mul] using ht)

lemma hasCoreAngularFirstOrderBounds_neg
    (A Astar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (C : ℝ) (x : R3) (hA : HasCoreAngularFirstOrderBounds hO hD A Astar C x) :
    HasCoreAngularFirstOrderBounds hO hD (-A) (-Astar) C x := by
  refine ⟨hA.1,?_,?_,?_,?_⟩
  · intro F G
    simp only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,inner_neg_left,inner_neg_right,hA.2.1]
  · intro F G
    simpa only [LinearMap.neg_apply,Submodule.coe_neg,Pi.neg_apply,inner_neg_left,abs_neg] using hA.2.2.1 F G
  · intro F
    simpa only [LinearMap.neg_apply,map_neg,Submodule.coe_neg,Pi.neg_apply,norm_neg] using hA.2.2.2.1 F
  · intro F
    simpa only [LinearMap.neg_apply,map_neg,Submodule.coe_neg,Pi.neg_apply,norm_neg] using hA.2.2.2.2 F

lemma hasCoreAngularFirstOrderBounds_zero (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD 0 0 0 x := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩ <;> intros <;>
    simp only [LinearMap.zero_apply,map_zero,Submodule.coe_zero,Pi.zero_apply,
      inner_zero_left,inner_zero_right,abs_zero,norm_zero,zero_mul,le_refl]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
