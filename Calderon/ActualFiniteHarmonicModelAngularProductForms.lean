import Calderon.ActualFiniteHarmonicModelHalfWeightSumAction

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularProductFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularProductFunction

def HasCoreAngularFirstOrderBounds
    (T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (C : ℝ) (x : R3) : Prop :=
  0 ≤ C ∧
  (∀ F G : smoothCompactFiniteSphereCore hO hD, ⟪T F x,G x⟫_ℝ = ⟪F x,Tstar G x⟫_ℝ) ∧
  (∀ F G : smoothCompactFiniteSphereCore hO hD,
    |⟪T F x,G x⟫_ℝ| ≤ C*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖) ∧
  (∀ F : smoothCompactFiniteSphereCore hO hD,
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (T F) x‖ ≤
      C*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖) ∧
  (∀ F : smoothCompactFiniteSphereCore hO hD,
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (Tstar F) x‖ ≤
      C*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖)

lemma coreAngular_product_inner_adjoint
    (A Astar B Bstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    ⟪(A*B) F x,G x⟫_ℝ = ⟪F x,(Bstar*Astar) G x⟫_ℝ := by
  exact (hA.2.1 (B F) G).trans (hB.2.1 F (Astar G))

lemma coreAngular_product_half_threehalf_bound
    (A Astar B Bstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪(A*B) F x,G x⟫_ℝ| ≤ (CA*CB)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  change |⟪A (B F) x,G x⟫_ℝ| ≤ _
  rw [hA.2.1]
  calc
    _ ≤ CB*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (Astar G) x‖ := hB.2.2.1 F (Astar G)
    _ ≤ CB*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      (CA*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) :=
      mul_le_mul_of_nonneg_left (hA.2.2.2.2 G) (mul_nonneg hB.1 (norm_nonneg _))
    _ = _ := by ring

lemma coreAngular_product_threehalf_half_bound
    (A Astar B Bstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪(A*B) F x,G x⟫_ℝ| ≤ (CA*CB)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  calc
    _ ≤ CA*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (B F) x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := hA.2.2.1 (B F) G
    _ ≤ CA*(CB*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB.2.2.2.1 F) hA.1) (norm_nonneg _)
    _ = _ := by ring

lemma coreAngular_triple_threehalf_bound
    (A Astar B Bstar T Tstar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (CA CB CT : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar CA x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar CB x)
    (hT : HasCoreAngularFirstOrderBounds hO hD T Tstar CT x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪(A*B*T) F x,G x⟫_ℝ| ≤ (CA*CB*CT)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have ht := coreAngular_product_half_threehalf_bound hO hD A Astar B Bstar CA CB x hA hB (T F) G
  calc
    _ ≤ (CA*CB)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (T F) x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := ht
    _ ≤ (CA*CB)*(CT*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT.2.2.2.1 F)
        (mul_nonneg hA.1 hB.1)) (norm_nonneg _)
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
