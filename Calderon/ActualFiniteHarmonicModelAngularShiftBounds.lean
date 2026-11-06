import Calderon.ActualFiniteHarmonicModelAngularBoundRules
import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BalancedAngularShift
  AngularShiftGraph ActualReferenceDDSpectralTransport ActualAngularDerivativeRaisingCommutator
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularShiftBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularShiftBoundFunction

lemma hasCoreAngularFirstOrderBounds_coreDerivative
    (hF : SphereFischerInner) (a : Fin 3) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (coreDerivative hO hD hF a) (coreRaising hO hD hF a)
      (4+2*(2 : ℝ)^(1/2 : ℝ)) x := by
  have hp : 0 ≤ (2 : ℝ)^(1/2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : (4 : ℝ) ≤ 4+2*(2 : ℝ)^(1/2 : ℝ) := by linarith
  have h2 : (2 : ℝ) ≤ 4+2*(2 : ℝ)^(1/2 : ℝ) := by linarith
  have hR : 2*(2 : ℝ)^(1/2 : ℝ) ≤ 4+2*(2 : ℝ)^(1/2 : ℝ) := by linarith
  refine ⟨by positivity,?_,?_,?_,?_⟩
  · intro F G
    exact sphereDerivativeGraph_inner_adjoint hF hO hD a
      (F x) (coreDerivative hO hD hF a F x) (G x) (coreRaising hO hD hF a G x)
      (coreDerivative_graph hO hD hF a F x) (coreRaising_graph hO hD hF a G x)
  · intro F G
    have ht := abs_inner_derivative_le_half_norm hF hO hD a (F x)
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x) (coreDerivative hO hD hF a F x)
      (G x) (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x)
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x)
      (coreDerivative_graph hO hD hF a F x)
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) G x)
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)) (norm_nonneg _))
  · intro F
    exact (norm_coreWeight_half_derivative_le hO hD hF a F x).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  · intro F
    exact (norm_coreWeight_half_raising_le hO hD hF a F x).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

lemma hasCoreAngularFirstOrderBounds_coreRaising
    (hF : SphereFischerInner) (a : Fin 3) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD (coreRaising hO hD hF a) (coreDerivative hO hD hF a)
      (4+2*(2 : ℝ)^(1/2 : ℝ)) x :=
  hasCoreAngularFirstOrderBounds_adjoint hO hD _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreDerivative hO hD hF a x)

lemma norm_coreWeight_half_derivative_raising_commutator_le
    (hF : SphereFischerInner) (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (commutator (coreDerivative hO hD hF i) (coreRaising hO hD hF j) F) x‖ ≤
      15*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  have ht := norm_coreWeight_half_preserving_action_le hO hD
    (normalizedDerivativeRaisingCommutator hF hO hD i j)
    (preservesSphereSpectralGraphs_normalizedDerivativeRaisingCommutator hO hD hF i j)
    _ F x (coreDerivative_coreRaising_commutator_apply hO hD hF i j F x)
  exact ht.trans (mul_le_mul_of_nonneg_right
    (norm_normalizedDerivativeRaisingCommutator_le hF hO hD i j) (norm_nonneg _))

lemma coreDerivative_coreRaising_commutator_inner_adjoint
    (hF : SphereFischerInner) (i j : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪commutator (coreDerivative hO hD hF i) (coreRaising hO hD hF j) F x,G x⟫_ℝ =
      ⟪F x,commutator (coreDerivative hO hD hF j) (coreRaising hO hD hF i) G x⟫_ℝ := by
  have hd (a : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) :
      ⟪coreDerivative hO hD hF a U x,V x⟫_ℝ = ⟪U x,coreRaising hO hD hF a V x⟫_ℝ :=
    (hasCoreAngularFirstOrderBounds_coreDerivative hO hD hF a x).2.1 U V
  have hr (a : Fin 3) (U V : smoothCompactFiniteSphereCore hO hD) :
      ⟪coreRaising hO hD hF a U x,V x⟫_ℝ = ⟪U x,coreDerivative hO hD hF a V x⟫_ℝ :=
    (hasCoreAngularFirstOrderBounds_coreRaising hO hD hF a x).2.1 U V
  change ⟪coreDerivative hO hD hF i (coreRaising hO hD hF j F) x-
      coreRaising hO hD hF j (coreDerivative hO hD hF i F) x,G x⟫_ℝ =
    ⟪F x,coreDerivative hO hD hF j (coreRaising hO hD hF i G) x-
      coreRaising hO hD hF i (coreDerivative hO hD hF j G) x⟫_ℝ
  rw [inner_sub_left,inner_sub_right,hd,hr,hr,hd]

lemma hasCoreAngularFirstOrderBounds_derivative_raising_commutator
    (hF : SphereFischerInner) (i j : Fin 3) (x : R3) :
    HasCoreAngularFirstOrderBounds hO hD
      (commutator (coreDerivative hO hD hF i) (coreRaising hO hD hF j))
      (commutator (coreDerivative hO hD hF j) (coreRaising hO hD hF i)) 15 x := by
  refine ⟨by norm_num,?_,?_,?_,?_⟩
  · intro F G
    exact coreDerivative_coreRaising_commutator_inner_adjoint hO hD hF i j F G x
  · intro F G
    exact abs_inner_coreDerivative_coreRaising_commutator_le_half hO hD hF i j F G x
  · intro F
    exact norm_coreWeight_half_derivative_raising_commutator_le hO hD hF i j F x
  · intro F
    exact norm_coreWeight_half_derivative_raising_commutator_le hO hD hF j i F x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
