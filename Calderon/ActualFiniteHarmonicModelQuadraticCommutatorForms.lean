import Calderon.ActualFiniteHarmonicModelAngularProductForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev quadraticCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] quadraticCommutatorFunction

lemma coreAngular_quadratic_linear_commutator_bound
    (A Astar B Bstar T Sstar Ustar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (M N : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar M x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar M x)
    (hBT : HasCoreAngularFirstOrderBounds hO hD (commutator B T) Sstar N x)
    (hAT : HasCoreAngularFirstOrderBounds hO hD (commutator A T) Ustar N x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪commutator (A*B) T F x,G x⟫_ℝ| ≤ (2*M*N)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have halg {R : Type} [Ring R] (a b t : R) :
      commutator (a*b) t = a*commutator b t+commutator a t*b := by
    unfold ActualModelCommutatorWords.commutator
    noncomm_ring
  rw [halg]
  simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left]
  have h1 := coreAngular_product_half_threehalf_bound hO hD A Astar (commutator B T) Sstar M N x hA hBT F G
  have h2 := coreAngular_product_half_threehalf_bound hO hD (commutator A T) Ustar B Bstar N M x hAT hB F G
  calc
    _ ≤ |⟪(A*commutator B T) F x,G x⟫_ℝ|+|⟪(commutator A T*B) F x,G x⟫_ℝ| := abs_add_le _ _
    _ ≤ (M*N)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖+
      (N*M)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := add_le_add h1 h2
    _ = _ := by ring

lemma coreAngular_quadratic_quadratic_commutator_bound
    (A Astar B Bstar T Tstar U Ustar BCstar BUstar ACstar AUstar :
      Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (M N : ℝ) (x : R3)
    (hA : HasCoreAngularFirstOrderBounds hO hD A Astar M x)
    (hB : HasCoreAngularFirstOrderBounds hO hD B Bstar M x)
    (hT : HasCoreAngularFirstOrderBounds hO hD T Tstar M x)
    (hU : HasCoreAngularFirstOrderBounds hO hD U Ustar M x)
    (hBT : HasCoreAngularFirstOrderBounds hO hD (commutator B T) BCstar N x)
    (hBU : HasCoreAngularFirstOrderBounds hO hD (commutator B U) BUstar N x)
    (hAT : HasCoreAngularFirstOrderBounds hO hD (commutator A T) ACstar N x)
    (hAU : HasCoreAngularFirstOrderBounds hO hD (commutator A U) AUstar N x)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪commutator (A*B) (T*U) F x,G x⟫_ℝ| ≤ (4*M^2*N)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  have halg {R : Type} [Ring R] (a b t u : R) :
      ActualModelCommutatorWords.commutator (a*b) (t*u) =
        a*ActualModelCommutatorWords.commutator b t*u+a*t*ActualModelCommutatorWords.commutator b u+ActualModelCommutatorWords.commutator a t*u*b+t*ActualModelCommutatorWords.commutator a u*b := by
    unfold ActualModelCommutatorWords.commutator
    noncomm_ring
  let f : ℝ := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖
  let g : ℝ := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  let e1 : ℝ := ⟪(A*ActualModelCommutatorWords.commutator B T*U) F x,G x⟫_ℝ
  let e2 : ℝ := ⟪(A*T*ActualModelCommutatorWords.commutator B U) F x,G x⟫_ℝ
  let e3 : ℝ := ⟪(ActualModelCommutatorWords.commutator A T*U*B) F x,G x⟫_ℝ
  let e4 : ℝ := ⟪(T*ActualModelCommutatorWords.commutator A U*B) F x,G x⟫_ℝ
  have he : ⟪ActualModelCommutatorWords.commutator (A*B) (T*U) F x,G x⟫_ℝ = e1+e2+e3+e4 := by
    rw [halg]
    simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left]
    rfl
  have h1 : |e1| ≤ (M*N*M)*f*g := coreAngular_triple_threehalf_bound hO hD A Astar (ActualModelCommutatorWords.commutator B T) BCstar U Ustar M N M x hA hBT hU F G
  have h2 : |e2| ≤ (M*M*N)*f*g := coreAngular_triple_threehalf_bound hO hD A Astar T Tstar (ActualModelCommutatorWords.commutator B U) BUstar M M N x hA hT hBU F G
  have h3 : |e3| ≤ (N*M*M)*f*g := coreAngular_triple_threehalf_bound hO hD (ActualModelCommutatorWords.commutator A T) ACstar U Ustar B Bstar N M M x hAT hU hB F G
  have h4 : |e4| ≤ (M*N*M)*f*g := coreAngular_triple_threehalf_bound hO hD T Tstar (ActualModelCommutatorWords.commutator A U) AUstar B Bstar M N M x hT hAU hB F G
  rw [he]
  change |e1+e2+e3+e4| ≤ (4*M^2*N)*f*g
  calc
    _ ≤ |e1|+|e2|+|e3|+|e4| :=
      (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (M*N*M)*f*g+(M*M*N)*f*g+(N*M*M)*f*g+(M*N*M)*f*g :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
