import Calderon.ActualFiniteHarmonicModelVAngularCommutators

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SmoothMetricFrame MovingFrameConnection
  AmbientReferenceCovariantCore ActualAngularCoefficientCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev scalarShiftCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] scalarShiftCommutatorFunction
lemma coreScalar_shift_sum_degree_commutator
    (hF : SphereFischerInner) (v : Fin 3 → R3 → ℝ) (hv : ∀ a, ContDiff ℝ ∞ (v a)) :
    let S := ∑ a : Fin 3, coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a+coreRaising hO hD hF a)
    ActualModelCommutatorWords.commutator S (coreDegree hO hD) =
      ∑ a : Fin 3, coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a-coreRaising hO hD hF a) := by
  dsimp only
  let N := coreDegree hO hD
  have hN : ScalarCentral hO hD N := scalarCentral_coreWeightOperator hO hD (fun k => (k : ℝ))
  have hRN (a : Fin 3) : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) N =
      -coreRaising hO hD hF a := by
    have he : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) N =
        -ActualModelCommutatorWords.commutator N (coreRaising hO hD hF a) := by
      unfold ActualModelCommutatorWords.commutator
      abel
    rw [he,coreDegree_raising_commutator hO hD hF a]
  have hPN (a : Fin 3) : ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a+coreRaising hO hD hF a) N =
      coreDerivative hO hD hF a-coreRaising hO hD hF a := by
    have hDN : ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) N =
        coreDerivative hO hD hF a := coreDerivative_degree_commutator hO hD hF a
    have ht := ActualModelCommutatorWords.commutator_add_left
      (coreDerivative hO hD hF a) (coreRaising hO hD hF a) N
    rw [hDN, hRN a] at ht
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    have hx := congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) ht
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg,
      Pi.add_apply, Pi.sub_apply, Pi.neg_apply, _root_.sub_eq_add_neg] using hx
  have hterm (a : Fin 3) : ActualModelCommutatorWords.commutator
      (coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a+coreRaising hO hD hF a)) N =
      coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a-coreRaising hO hD hF a) := by
    rw [ActualAngularCoefficientCommutator.commutator_mul_left_of_commute _ _ _ (hN _ _).symm,hPN a]
  rw [ActualModelCommutatorWords.commutator_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  exact hterm a


lemma coreScalar_shift_sum_raising_commutator
    (hF : SphereFischerInner) (v : Fin 3 → R3 → ℝ) (hv : ∀ a, ContDiff ℝ ∞ (v a)) (b : Fin 3) :
    let S := ∑ a : Fin 3, coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a+coreRaising hO hD hF a)
    ActualModelCommutatorWords.commutator S (coreRaising hO hD hF b) =
      ∑ a : Fin 3, coreScalar hO hD (v a) (hv a)*
        ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) (coreRaising hO hD hF b) := by
  dsimp only
  let Y := coreRaising hO hD hF b
  have hY : ScalarCentral hO hD Y := scalarCentral_coreRaising hO hD hF b
  have hPY (a : Fin 3) : ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a+coreRaising hO hD hF a) Y =
      ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) Y := by
    have hRR : ActualModelCommutatorWords.commutator (coreRaising hO hD hF a) Y=0 :=
      ActualAngularCoefficientCommutator.commutator_eq_zero_of_commute _ _ (coreRaising_commute hO hD hF a b)
    simpa only [hRR,add_zero] using ActualModelCommutatorWords.commutator_add_left
      (coreDerivative hO hD hF a) (coreRaising hO hD hF a) Y
  have hterm (a : Fin 3) : ActualModelCommutatorWords.commutator
      (coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a+coreRaising hO hD hF a)) Y =
      coreScalar hO hD (v a) (hv a)*ActualModelCommutatorWords.commutator (coreDerivative hO hD hF a) Y := by
    rw [ActualAngularCoefficientCommutator.commutator_mul_left_of_commute _ _ _ (hY _ _).symm,hPY a]
  rw [ActualModelCommutatorWords.commutator_sum_left]
  apply Finset.sum_congr rfl
  intro a ha
  exact hterm a


lemma coreScalar_shift_sum_connection_commutator
    (hF : SphereFischerInner) (v : Fin 3 → R3 → ℝ) (hv : ∀ a, ContDiff ℝ ∞ (v a))
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (c : Fin 3) :
    let S := ∑ a : Fin 3, coreScalar hO hD (v a) (hv a)*(coreDerivative hO hD hF a+coreRaising hO hD hF a)
    let Gamma : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD) := fun b a =>
      coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) c) b a)
        (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
          (contDiff_referenceMetricGramFrame_slice g hg L lam c) b a)
    ActualModelCommutatorWords.commutator S (nativeReferenceConnectionAction hO hD g hg L lam c) =
      -(∑ a : Fin 3, ∑ b : Fin 3, coreScalar hO hD (v a) (hv a)*Gamma b a*
        (coreDerivative hO hD hF b+coreRaising hO hD hF b)) := by
  dsimp only
  let Y := nativeReferenceConnectionAction hO hD g hg L lam c
  let P (a : Fin 3) := coreDerivative hO hD hF a+coreRaising hO hD hF a
  let Gamma (b a : Fin 3) := coreScalar hO hD (fun x => referenceFrameConnectionCoefficient g L lam x
    (referenceMetricGramFrame g L (lam,x) c) b a)
    (contDiff_referenceFrameConnectionCoefficient_field g hg L lam _
      (contDiff_referenceMetricGramFrame_slice g hg L lam c) b a)
  have hY : ScalarCentral hO hD Y := scalarCentral_nativeReferenceConnectionAction hO hD g hg L lam c
  have hYP (a : Fin 3) : ActualModelCommutatorWords.commutator Y (P a) = ∑ b : Fin 3, Gamma b a*P b := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    have he := congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (ActualModelCommutatorWords.commutator_add_right Y (coreDerivative hO hD hF a) (coreRaising hO hD hF a))
    change ActualModelCommutatorWords.commutator Y (P a) F x =
      ActualModelCommutatorWords.commutator Y (coreDerivative hO hD hF a) F x+
      ActualModelCommutatorWords.commutator Y (coreRaising hO hD hF a) F x at he
    rw [nativeReferenceConnection_derivative_commutator hO hD hF g hg L lam c a F x,
      nativeReferenceConnection_raising_commutator hO hD hF g hg L lam c a F x] at he
    simpa only [Gamma, P, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply, coreScalar, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_mk, Submodule.coe_sum, Submodule.coe_add, Finset.sum_apply,
      Pi.add_apply, smul_add, Finset.sum_add_distrib] using he
  have hPY (a : Fin 3) : ActualModelCommutatorWords.commutator (P a) Y = -(∑ b : Fin 3, Gamma b a*P b) := by
    have he : ActualModelCommutatorWords.commutator (P a) Y = -ActualModelCommutatorWords.commutator Y (P a) := by
      unfold ActualModelCommutatorWords.commutator
      abel
    rw [he,hYP a]
  have hterm (a : Fin 3) : ActualModelCommutatorWords.commutator (coreScalar hO hD (v a) (hv a)*P a) Y =
      -(∑ b : Fin 3, coreScalar hO hD (v a) (hv a)*Gamma b a*P b) := by
    rw [ActualAngularCoefficientCommutator.commutator_mul_left_of_commute _ _ _ (hY _ _).symm,hPY a]
    apply LinearMap.ext
    intro F
    simp only [Fin.sum_univ_three, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.add_apply, map_neg, map_add]
  change ActualModelCommutatorWords.commutator
    (∑ a : Fin 3, coreScalar hO hD (v a) (hv a) * P a) Y =
      -(∑ a : Fin 3, ∑ b : Fin 3, coreScalar hO hD (v a) (hv a) * Gamma b a * P b)
  rw [ActualModelCommutatorWords.commutator_sum_left]
  calc
    (∑ a : Fin 3, ActualModelCommutatorWords.commutator
      (coreScalar hO hD (v a) (hv a) * P a) Y) =
        ∑ a : Fin 3, -(∑ b : Fin 3,
          coreScalar hO hD (v a) (hv a) * Gamma b a * P b) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hterm a
    _ = -(∑ a : Fin 3, ∑ b : Fin 3,
        coreScalar hO hD (v a) (hv a) * Gamma b a * P b) := by
      apply LinearMap.ext
      intro F
      simp only [Fin.sum_univ_three, LinearMap.add_apply, LinearMap.neg_apply]
      abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
