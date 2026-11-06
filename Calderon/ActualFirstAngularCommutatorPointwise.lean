import Calderon.ActualFiniteHarmonicCore

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ActualFirstAngularCommutatorPointwise
open SphereHarmonic ActualFiniteHarmonicCore

lemma core_four_angular_blocks_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d t : R3 → ℝ) (m n e k : Fin 3 → R3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (hd : ContDiff ℝ ∞ d) (ht : ContDiff ℝ ∞ t)
    (hm : ∀ a, ContDiff ℝ ∞ (m a)) (hn : ∀ b, ContDiff ℝ ∞ (n b))
    (he : ∀ a, ContDiff ℝ ∞ (e a)) (hk : ∀ c, ContDiff ℝ ∞ (k c))
    (hGamma : ∀ c b a, ContDiff ℝ ∞ (Gamma c b a))
    (P Q R : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (E : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let f (a : Fin 3) : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
      coreScalar hO hD (m a) (hm a)+(2 : ℝ) • coreScalar hO hD (e a) (he a)
    ((-(∑ a : Fin 3, coreScalar hO hD d hd * f a * P a) +
      (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        coreScalar hO hD (k c) (hk c)*f a*coreScalar hO hD (Gamma c b a) (hGamma c b a)*Q b) -
      (∑ b : Fin 3, coreScalar hO hD (n b) (hn b)*((2 : ℝ) • coreScalar hO hD t ht)*R b) -
      (∑ b : Fin 3, ∑ a : Fin 3, coreScalar hO hD (n b) (hn b)*f a*E a b)) F).val x =
    -(∑ a : Fin 3, (d x*(m a x+2*e a x)) • (P a F).val x) +
      (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        (k c x*(m a x+2*e a x)*Gamma c b a x) • (Q b F).val x) -
      (∑ b : Fin 3, (n b x*(2*t x)) • (R b F).val x) -
      (∑ b : Fin 3, ∑ a : Fin 3, (n b x*(m a x+2*e a x)) • (E a b F).val x) := by
  dsimp only
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_add,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul,
    Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,
    smul_smul,smul_add,add_smul,mul_add,add_mul,mul_assoc]

end OAI.AnisotropicCalderon.ActualFirstAngularCommutatorPointwise
