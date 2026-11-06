import Calderon.ActualModelCommutatorWords

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualAngularCoefficientCommutator
open ActualModelCommutatorWords
variable {A : Type*} [Ring A]
lemma commutator_eq_zero_of_commute (X Y : A) (hXY : Commute X Y) :
    ActualModelCommutatorWords.commutator X Y = 0 := by
  change X*Y-Y*X=0
  exact sub_eq_zero.mpr hXY.eq


lemma commutator_mul_left_of_commute (c X Y : A) (hcY : Commute c Y) :
    ActualModelCommutatorWords.commutator (c*X) Y = c*ActualModelCommutatorWords.commutator X Y := by
  simp only [ActualModelCommutatorWords.commutator,mul_sub,mul_assoc]
  rw [← mul_assoc Y c X,← hcY.eq,mul_assoc]


lemma commutator_mul_right_of_commute (X c Y : A) (hXc : Commute X c) :
    ActualModelCommutatorWords.commutator X (c*Y) = c*ActualModelCommutatorWords.commutator X Y := by
  simp only [ActualModelCommutatorWords.commutator,mul_sub,mul_assoc]
  rw [← mul_assoc X c Y,hXc.eq,mul_assoc]


lemma firstAngularCoefficient_commutator_right (X s d N : A) (k m K R : Fin 3 → A)
    (hXs : Commute X s) (hXd : Commute X d)
    (hXk : ∀ a, Commute X (k a)) (hXm : ∀ a, Commute X (m a)) :
    ActualModelCommutatorWords.commutator X (s+d*N+(∑ a : Fin 3, k a*K a)+(∑ a : Fin 3, m a*R a)) =
    d*ActualModelCommutatorWords.commutator X N +
      (∑ a : Fin 3, k a*ActualModelCommutatorWords.commutator X (K a)) +
      ∑ a : Fin 3, m a*ActualModelCommutatorWords.commutator X (R a) := by
  have hd := commutator_mul_right_of_commute X d N hXd
  have hk (a : Fin 3) := commutator_mul_right_of_commute X (k a) (K a) (hXk a)
  have hm (a : Fin 3) := commutator_mul_right_of_commute X (m a) (R a) (hXm a)
  simp only [ActualModelCommutatorWords.commutator_add_right,
    ActualModelCommutatorWords.commutator_sum_right,
    commutator_eq_zero_of_commute X s hXs,hd,hk,hm,zero_add]


lemma defectFirstAngularCoefficient_commutator_left (s c N Y : A) (m P : Fin 3 → A)
    (hsY : Commute s Y) (hcY : Commute c Y) (hmY : ∀ a, Commute (m a) Y) :
    ActualModelCommutatorWords.commutator (s-c*N-(∑ a : Fin 3, m a*P a)) Y =
      -c*ActualModelCommutatorWords.commutator N Y -
        ∑ a : Fin 3, m a*ActualModelCommutatorWords.commutator (P a) Y := by
  have he : ActualModelCommutatorWords.commutator (s-c*N-(∑ a : Fin 3, m a*P a)) Y =
      ActualModelCommutatorWords.commutator s Y - ActualModelCommutatorWords.commutator (c*N) Y -
        ∑ a : Fin 3, ActualModelCommutatorWords.commutator (m a*P a) Y := by
    unfold ActualModelCommutatorWords.commutator
    simp only [sub_mul,mul_sub,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
    noncomm_ring
  have hm (a : Fin 3) := commutator_mul_left_of_commute (m a) (P a) Y (hmY a)
  rw [commutator_eq_zero_of_commute s Y hsY,commutator_mul_left_of_commute c N Y hcY] at he
  simpa only [zero_sub,neg_mul,hm] using he

end OAI.AnisotropicCalderon.ActualAngularCoefficientCommutator
