import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualModelCommutatorWords
variable {A : Type*} [Ring A]

def commutator (X Y : A) : A := X*Y-Y*X
/-- Inner derivation by the actual ordinary base operator. No boundedness is implied. -/
def coefficientDerivative (d X : A) : A := commutator d X

lemma commutator_add_left (X Y Z : A) :
    commutator (X+Y) Z = commutator X Z+commutator Y Z := by
  unfold commutator
  noncomm_ring
lemma commutator_add_right (X Y Z : A) :
    commutator X (Y+Z) = commutator X Y+commutator X Z := by
  unfold commutator
  noncomm_ring
lemma commutator_sum_left {ι : Type*} (s : Finset ι) (X : ι → A) (Y : A) :
    commutator (∑ i ∈ s, X i) Y = ∑ i ∈ s, commutator (X i) Y := by
  simp only [commutator,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
lemma commutator_sum_right {ι : Type*} (s : Finset ι) (X : A) (Y : ι → A) :
    commutator X (∑ i ∈ s, Y i) = ∑ i ∈ s, commutator X (Y i) := by
  simp only [commutator,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]

lemma commutator_first_second (dl di dj H a : A)
    (hHa : Commute H a) (hli : Commute dl di) (hlj : Commute dl dj) :
    commutator (H*dl) (a*di*dj) =
      H*coefficientDerivative dl a*di*dj -
      a*coefficientDerivative di (coefficientDerivative dj H)*dl -
      a*coefficientDerivative dj H*di*dl -
      a*coefficientDerivative di H*dj*dl := by
  have hHa0 : commutator H a = 0 := sub_eq_zero.mpr hHa.eq
  have hli0 : commutator dl di = 0 := sub_eq_zero.mpr hli.eq
  have hlj0 : commutator dl dj = 0 := sub_eq_zero.mpr hlj.eq
  have he : commutator (H*dl) (a*di*dj) =
      H*coefficientDerivative dl a*di*dj+commutator H a*dl*di*dj+
      a*(H*commutator dl di-coefficientDerivative di H*dl)*dj+
      a*di*(H*commutator dl dj-coefficientDerivative dj H*dl) := by
    unfold coefficientDerivative commutator
    noncomm_ring
  have hswap : a*coefficientDerivative di H*dl*dj =
      a*coefficientDerivative di H*dj*dl := by
    simpa only [mul_assoc] using
      congrArg (fun z : A => a*coefficientDerivative di H*z) hlj.eq
  have hp : a*di*coefficientDerivative dj H*dl =
      a*coefficientDerivative di (coefficientDerivative dj H)*dl+
        a*coefficientDerivative dj H*di*dl := by
    unfold coefficientDerivative commutator
    noncomm_ring
  calc
    _ = H*coefficientDerivative dl a*di*dj-
        a*coefficientDerivative di H*dl*dj-a*di*coefficientDerivative dj H*dl := by
      rw [he,hHa0,hli0,hlj0]
      noncomm_ring
    _ = _ := by rw [hswap,hp]; noncomm_ring

lemma commutator_zero_second (di dj H a : A) (hHa : Commute H a) :
    commutator H (a*di*dj) =
      -a*coefficientDerivative di (coefficientDerivative dj H) -
      a*coefficientDerivative dj H*di - a*coefficientDerivative di H*dj := by
  have hHa0 : commutator H a = 0 := sub_eq_zero.mpr hHa.eq
  have he : commutator H (a*di*dj) = commutator H a*di*dj-
      a*coefficientDerivative di H*dj-a*di*coefficientDerivative dj H := by
    unfold coefficientDerivative commutator
    noncomm_ring
  rw [he,hHa0]
  unfold coefficientDerivative commutator
  noncomm_ring

lemma commutator_first_first (dl di H B : A) (hli : Commute dl di) :
    commutator (H*dl) (B*di) =
      commutator H B*dl*di + H*coefficientDerivative dl B*di -
      B*coefficientDerivative di H*dl := by
  have hli0 : commutator dl di = 0 := sub_eq_zero.mpr hli.eq
  have he : commutator (H*dl) (B*di) =
      (H*coefficientDerivative dl B+commutator H B*dl)*di+
        B*(H*commutator dl di-coefficientDerivative di H*dl) := by
    unfold coefficientDerivative commutator
    noncomm_ring
  rw [he,hli0]
  noncomm_ring

lemma commutator_zero_first (di H B : A) :
    commutator H (B*di) = commutator H B*di-B*coefficientDerivative di H := by
  unfold coefficientDerivative commutator
  noncomm_ring

lemma commutator_first_zero (dl H C : A) :
    commutator (H*dl) C = commutator H C*dl+H*coefficientDerivative dl C := by
  unfold coefficientDerivative commutator
  noncomm_ring

/-- Exact whole error-expression reduction, with Udag and Tdag as separate
operator letters. Their actual adjunction is an independent native theorem. -/
theorem full_error_expression_reduction (U Udag T Tdag Z Zdag : A) :
    2*commutator Tdag U + 2*commutator Udag T + commutator Udag U -
      2*(U*Z+Zdag*Udag) =
    commutator (2*(Tdag-T)+(Udag-U)) U +
      2*commutator (Udag-U) T - 2*(U*Z+Zdag*Udag) := by
  unfold commutator
  simp only [two_mul, mul_sub, sub_mul, mul_add, add_mul]
  noncomm_ring

def modelFirstOrder (d H : Fin 3 → A) (H0 : A) : A :=
  (∑ l : Fin 3, H l*d l)+H0

def modelSecondOrder (d : Fin 3 → A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (C : A) : A :=
  (∑ i : Fin 3, ∑ j : Fin 3, a i j*d i*d j)+(∑ i : Fin 3, B i*d i)+C

/-- The exact second-base words, with the displayed ordering preserved. -/
def secondBaseWords (d H : Fin 3 → A) (a : Fin 3 → Fin 3 → A) (B : Fin 3 → A) : A :=
  (∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    (H l*coefficientDerivative (d l) (a i j)*d i*d j -
    a i j*coefficientDerivative (d j) (H l)*d i*d l -
    a i j*coefficientDerivative (d i) (H l)*d j*d l)) +
  (∑ l : Fin 3, ∑ i : Fin 3, commutator (H l) (B i)*d l*d i)

def firstBaseWords (d H : Fin 3 → A) (H0 : A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (C : A) : A :=
  -(∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
    a i j*coefficientDerivative (d i) (coefficientDerivative (d j) (H l))*d l) -
  (∑ i : Fin 3, ∑ j : Fin 3, (a i j*coefficientDerivative (d j) H0*d i +
    a i j*coefficientDerivative (d i) H0*d j)) +
  (∑ l : Fin 3, ∑ i : Fin 3, (H l*coefficientDerivative (d l) (B i)*d i -
    B i*coefficientDerivative (d i) (H l)*d l)) +
  (∑ i : Fin 3, commutator H0 (B i)*d i) +
  (∑ l : Fin 3, commutator (H l) C*d l)

def zeroBaseWords (d H : Fin 3 → A) (H0 : A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (C : A) : A :=
  -(∑ i : Fin 3, ∑ j : Fin 3,
    a i j*coefficientDerivative (d i) (coefficientDerivative (d j) H0)) -
  (∑ i : Fin 3, B i*coefficientDerivative (d i) H0) +
  (∑ l : Fin 3, H l*coefficientDerivative (d l) C) + commutator H0 C

/-- Full three-dimensional coefficient words. In an invariant raw smooth
operator domain, coefficientDerivative is the actual base coefficient derivative. -/
theorem first_second_order_commutator_words
    (d H : Fin 3 → A) (H0 : A) (a : Fin 3 → Fin 3 → A) (B : Fin 3 → A) (C : A)
    (hd : ∀ i j, Commute (d i) (d j))
    (hHa : ∀ l i j, Commute (H l) (a i j))
    (hH0a : ∀ i j, Commute H0 (a i j)) :
    commutator (modelFirstOrder d H H0) (modelSecondOrder d a B C) =
      secondBaseWords d H a B + firstBaseWords d H H0 a B C +
        zeroBaseWords d H H0 a B C := by
  have hfs (l i j : Fin 3) := commutator_first_second (d l) (d i) (d j) (H l) (a i j)
    (hHa l i j) (hd l i) (hd l j)
  have hzs (i j : Fin 3) := commutator_zero_second (d i) (d j) H0 (a i j) (hH0a i j)
  have hff (l i : Fin 3) := commutator_first_first (d l) (d i) (H l) (B i) (hd l i)
  simp only [modelFirstOrder,modelSecondOrder,commutator_add_left,commutator_add_right,
    commutator_sum_left,commutator_sum_right]
  simp_rw [hfs,hzs,hff,commutator_zero_first,commutator_first_zero]
  simp only [secondBaseWords,firstBaseWords,zeroBaseWords,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib,neg_mul,Fin.sum_univ_three]
  abel

/-- Exact ordered Leibniz expansion of the UZ term, before taking adjoints. -/
lemma second_coefficient_right_product_words (di dj a Z : A) :
    a*di*dj*Z = a*Z*di*dj +
      (a*coefficientDerivative di Z*dj+a*coefficientDerivative dj Z*di) +
      a*coefficientDerivative di (coefficientDerivative dj Z) := by
  unfold coefficientDerivative commutator
  noncomm_ring

lemma first_coefficient_right_product_words (di B Z : A) :
    B*di*Z = B*Z*di+B*coefficientDerivative di Z := by
  unfold coefficientDerivative commutator
  noncomm_ring

def secondBaseRightProduct (d : Fin 3 → A) (a : Fin 3 → Fin 3 → A) (Z : A) : A :=
  ∑ i : Fin 3, ∑ j : Fin 3, a i j*Z*d i*d j

def firstBaseRightProduct (d : Fin 3 → A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (Z : A) : A :=
  (∑ i : Fin 3, ∑ j : Fin 3, (a i j*coefficientDerivative (d i) Z*d j +
    a i j*coefficientDerivative (d j) Z*d i)) +
  (∑ i : Fin 3, B i*Z*d i)

def zeroBaseRightProduct (d : Fin 3 → A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (C Z : A) : A :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    a i j*coefficientDerivative (d i) (coefficientDerivative (d j) Z)) +
  (∑ i : Fin 3, B i*coefficientDerivative (d i) Z)+C*Z

theorem second_order_right_product_words (d : Fin 3 → A) (a : Fin 3 → Fin 3 → A)
    (B : Fin 3 → A) (C Z : A) :
    modelSecondOrder d a B C*Z = secondBaseRightProduct d a Z +
      firstBaseRightProduct d a B Z+zeroBaseRightProduct d a B C Z := by
  have hs (i j : Fin 3) := second_coefficient_right_product_words (d i) (d j) (a i j) Z
  have hf (i : Fin 3) := first_coefficient_right_product_words (d i) (B i) Z
  simp only [modelSecondOrder,add_mul,Finset.sum_mul]
  simp_rw [hs,hf]
  simp only [secondBaseRightProduct,firstBaseRightProduct,zeroBaseRightProduct,
    Finset.sum_add_distrib,Fin.sum_univ_three]
  abel

end OAI.AnisotropicCalderon.ActualModelCommutatorWords
