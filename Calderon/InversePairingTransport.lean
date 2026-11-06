import Calderon.NativeHalfCoefficientInverseCompatibility

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/repair-v077-v004/
EXPANSION-same-statement-v004.md. Pure function inverse transport, no analytic premise. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ConnectionError

lemma pairing_inverse_eq_of_forward_pairing {E F V : Type*}
    (pairing : F → E → V) (M : E → E) (N : F → F) (W : E → E) (Z : F → F)
    (hM : ∀ x, M (W x) = x) (hN : ∀ y, N (Z y) = y)
    (hPair : ∀ y x, pairing (N y) x = pairing y (M x)) (y : F) (x : E) :
    pairing (Z y) x = pairing y (W x) := by
  have h := hPair (Z y) (W x)
  rw [hN y,hM x] at h
  exact h.symm

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.pairing_inverse_eq_of_forward_pairing
