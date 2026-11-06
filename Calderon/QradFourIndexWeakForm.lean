import Calderon.SphereSobolevQuarticCommutatorForm
import Mathlib.Tactic.GCongr

/-! Exact four-index Qrad weak form.
Only boundedness and ring algebra are proved here. The actual strong-domain
pivot identification and the actual uniform coefficient/operator caps are treated
separately. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma commutator_two_products_eq_four_words {A : Type*} [Ring A] (Li Lj Rk Rl : A) :
    (Lj*Li)*(Rk*Rl) - (Rk*Rl)*(Lj*Li) =
      Lj*(Li*Rk-Rk*Li)*Rl + (Lj*Rk-Rk*Lj)*Li*Rl +
      Rk*Lj*(Li*Rl-Rl*Li) + Rk*(Lj*Rl-Rl*Lj)*Li := by
  noncomm_ring

def qradFourIndexWeakForm
    (RH LH : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (LL : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CH : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CL : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (i j k l : Fin 3) (u : SphereSobolev (3/2 : ℝ)) : ℝ :=
  sphereSobolevDualPairing (-(1/2 : ℝ)) (CL i k (RH l u)) (RH j u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (LL i (RH l u)) (CH k j u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (LL j (CH i l u)) (LH k u) +
  sphereSobolevDualPairing (-(1/2 : ℝ)) (CL j l (LH i u)) (LH k u)

lemma abs_sphereSobolevDualPairing_comp_apply_le_uniform
    (A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (B D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hD : ‖D‖ ≤ M)
    (u : SphereSobolev (3/2 : ℝ)) :
    |sphereSobolevDualPairing (-(1/2 : ℝ)) (A (B u)) (D u)| ≤ M^3*‖u‖^2 := by
  calc
    _ ≤ ‖A‖*‖B‖*‖D‖*‖u‖^2 := abs_sphereSobolevDualPairing_comp_apply_le A B D u
    _ ≤ M*M*M*‖u‖^2 := by gcongr
    _ = _ := by ring

lemma abs_qradFourIndexWeakForm_le
    (RH LH : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (LL : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CH : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CL : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hRH : ∀ i, ‖RH i‖ ≤ M) (hLH : ∀ i, ‖LH i‖ ≤ M) (hLL : ∀ i, ‖LL i‖ ≤ M)
    (hCH : ∀ i k, ‖CH i k‖ ≤ M) (hCL : ∀ i k, ‖CL i k‖ ≤ M)
    (i j k l : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    |qradFourIndexWeakForm RH LH LL CH CL i j k l u| ≤ 4*M^3*‖u‖^2 := by
  have h1 := abs_sphereSobolevDualPairing_comp_apply_le_uniform (CL i k) (RH l) (RH j)
    M hM (hCL i k) (hRH l) (hRH j) u
  have h2 := abs_sphereSobolevDualPairing_comp_apply_le_uniform (LL i) (RH l) (CH k j)
    M hM (hLL i) (hRH l) (hCH k j) u
  have h3 := abs_sphereSobolevDualPairing_comp_apply_le_uniform (LL j) (CH i l) (LH k)
    M hM (hLL j) (hCH i l) (hLH k) u
  have h4 := abs_sphereSobolevDualPairing_comp_apply_le_uniform (CL j l) (LH i) (LH k)
    M hM (hCL j l) (hLH i) (hLH k) u
  let a := sphereSobolevDualPairing (-(1/2 : ℝ)) (CL i k (RH l u)) (RH j u)
  let b := sphereSobolevDualPairing (-(1/2 : ℝ)) (LL i (RH l u)) (CH k j u)
  let c := sphereSobolevDualPairing (-(1/2 : ℝ)) (LL j (CH i l u)) (LH k u)
  let d := sphereSobolevDualPairing (-(1/2 : ℝ)) (CL j l (LH i u)) (LH k u)
  have h12 := abs_add_le a b
  have h123 := abs_add_le (a+b) c
  have h1234 := abs_add_le (a+b+c) d
  change |a+b+c+d| ≤ _
  change |a| ≤ _ at h1
  change |b| ≤ _ at h2
  change |c| ≤ _ at h3
  change |d| ≤ _ at h4
  linarith

def qradSignedWeakSelfExpression
    (RH LH : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (LL : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CH : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CL : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (Q : Fin 3 → Fin 3 → ℝ) (r : ℝ) (u : SphereSobolev (3/2 : ℝ)) : ℝ :=
  r^6 * ∑ i, ∑ j, ∑ k, ∑ l, Q i j * Q k l * qradFourIndexWeakForm RH LH LL CH CL i j k l u

lemma abs_qradSignedWeakSelfExpression_le
    (RH LH : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (LL : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CH : Fin 3 → Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CL : Fin 3 → Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (Q : Fin 3 → Fin 3 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hRH : ∀ i, ‖RH i‖ ≤ M) (hLH : ∀ i, ‖LH i‖ ≤ M) (hLL : ∀ i, ‖LL i‖ ≤ M)
    (hCH : ∀ i k, ‖CH i k‖ ≤ M) (hCL : ∀ i k, ‖CL i k‖ ≤ M)
    (hQ : ∀ i j, |Q i j| ≤ M) (r : ℝ) (u : SphereSobolev (3/2 : ℝ)) :
    |qradSignedWeakSelfExpression RH LH LL CH CL Q r u| ≤ 324*M^5*r^6*‖u‖^2 := by
  have hTerm (i j k l : Fin 3) :
      |Q i j * Q k l * qradFourIndexWeakForm RH LH LL CH CL i j k l u| ≤ 4*M^5*‖u‖^2 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ M*M*(4*M^3*‖u‖^2) := by
        gcongr
        exact hQ i j
        exact hQ k l
        exact abs_qradFourIndexWeakForm_le RH LH LL CH CL M hM hRH hLH hLL hCH hCL i j k l u
      _ = _ := by ring
  have hSum : |∑ i, ∑ j, ∑ k, ∑ l,
      Q i j * Q k l * qradFourIndexWeakForm RH LH LL CH CL i j k l u| ≤
      324*M^5*‖u‖^2 := by
    calc
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l,
          |Q i j * Q k l * qradFourIndexWeakForm RH LH LL CH CL i j k l u| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
              Finset.abs_sum_le_sum_abs _ _)))
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ∑ _k : Fin 3, ∑ _l : Fin 3, 4*M^5*‖u‖^2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hTerm i j k l
      _ = _ := by simp; ring
  unfold qradSignedWeakSelfExpression
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ r^6)]
  calc
    _ ≤ r^6*(324*M^5*‖u‖^2) := mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by ring

end OAI.AnisotropicCalderon.SphereHarmonic
