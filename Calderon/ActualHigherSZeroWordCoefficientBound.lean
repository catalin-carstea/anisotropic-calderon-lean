import Calderon.ActualHigherSQuadraticZeroWords

/-! Scalar bound for every original zero-word coefficient. The declaration
retains its original namespace and exact hypotheses; no physical endpoint or
pairing context is required. AUTHOR REPAIR UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
open ActualHigherSQuadraticZeroWords

lemma abs_wordCoefficient_le_common (r beta M : ℝ) (Q : Fin 3 → Fin 3 → ℝ)
    (f : Fin 3 → ℝ) (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ beta) (hM : 1 ≤ M) (hs : r*beta^2 ≤ 1)
    (hQ : ∀ i j, |Q i j| ≤ M) (hf : ∀ i, |f i| ≤ M*beta)
    (hΓ : ∀ i a b, |Γ i a b| ≤ M) (z : ZeroWord) :
    |wordCoefficient r Q f Γ z| ≤ M^2*r := by
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hb12 : beta ≤ beta^2 := by nlinarith only [hb]
  have hr1 : r ≤ 1 := (calc
    r = r*1 := (mul_one r).symm
    _ ≤ r*beta^2 := mul_le_mul_of_nonneg_left hb2 hr).trans hs
  have hrb : r*beta ≤ 1 := (mul_le_mul_of_nonneg_left hb12 hr).trans hs
  have hr2 : r^2 ≤ r := by nlinarith
  have hr3 : r^3 ≤ r := by
    calc
      r^3 = r^2*r := by ring
      _ ≤ r*r := mul_le_mul_of_nonneg_right hr2 hr
      _ ≤ r := by nlinarith
  have hfScaled (i : Fin 3) : r*|f i| ≤ M := by
    calc
      _ ≤ r*(M*beta) := mul_le_mul_of_nonneg_left (hf i) hr
      _ = M*(r*beta) := by ring
      _ ≤ M*1 := mul_le_mul_of_nonneg_left hrb hM0
      _ = M := mul_one _
  have hRot (i j k a b : Fin 3) : |(r^2/2)*Q i j*Γ k a b| ≤ M^2*r := by
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (sq_nonneg r)]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ (r^2/2)*M*M := by gcongr; exacts [hQ i j, hΓ k a b]
      _ = (r^2/2)*M^2 := by ring
      _ ≤ r*M^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg M)
      _ = M^2*r := mul_comm _ _
  have hDegree (i j k : Fin 3) : |r^2*Q i j*f k| ≤ M^2*r := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc
      _ = r*|Q i j| *(r*|f k|) := by ring
      _ ≤ r*M*M := by gcongr; exacts [hQ i j, hfScaled k]
      _ = M^2*r := by ring
  have hRaise (i j : Fin 3) : |r*Q i j| ≤ M^2*r := by
    rw [abs_mul, abs_of_nonneg hr]
    calc
      _ ≤ r*M := mul_le_mul_of_nonneg_left (hQ i j) hr
      _ ≤ r*M^2 := mul_le_mul_of_nonneg_left (by nlinarith) hr
      _ = M^2*r := mul_comm _ _
  have hDouble (i j : Fin 3) : |r^3*Q i j| ≤ M^2*r := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr 3)]
    calc
      _ ≤ r^3*M := mul_le_mul_of_nonneg_left (hQ i j) (pow_nonneg hr 3)
      _ ≤ r*M := mul_le_mul_of_nonneg_right hr3 hM0
      _ ≤ r*M^2 := mul_le_mul_of_nonneg_left (by nlinarith) hr
      _ = M^2*r := mul_comm _ _
  rcases z with ⟨⟨i,j⟩, kind⟩
  cases kind with
  | inl ab => exact hRot i j i ab.1 ab.2
  | inr kind =>
    cases kind with
    | inl ab => exact hRot i j j ab.1 ab.2
    | inr m =>
      simp only [wordCoefficient]
      split_ifs
      · exact hDegree i j i
      · exact hDegree i j j
      · exact hRaise i j
      · exact hRaise i j
      · exact hDouble i j

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
