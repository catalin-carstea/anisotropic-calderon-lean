import Calderon.ActualHigherSMixedWordScalarJetAlgebra

/-! Typed scalar first-jet products and finite cleared-word smoothness. All actual
geometry caps are discharged by the original-data factory, not assumed there. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
open EnergyBridge ConnectionError ConformalDepth ReferenceWeightedApproximation
  ActualHigherSQuadraticZeroWords

lemma scalarPointJet_radius_sq_weight_word
    (R W Z : R3 → ℝ) (x : R3) (r beta M Cw Cs : ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ beta) (hM : 0 ≤ M) (hCw : 0 ≤ Cw)
    (hValue : M*Cw ≤ Cs) (hDerivative : Cw*(2*M+2*M^2) ≤ Cs)
    (hR : ScalarPointJet R x r (M*r*beta))
    (hW : ScalarPointJet W x M M)
    (hZ : ScalarPointJet Z x (Cw*r) (Cw*r*beta)) :
    ScalarPointJet (fun y => R y^2*W y*Z y) x (Cs*r^3) (Cs*r^3*beta) := by
  have hProduct : ScalarPointJet (fun y => R y^2*W y*Z y) x
      ((r^2*M)*(Cw*r))
      ((r^2*M)*(Cw*r*beta)+(Cw*r)*(r^2*M+M*(2*r*(M*r*beta)))) :=
    (hR.pow_two.mul hW).mul hZ
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hRadius : r^3 ≤ r^3*beta := le_mul_of_one_le_right (pow_nonneg hr 3) hb
  refine hProduct.mono ?_ ?_
  · calc
      _ = (M*Cw)*r^3 := by ring
      _ ≤ Cs*r^3 := mul_le_mul_of_nonneg_right hValue (pow_nonneg hr 3)
  · calc
      _ = (M*Cw)*(r^3*beta)+(M*Cw)*r^3+(2*M^2*Cw)*(r^3*beta) := by ring
      _ ≤ (M*Cw)*(r^3*beta)+(M*Cw)*(r^3*beta)+(2*M^2*Cw)*(r^3*beta) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hRadius (mul_nonneg hM hCw))) le_rfl
      _ = (Cw*(2*M+2*M^2))*(r^3*beta) := by ring
      _ ≤ Cs*(r^3*beta) := mul_le_mul_of_nonneg_right hDerivative
        (mul_nonneg (pow_nonneg hr 3) hb0)
      _ = Cs*r^3*beta := by ring

lemma contDiff_clearedWordCoefficient
    (R : R3 → ℝ) (Q : Fin 3 → Fin 3 → R3 → ℝ)
    (X : Fin 3 → R3 → R3) (Γ : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ)
    (hR : ContDiff ℝ ∞ R) (hQ : ∀ i j, ContDiff ℝ ∞ (Q i j))
    (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hΓ : ∀ i a b, ContDiff ℝ ∞ (Γ i a b))
    (z : ZeroWord) : ContDiff ℝ ∞ (clearedWordCoefficient R Q X Γ z) := by
  have hRD : ContDiff ℝ ∞ (fderiv ℝ R) := hR.fderiv_right (by simp)
  have hV (i : Fin 3) : ContDiff ℝ ∞ (fun x => fderiv ℝ R x (X i x)) := hRD.clm_apply (hX i)
  rcases z with ⟨⟨i,j⟩,kind⟩
  cases kind with
  | inl ab =>
    change ContDiff ℝ ∞ (fun x => (R x^2/2)*Q i j x*Γ i ab.1 ab.2 x)
    exact (((hR.pow 2).div_const 2).mul (hQ i j)).mul (hΓ i ab.1 ab.2)
  | inr kind =>
    cases kind with
    | inl ab =>
      change ContDiff ℝ ∞ (fun x => (R x^2/2)*Q i j x*Γ j ab.1 ab.2 x)
      exact (((hR.pow 2).div_const 2).mul (hQ i j)).mul (hΓ j ab.1 ab.2)
    | inr m =>
      change ContDiff ℝ ∞ (fun x =>
        if m = 0 then R x*Q i j x*(fderiv ℝ R x (X i x)) else
        if m = 1 then R x*Q i j x*(fderiv ℝ R x (X j x)) else
        if m = 2 then R x*Q i j x else
        if m = 3 then R x*Q i j x else R x^3*Q i j x)
      split_ifs
      · exact (hR.mul (hQ i j)).mul (hV i)
      · exact (hR.mul (hQ i j)).mul (hV j)
      · exact hR.mul (hQ i j)
      · exact hR.mul (hQ i j)
      · exact (hR.pow 3).mul (hQ i j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedWordScalarJets
