import Calderon.ActualHigherSLeadingWeightedJetBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingGainedSecondForm
open PrincipalCommutator ReferenceDensityBounds ActualScalarPrincipalAdjoint
  ActualHigherSScalarCommutatorForm ActualHigherSLeadingWeightedJetBounds
  ActualHigherSScalarCommutatorCoefficients ActualScalarPrincipalSelfFormBound

/-- Depends only on the uniform scalar/operator/radius-jet constants, before profiles. -/
def leadingCoefficientBudget (M B0 B1 J : ℝ) : ℝ :=
  (9*M^2*B0)+(9*(2*M^2*B0+M^2*B1)+4*J*(9*M^2*B0))

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def weightedGainedCoefficient (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → (E →L[ℝ] F)) (x : R3) : E →L[ℝ] F :=
  (-(R x)^4) • (∑ i : Fin 3, ∑ j : Fin 3, (a i x*b j x) • G i j x)

/-- The true derivative calculus yields exactly the two coefficient caps needed for one base IBP. -/
theorem weightedGainedCoefficient_form_caps
    (M B0 B1 J : ℝ) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hJ : 0 ≤ J)
    (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → (E →L[ℝ] F)) (x : R3)
    (hR : ContDiffAt ℝ ∞ R x) (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (G i j) x)
    (h0a : ∀ i, ‖a i x‖ ≤ M) (h1a : ∀ i, ‖fderiv ℝ (a i) x‖ ≤ M)
    (h0b : ∀ j, ‖b j x‖ ≤ M) (h1b : ∀ j, ‖fderiv ℝ (b j) x‖ ≤ M)
    (h0G : ∀ i j, ‖G i j x‖ ≤ B0) (h1G : ∀ i j, ‖fderiv ℝ (G i j) x‖ ≤ B1)
    (beta eps : ℝ) (hr : 0 ≤ R x) (hbeta : 1 ≤ beta) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hsmall : R x*beta^2 ≤ eps) (hjet : ‖fderiv ℝ R x‖ ≤ J*R x*beta) :
    ContDiffAt ℝ ∞ (weightedGainedCoefficient R a b G) x ∧
      ‖weightedGainedCoefficient R a b G x‖ ≤ leadingCoefficientBudget M B0 B1 J*eps/beta ∧
      ‖fderiv ℝ (weightedGainedCoefficient R a b G) x‖ ≤ leadingCoefficientBudget M B0 B1 J*eps := by
  let A := 9*M^2*B0
  let B := 9*(2*M^2*B0+M^2*B1)
  let Q := leadingCoefficientBudget M B0 B1 J
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAQ : A ≤ Q := by
    change A ≤ A+(B+4*J*A)
    exact le_add_of_nonneg_right (add_nonneg hB (by positivity))
  have hBQ : B+4*J*A ≤ Q := by
    change B+4*J*A ≤ A+(B+4*J*A)
    exact le_add_of_nonneg_left hA
  have hW : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y) x := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact ((ha i).mul (hb j)).smul (hG i j)
  have hCaps := weighted_family_first_caps a b G x
    (fun i => (ha i).differentiableAt (by simp)) (fun i => (hb i).differentiableAt (by simp))
    (fun i j => (hG i j).differentiableAt (by simp)) M B0 B1 hM hB0 hB1 h0a h1a h0b h1b h0G h1G
  have hRad := negative_radius_four_first_caps R
    (fun y => ∑ i : Fin 3, ∑ j : Fin 3, (a i y*b j y) • G i j y) x
    (hR.differentiableAt (by simp)) (hW.differentiableAt (by simp)) A B J beta hA hB hJ hr hbeta
    hCaps.1 hCaps.2 hjet
  have hAtt := radius_four_absorption (R x) beta eps hr hbeta heps1 hsmall
  have hb0 : 0 ≤ beta := by linarith
  have hbpos : 0 < beta := by linarith
  refine ⟨((hR.pow 4).neg).smul hW,?_,?_⟩
  · calc
      _ ≤ A*(R x)^4 := hRad.1
      _ ≤ A*(eps/beta) := mul_le_mul_of_nonneg_left hAtt.1 hA
      _ ≤ Q*(eps/beta) := mul_le_mul_of_nonneg_right hAQ (div_nonneg heps hb0)
      _ = _ := by ring
  · calc
      _ ≤ (B+4*J*A)*(R x)^4*beta := hRad.2
      _ = (B+4*J*A)*((R x)^4*beta) := by ring
      _ ≤ (B+4*J*A)*eps := mul_le_mul_of_nonneg_left hAtt.2 (by positivity)
      _ ≤ Q*eps := mul_le_mul_of_nonneg_right hBQ heps
end Generic

section Form
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The complete leading gained two-base row is small in the original weighted coordinate energy. -/
theorem leading_gained_second_form_bound
    (M B0 B1 J : ℝ) (hM : 0 ≤ M) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hJ : 0 ≤ J)
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu beta : R3 → ℝ) (u : R3 → E)
    (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G : Fin 3 → Fin 3 → R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ContDiff ℝ ∞ mu) (hbcont : Continuous beta) (hbpos : ∀ x, 0 < beta x)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hR : ∀ x ∈ K, ContDiffAt ℝ ∞ R x)
    (ha : ∀ i, ∀ x ∈ K, ContDiffAt ℝ ∞ (a i) x)
    (hb : ∀ i, ∀ x ∈ K, ContDiffAt ℝ ∞ (b i) x)
    (hG : ∀ i j, ∀ x ∈ K, ContDiffAt ℝ ∞ (G i j) x)
    (h0a : ∀ i, ∀ x ∈ K, ‖a i x‖ ≤ M) (h1a : ∀ i, ∀ x ∈ K, ‖fderiv ℝ (a i) x‖ ≤ M)
    (h0b : ∀ j, ∀ x ∈ K, ‖b j x‖ ≤ M) (h1b : ∀ j, ∀ x ∈ K, ‖fderiv ℝ (b j) x‖ ≤ M)
    (h0G : ∀ i j, ∀ x ∈ K, ‖G i j x‖ ≤ B0) (h1G : ∀ i j, ∀ x ∈ K, ‖fderiv ℝ (G i j) x‖ ≤ B1)
    (eps Md : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hMd : 0 ≤ Md)
    (hmu : ∀ x, 0 ≤ mu x) (hbeta : ∀ x ∈ K, 1 ≤ beta x)
    (hr : ∀ x ∈ K, 0 ≤ R x) (hsmall : ∀ x ∈ K, R x*(beta x)^2 ≤ eps)
    (hjet : ∀ x ∈ K, ‖fderiv ℝ R x‖ ≤ J*R x*beta x) (i j : Fin 3)
    (hdmu : ∀ x ∈ K, |directionalFDeriv (coordinateDirection i) mu x| ≤ Md*mu x) :
    Integrable (fun x => mu x*P (u x)
      (weightedGainedCoefficient R a b G x (directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection j) u) x))) ∧
    |∫ x, mu x*P (u x) (weightedGainedCoefficient R a b G x
      (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x))| ≤
      (‖P‖*leadingCoefficientBudget M B0 B1 J*(Md+3)*eps)*coordinateEnergy coordinateDirection mu beta u := by
  have hc (x : R3) (hx : x ∈ K) := weightedGainedCoefficient_form_caps M B0 B1 J hM hB0 hB1 hJ
    R a b G x (hR x hx) (fun i => ha i x hx) (fun i => hb i x hx) (fun i j => hG i j x hx)
    (fun i => h0a i x hx) (fun i => h1a i x hx) (fun i => h0b i x hx) (fun i => h1b i x hx)
    (fun i j => h0G i j x hx) (fun i j => h1G i j x hx)
    (beta x) eps (hr x hx) (hbeta x hx) heps heps1 (hsmall x hx) (hjet x hx)
  refine weighted_second_operator_form_bound P mu beta u (weightedGainedCoefficient R a b G) K hK
    hm hbcont hbpos hu h0 (fun x hx => (hc x hx).1) (leadingCoefficientBudget M B0 B1 J) Md eps
    (by unfold leadingCoefficientBudget; positivity) hMd heps hmu hbeta i j
    (fun x hx => (hc x hx).2.1) ?_ hdmu
  intro x hx
  calc
    _ ≤ ‖fderiv ℝ (weightedGainedCoefficient R a b G) x‖*‖coordinateDirection i‖ :=
      (fderiv ℝ (weightedGainedCoefficient R a b G) x).le_opNorm _
    _ = ‖fderiv ℝ (weightedGainedCoefficient R a b G) x‖ := by rw [norm_coordinateDirection,mul_one]
    _ ≤ _ := (hc x hx).2.2
end Form
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSLeadingGainedSecondForm
