import Calderon.ActualStrongInverse
import Calderon.CoefficientMatrixRegularity
import Calderon.BanachInverseFamily

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem strongDirichletOperator_isInvertible_of_elliptic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) F) lam Lam) :
    (strongDirichletOperator hcalc s F).IsInvertible :=
  strongDirichletOperator_isInvertible hcalc hreg s F
    (contDiffOn_coefficientMatrixField_closedBall (s + 2) F) ha
    (aestronglyMeasurable_coefficientMatrixField (s + 2) F)
    (memLp_coefficientMatrixEnergyIntegrand (s + 2) F ha)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_strongDirichletOperatorFamily {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : E → SmoothCoefficientMatrix (s + 2)) (q : Set E)
    (hF : ContDiffOn ℝ n F q) :
    ContDiffOn ℝ n (fun x => strongDirichletOperator hcalc s (F x)) q :=
  by
    simpa only [strongDirichletOperator_eq] using
      (contDiffOn_strongCoefficientOperator hcalc s F q hF)

theorem contDiffOn_strongDirichletInverseFamily {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : E → SmoothCoefficientMatrix (s + 2)) (q : Set E)
    (hF : ContDiffOn ℝ n F q) (lam Lam : E → ℝ)
    (hUE : ∀ x ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) (F x)) (lam x) (Lam x)) :
    ContDiffOn ℝ n (fun x => (strongDirichletOperator hcalc s (F x)).inverse) q :=
  contDiffOn_banachInverseFamily _ q
    (contDiffOn_strongDirichletOperatorFamily hcalc s F q hF)
    (fun x hx => strongDirichletOperator_isInvertible_of_elliptic
      hcalc hreg s (F x) (hUE x hx))

theorem exists_uniform_strongDirichletInverseFamily_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : E → SmoothCoefficientMatrix (s + 2)) (q : Set E) (hq : IsCompact q)
    (hF : ContinuousOn F q) (lam Lam : E → ℝ)
    (hUE : ∀ x ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) (F x)) (lam x) (Lam x)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ q, ‖(strongDirichletOperator hcalc s (F x)).inverse‖ ≤ C := by
  apply uniform_norm_banachInverseFamily _ q hq
  · exact (strongCoefficientOperatorL hcalc s).continuous.comp_continuousOn hF
  · intro x hx
    exact strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s (F x) (hUE x hx)

theorem exists_uniform_strongDirichletInverseFamily_apply_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : E → SmoothCoefficientMatrix (s + 2)) (q : Set E) (hq : IsCompact q)
    (hF : ContinuousOn F q) (lam Lam : E → ℝ)
    (hUE : ∀ x ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) (F x)) (lam x) (Lam x)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ q, ∀ f : BallSobolev s,
      ‖(strongDirichletOperator hcalc s (F x)).inverse f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_strongDirichletInverseFamily_bound
    hcalc hreg s F q hq hF lam Lam hUE
  refine ⟨C, hC, fun x hx f => ?_⟩
  exact ((strongDirichletOperator hcalc s (F x)).inverse.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg f))

end OAI.AnisotropicCalderon.DirichletFamily
