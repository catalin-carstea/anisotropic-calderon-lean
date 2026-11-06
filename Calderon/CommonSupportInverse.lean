import Calderon.CoefficientJetFamily
import Calderon.StrongInverseFamily

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportCoefficientMatrix (r : ℕ) (g : Fin 3 → Fin 3 → H × R3 → ℝ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0) (t : H) : SmoothCoefficientMatrix r :=
  fun i j => commonSupportCoefficientFamily r (g i j) (hg i j) K hK (hz i j) t

theorem coefficientMatrixField_commonSupportCoefficientMatrix (r : ℕ)
    (g : Fin 3 → Fin 3 → H × R3 → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0) (t : H) :
    coefficientMatrixField r (commonSupportCoefficientMatrix r g hg K hK hz t) =
      fun x i j => g i j (t,x) := by
  funext x i j
  exact coefficientValue_commonSupportCoefficientFamily r (g i j) (hg i j) K hK (hz i j) t x

theorem continuous_commonSupportCoefficientMatrix (r : ℕ)
    (g : Fin 3 → Fin 3 → H × R3 → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0) :
    Continuous (commonSupportCoefficientMatrix r g hg K hK hz) :=
  continuous_pi (fun i => continuous_pi (fun j =>
    continuous_commonSupportCoefficientFamily r (g i j) (hg i j) K hK (hz i j)))

theorem exists_uniform_commonSupportInverse_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (g : Fin 3 → Fin 3 → H × R3 → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0)
    (q : Set H) (hq : IsCompact q) (lam Lam : H → ℝ)
    (hUE : ∀ t ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun x i j => g i j (t,x)) (lam t) (Lam t)) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ q,
      ‖(strongDirichletOperator hcalc s
        (commonSupportCoefficientMatrix (s + 2) g hg K hK hz t)).inverse‖ ≤ C := by
  apply exists_uniform_strongDirichletInverseFamily_bound hcalc hreg s _ q hq
    (continuous_commonSupportCoefficientMatrix _ g hg K hK hz).continuousOn lam Lam
  intro t ht
  rw [coefficientMatrixField_commonSupportCoefficientMatrix]
  exact hUE t ht

theorem exists_uniform_commonSupportInverse_apply_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (g : Fin 3 → Fin 3 → H × R3 → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0)
    (q : Set H) (hq : IsCompact q) (lam Lam : H → ℝ)
    (hUE : ∀ t ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun x i j => g i j (t,x)) (lam t) (Lam t)) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ q, ∀ f : BallSobolev s,
      ‖(strongDirichletOperator hcalc s
        (commonSupportCoefficientMatrix (s + 2) g hg K hK hz t)).inverse f‖ ≤ C * ‖f‖ := by
  obtain ⟨C,hC,hb⟩ := exists_uniform_commonSupportInverse_bound
    hcalc hreg s g hg K hK hz q hq lam Lam hUE
  refine ⟨C,hC,fun t ht f => ?_⟩
  exact ((strongDirichletOperator hcalc s
    (commonSupportCoefficientMatrix (s + 2) g hg K hK hz t)).inverse.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg f))

end OAI.AnisotropicCalderon.DirichletFamily
