import Calderon.ClosedCoefficientMultiplier
import Calderon.CommonSupportMatrixInverse

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem contDiff_commonSupport_actual_strongDirichletOperator
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => strongDirichletOperator hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s+1)
      (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun p z h => by rw [hz p z h]; rfl)
  change ContDiff ℝ ∞ (fun p => unitBallDivergenceL hcalc s
    (coefficientMatrixMultiplierL hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hz p)))
  exact (unitBallDivergenceL hcalc s).contDiff.comp hm

theorem contDiffOn_commonSupport_actual_strongDirichletInverse
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → a (p,z) = 0)
    (q : Set H) (lam Lam : H → ℝ)
    (hUE : ∀ p ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a (p,z)) (lam p) (Lam p)) :
    ContDiffOn ℝ ∞ (fun p => (strongDirichletOperator hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)).inverse) q := by
  apply contDiffOn_banachInverseFamily _ q
    (contDiff_commonSupport_actual_strongDirichletOperator hcalc s a ha K hK hz).contDiffOn
  intro p hp
  apply strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  exact hUE p hp
end OAI.AnisotropicCalderon.DirichletFamily
