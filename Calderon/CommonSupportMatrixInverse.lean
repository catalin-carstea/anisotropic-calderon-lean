import Calderon.CommonSupportInverse

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportMatrixFamily (r : ℕ) (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (ha : ContDiff ℝ ∞ a) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t z, z ∉ K → a (t,z) = 0) (t : H) : SmoothCoefficientMatrix r :=
  commonSupportCoefficientMatrix r (fun i j p => a p i j)
    (fun i j => contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun i j t z h => by rw [hz t z h]; rfl) t

theorem coefficientMatrixField_commonSupportMatrixFamily (r : ℕ)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ t z, z ∉ K → a (t,z) = 0) (t : H) :
    coefficientMatrixField r (commonSupportMatrixFamily r a ha K hK hz t) =
      fun z => a (t,z) :=
  coefficientMatrixField_commonSupportCoefficientMatrix r (fun i j p => a p i j)
    (fun i j => contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun i j t z h => by rw [hz t z h]; rfl) t

theorem exists_uniform_commonSupportMatrixInverse_apply_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ t z, z ∉ K → a (t,z) = 0)
    (q : Set H) (hq : IsCompact q) (lam Lam : ℝ)
    (hUE : ∀ t ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a (t,z)) lam Lam) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ q, ∀ f : BallSobolev s,
      ‖(strongDirichletOperator hcalc s
        (commonSupportMatrixFamily (s+2) a ha K hK hz t)).inverse f‖ ≤ C * ‖f‖ :=
  exists_uniform_commonSupportInverse_apply_bound hcalc hreg s (fun i j p => a p i j)
    (fun i j => contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun i j t z h => by rw [hz t z h]; rfl) q hq (fun _ => lam) (fun _ => Lam) hUE
end OAI.AnisotropicCalderon.DirichletFamily
