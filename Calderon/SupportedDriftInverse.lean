import Calderon.SupportedDriftOperator
import Calderon.SmoothCommonSupportStrongOperator
import Calderon.CompactDriftInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def commonSupportStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) :
    StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  linearDriftOperatorFamily (fun p => strongDirichletOperator hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hza p)) (commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw) L p

def commonSupportStrongDriftWeightedSolution
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) :
    BallSobolev s →L[ℝ] StrongDirichletSpace s :=
  (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).inverse.comp
    (coefficientMultiplier hcalc s (commonSupportCoefficientFamily (s+1) w hw K hK hzw p))

theorem commonSupportStrongDriftFamily_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) :
    commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p =
      strongDirichletOperator hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hza p) +
        commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hzw L p := rfl

theorem contDiff_commonSupportStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) :
    ContDiff ℝ ∞ (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L) :=
  contDiff_linearDriftOperatorFamily _ _
    (contDiff_commonSupport_actual_strongDirichletOperator hcalc s a ha K hK hza)
    (contDiff_commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw) L

theorem exists_commonSupport_smallRadius_strongDrift_inverse
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ)
    (q : Set R3) (hq : IsCompact q) (lam Lam : R3 → ℝ)
    (hUE : ∀ y ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((y,0),z)) (lam y) (Lam y)) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      (∀ p ∈ q ×ˢ Icc (-delta) delta, (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun p => (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).inverse) (q ×ˢ Icc (-delta) delta) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ f : BallSobolev s,
        ‖(commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).inverse f‖ ≤ C*‖f‖) ∧
      (∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q ×ˢ Icc (-delta) delta,
        ‖iteratedFDeriv ℝ j (fun t => (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L t).inverse) p‖ ≤ C) ∧
      ContDiffOn ℝ ∞ (commonSupportStrongDriftWeightedSolution hcalc s a ha w hw b hb K hK hza hzw L) (q ×ˢ Icc (-delta) delta) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ q ×ˢ Icc (-delta) delta,
        ‖iteratedFDeriv ℝ j (commonSupportStrongDriftWeightedSolution hcalc s a ha w hw b hb K hK hza hzw L) p‖ ≤ C := by
  let A : R3 × ℝ → StrongDirichletSpace s →L[ℝ] BallSobolev s := fun p => strongDirichletOperator hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hza p)
  let D : R3 × ℝ → StrongDirichletSpace s →L[ℝ] BallSobolev s := commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw
  let W : R3 × ℝ → BallSobolev s →L[ℝ] BallSobolev s := fun p => coefficientMultiplier hcalc s (commonSupportCoefficientFamily (s+1) w hw K hK hzw p)
  have hA := contDiff_commonSupport_actual_strongDirichletOperator hcalc s a ha K hK hza
  have hD := contDiff_commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw
  have hW := contDiff_commonSupport_actual_coefficientMultiplier hcalc s w hw K hK hzw
  have hi (y : R3) (hy : y ∈ q) : (A (y,0)).IsInvertible := by
    apply strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE y hy
  exact exists_compact_smallRadius_linearDrift_weighted_inverse A D hA hD W hW L q hq hi eta heta

theorem commonSupportStrongDriftWeightedSolution_equation
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ)
    (hi : (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).IsInvertible) (f : BallSobolev s) :
    commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p (commonSupportStrongDriftWeightedSolution hcalc s a ha w hw b hb K hK hza hzw L p f) =
      coefficientMultiplier hcalc s (commonSupportCoefficientFamily (s+1) w hw K hK hzw p) f := by
  exact hi.self_apply_inverse _
end OAI.AnisotropicCalderon.DirichletFamily
