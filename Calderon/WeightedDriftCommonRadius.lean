import Calderon.DriftRegularityBootstrap
import Calderon.SupportedDriftInverse
import Calderon.WeightedRadialDriftCoercivity
import Calderon.WeightedDriftSlice
import Calderon.OrdinaryWeightedDriftOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem commonSupportWeightedDriftOperator_apply_eq_ordinaryWeightedDriftL
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z) = 0)
    (L : ℝ) (p : R3 × ℝ) (U : StrongDirichletSpace s) :
    commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L p U =
      ordinaryWeightedDriftL hcalc s w hw b hb K hK hz L p
        (U : BallSobolev (s + 2)) := by
  exact (congrArg (fun T : StrongDirichletSpace s →L[ℝ] BallSobolev s => T U)
    (ordinaryWeightedDriftL_restriction hcalc s w hw b hb K hK hz L p)).symm

theorem commonSupportWeightedDriftOperator_value_eq_projection
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z) = 0)
    (L : ℝ) (p : R3 × ℝ) (U : StrongDirichletSpace s) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L p U) =
      supportedDriftL hcalc 0 (weightedDriftSlice w b L p)
        (contDiff_weightedDriftSlice w hw b hb L p) K hK
        (weightedDriftSlice_support w b L p K hz)
        (strongDirichletProjectionL s U : BallH1) := by
  have hRestriction := commonSupportWeightedDriftOperator_apply_eq_ordinaryWeightedDriftL
    hcalc s w hw b hb K hK hz L p U
  have hValue := congrArg (fun V : BallSobolev s =>
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s V)
    hRestriction
  have hOrdinary := ordinaryWeightedDriftL_value_eq hcalc s w hw b hb K hK hz L p
    (U : BallSobolev (s + 2))
  have hProjection := congrArg (fun u : BallH1 =>
    supportedDriftL hcalc 0 (weightedDriftSlice w b L p)
      (contDiff_weightedDriftSlice w hw b hb L p) K hK
      (weightedDriftSlice_support w b L p K hz) u)
    (strongDirichletProjectionL_apply s U).symm
  exact hValue.trans (hOrdinary.trans hProjection)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The new one-order construction is exactly the already-defined weighted strong drift. -/
theorem commonSupportWeightedDriftOperator_eq_supportedStrongDriftL
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z) = 0)
    (L : ℝ) (p : R3 × ℝ) :
    commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L p =
      supportedStrongDriftL hcalc s (weightedDriftSlice w b L p)
        (contDiff_weightedDriftSlice w hw b hb L p) K hK
        (weightedDriftSlice_support w b L p K hz) := by
  apply ContinuousLinearMap.ext
  intro U
  apply TauCeti.Wkp.ext s
  exact (commonSupportWeightedDriftOperator_value_eq_projection hcalc s w hw b hb K hK hz L p U).trans
    (supportedStrongDriftL_value_eq hcalc s (weightedDriftSlice w b L p)
      (contDiff_weightedDriftSlice w hw b hb L p) K hK
      (weightedDriftSlice_support w b L p K hz) U).symm

theorem commonSupportStrongDriftFamily_eq_supportedStrongOperatorL
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
    (L : ℝ) (p : R3 × ℝ) :
    commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p =
      supportedStrongOperatorL hcalc s (commonSupportMatrixFamily (s + 2) a ha K hK hza p)
        (weightedDriftSlice w b L p) (contDiff_weightedDriftSlice w hw b hb L p) K hK
        (weightedDriftSlice_support w b L p K hzw) := by
  rw [commonSupportStrongDriftFamily_eq,
    commonSupportWeightedDriftOperator_eq_supportedStrongDriftL]
  rfl

/-- One actual weak-coercive radius precedes every strong Sobolev order and jet order.
No order-uniform estimate is asserted: each (s,N) has its own compact bound. -/
theorem exists_commonRadius_allOrder_strongDrift_inverse
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
    (L : ℝ) (q : Set R3) (hq : IsCompact q) (eta lam Lam : ℝ)
    (heta : 0 < eta) (hlam : 0 < lam)
    (hUE : ∀ p ∈ q ×ˢ Icc (-eta) eta, TauCeti.PDE.UniformlyEllipticOn
      (ballOpens : Set R3) (fun z => a (p,z)) lam Lam) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧ ∀ s : ℕ,
      (∀ p ∈ q ×ˢ Icc (-delta) delta,
        (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).IsInvertible) ∧
      ContDiffOn ℝ ∞ (fun p =>
        (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).inverse)
        (q ×ˢ Icc (-delta) delta) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ f : BallSobolev s,
        ‖(commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).inverse f‖
          ≤ C * ‖f‖) ∧
      (∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ q ×ˢ Icc (-delta) delta,
          ‖iteratedFDeriv ℝ j (fun t =>
            (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L t).inverse) p‖
              ≤ C) ∧
      ContDiffOn ℝ ∞
        (commonSupportStrongDriftWeightedSolution hcalc s a ha w hw b hb K hK hza hzw L)
        (q ×ˢ Icc (-delta) delta) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ q ×ˢ Icc (-delta) delta,
          ‖iteratedFDeriv ℝ j
            (commonSupportStrongDriftWeightedSolution hcalc s a ha w hw b hb K hK hza hzw L) p‖
              ≤ C := by
  obtain ⟨delta, hd, hdeta, hweak⟩ := exists_compact_smallRadius_weightedDrift_coercivity
    a ha w hw b hb L q hq eta lam Lam heta hlam hUE
  refine ⟨delta, hd, hdeta, ?_⟩
  intro s
  let A := commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L
  let W : R3 × ℝ → BallSobolev s →L[ℝ] BallSobolev s := fun p =>
    coefficientMultiplier hcalc s (commonSupportCoefficientFamily (s + 1) w hw K hK hzw p)
  let S : Set (R3 × ℝ) := q ×ˢ Icc (-delta) delta
  have hS : IsCompact S := hq.prod isCompact_Icc
  have hA : ContDiff ℝ ∞ A :=
    contDiff_commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L
  have hW : ContDiff ℝ ∞ W :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc s w hw K hK hzw
  have hi : ∀ p ∈ S, (A p).IsInvertible := by
    intro p hp
    have hpeta : p ∈ q ×ˢ Icc (-eta) eta :=
      ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    change (commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).IsInvertible
    rw [commonSupportStrongDriftFamily_eq_supportedStrongOperatorL]
    apply supportedStrongOperatorL_isInvertible hcalc hreg s _ lam Lam
    · rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact hUE p hpeta
    · exact (hweak p hp).1
  obtain ⟨C, hC, hnorm⟩ := uniform_norm_banachInverseFamily A S hS hA.continuous.continuousOn hi
  refine ⟨hi, contDiffOn_banachInverseFamily A S hA.contDiffOn hi,
    ⟨C, hC, ?_⟩, ?_, ?_, ?_⟩
  · intro p hp f
    exact ((A p).inverse.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (hnorm p hp) (norm_nonneg f))
  · intro N
    exact exists_compact_banachInverse_derivative_bound A hA S hS hi N
  · exact contDiffOn_banachWeightedInverse A W S hA.contDiffOn hi hW.contDiffOn
  · intro N
    exact exists_compact_banachWeightedInverse_derivative_bound A hA W hW S hS hi N

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
