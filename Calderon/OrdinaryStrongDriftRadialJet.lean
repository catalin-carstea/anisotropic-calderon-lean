import Calderon.OrdinaryWeightedDriftOperator
import Calderon.MultiplierRadialZeroJet
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem coefficientMultiplier_eq_smul_id_on_ball
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F : SmoothCoefficientJets (k+1)) (c : ℝ)
    (hc : ∀ z ∈ (ballOpens : Set R3), coefficientValue (k+1) F z = c) :
    coefficientMultiplier hcalc k F = c • ContinuousLinearMap.id ℝ (BallSobolev k) := by
  apply ContinuousLinearMap.ext
  intro u
  apply TauCeti.Wkp.ext k
  rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,TauCeti.Wkp.value_smul]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F u,
    Lp.coeFn_smul c (TauCeti.Wkp.value k u),
    ae_restrict_mem ballOpens.isOpen.measurableSet] with z hmul hsmul hz
  rw [hmul,hsmul,hc z hz]
  rfl

section Family
variable (hcalc : FixedSobolevCalculus) (s : ℕ)
  (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
  (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
  (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
  (K : Set R3) (hK : IsCompact K)
  (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
  (L : ℝ)

theorem ordinaryStrongDriftFamily_zero_apply (y : R3)
    (hzero : ∀ z ∈ (ballOpens : Set R3), a ((y,0),z) = 1)
    (E : BallSobolev (s+2)) :
    ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L (y,0) E =
      -∑ i : Fin 3, unitBallCoordinateDerivativeL hcalc s i
        (unitBallCoordinateDerivativeL hcalc (s+1) i E) := by
  have hm (i j : Fin 3) : coefficientMultiplier hcalc (s+1)
      ((commonSupportMatrixFamily (s+2) a ha K hK hza (y,0)) i j) =
      ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) • ContinuousLinearMap.id ℝ (BallSobolev (s+1)) := by
    apply coefficientMultiplier_eq_smul_id_on_ball
    intro z hz
    change coefficientValue (s+2) (commonSupportCoefficientFamily (s+2)
      (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun p z h => by rw [hza p z h]; rfl) (y,0)) z = _
    rw [coefficientValue_commonSupportCoefficientFamily,hzero z hz]
  simp only [ordinaryStrongDriftFamily,ordinaryWeightedDriftL,mul_zero,zero_smul,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,add_zero]
  rw [ordinaryPrincipalL_apply]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [hm i i]
    simp only [Matrix.one_apply_eq, one_smul, ContinuousLinearMap.id_apply]
  · intro j hj hji
    rw [hm i j]
    simp only [Matrix.one_apply_ne (Ne.symm hji), zero_smul,
      ContinuousLinearMap.zero_apply, map_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem contDiff_ordinaryWeightedDriftBaseL :
    ContDiff ℝ ∞ (ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw) := by
  apply ContDiff.sum
  intro i hi
  exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s
    (weightedDriftCoordinate w b i) (contDiff_weightedDriftCoordinate w hw b hb i)
    K hK (weightedDriftCoordinate_support w b K hzw i)).clm_comp contDiff_const

theorem hasDerivAt_ordinaryStrongDriftFamily_zero (y : R3)
    (hzero : ∀ z ∈ (ballOpens : Set R3),
      HasDerivAt (fun r : ℝ => a ((y,r),z)) 0 0) :
    HasDerivAt
      (fun r : ℝ => ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L (y,r))
      ((-L) • ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw (y,0)) 0 := by
  have hm : HasDerivAt (fun r : ℝ => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hza (y,r))) 0 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    let g : ℝ × R3 → ℝ := fun p => a ((y,p.1),p.2) i j
    have hg : ContDiff ℝ ∞ g :=
      (contDiff_pi.mp (contDiff_pi.mp ha i) j).comp
        ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    have hz : ∀ r z, z ∉ K → g (r,z) = 0 := by
      intro r z hz
      change a ((y,r),z) i j = 0
      rw [hza (y,r) z hz]
      rfl
    have hj : ∀ z ∈ (ballOpens : Set R3), HasDerivAt (fun r : ℝ => g (r,z)) 0 0 := by
      intro z hz
      exact hasDerivAt_pi.mp (hasDerivAt_pi.mp (hzero z hz) i) j
    change HasDerivAt (fun r : ℝ => coefficientMultiplier hcalc (s+1)
      (commonSupportCoefficientFamily (s+2) g hg K hK hz r)) 0 0
    exact hasDerivAt_commonSupport_coefficientMultiplier_zero hcalc (s+1) g hg K hK hz hj
  have hP : HasDerivAt (fun r : ℝ => ordinaryPrincipalL hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hza (y,r))) 0 0 := by
    simpa only [ordinaryPrincipalL,ordinaryCoefficientOperatorL,
      ContinuousLinearMap.comp_apply,map_zero,Function.comp_def] using
      (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
        (unitBallCoordinateDerivativeL hcalc (s+1))).hasFDerivAt.comp_hasDerivAt 0 hm
  have hs : ContDiff ℝ ∞ (fun r : ℝ =>
      ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw (y,r)) :=
    (contDiff_ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw).comp
      (show ContDiff ℝ ∞ (fun r : ℝ => (y,r)) from
        contDiff_const.prodMk contDiff_id)
  have hf := (hs.differentiable (by simp) (0 : ℝ)).hasDerivAt
  have hfactor : HasDerivAt (fun r : ℝ => -L*r) (-L) 0 := by
    convert! (hasDerivAt_id' (0 : ℝ)).const_mul (-L) using 1 <;>
      simp only [mul_one]
  have hD := hfactor.smul hf
  convert! hP.add hD using 1 <;>
    simp only [ordinaryStrongDriftFamily, ordinaryWeightedDriftL,
      Pi.add_def, Pi.smul_def', mul_zero, zero_smul, add_zero, zero_add]

theorem ordinaryWeightedDriftBaseL_zero_eq (y : R3) (c : R3)
    (hzero : ∀ z ∈ (ballOpens : Set R3), ∀ i : Fin 3, w ((y,0),z) * b ((y,0),z) i = c i) :
    ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw (y,0) =
      ∑ i : Fin 3, (c i) • ordinaryLowerOrderCoordinateDerivativeL hcalc s i := by
  unfold ordinaryWeightedDriftBaseL
  apply Finset.sum_congr rfl
  intro i hi
  have hm : coefficientMultiplier hcalc s
      (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
        (contDiff_weightedDriftCoordinate w hw b hb i) K hK
        (weightedDriftCoordinate_support w b K hzw i) (y,0)) =
      (c i) • ContinuousLinearMap.id ℝ (BallSobolev s) := by
    apply coefficientMultiplier_eq_smul_id_on_ball
    intro z hz
    rw [coefficientValue_commonSupportCoefficientFamily]
    exact hzero z hz i
  rw [hm]
  ext E
  rfl

end Family
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
