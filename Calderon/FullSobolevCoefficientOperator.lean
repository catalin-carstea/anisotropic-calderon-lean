import Calderon.SupportedDriftInverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def fullCoefficientOperatorL (hcalc : FixedSobolevCalculus) (s : ℕ) :
    SmoothCoefficientMatrix (s+2) →L[ℝ] BallSobolev (s+2) →L[ℝ] BallSobolev s :=
  (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
    (unitBallCoordinateDerivativeL hcalc (s+1))).comp (coefficientMatrixMultiplierL hcalc s)

theorem fullCoefficientOperatorL_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s+2)) :
    fullCoefficientOperatorL hcalc s F = -∑ i, ∑ j,
      ((unitBallCoordinateDerivativeL hcalc s i).comp
        (coefficientMultiplier hcalc (s+1) (F i j))).comp
          (unitBallCoordinateDerivativeL hcalc (s+1) j) := by
  exact coefficientDivergenceL_apply _ _ _

theorem fullCoefficientOperatorL_apply_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s+2)) (u : BallSobolev (s+2)) :
    fullCoefficientOperatorL hcalc s F u = -∑ i, ∑ j,
      unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s+1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s+1) j u)) := by
  exact coefficientDivergenceL_apply_apply _ _ _ _

theorem fullCoefficientOperatorL_comp_subtype (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s+2)) :
    (fullCoefficientOperatorL hcalc s F).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL = strongDirichletOperator hcalc s F := by
  apply ContinuousLinearMap.ext
  intro u
  change fullCoefficientOperatorL hcalc s F (u : BallSobolev (s+2)) = _
  rw [fullCoefficientOperatorL_apply_apply,strongDirichletOperator_apply]
  rfl

theorem norm_fullCoefficientOperatorL_apply_le (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s+2)) :
    ‖fullCoefficientOperatorL hcalc s F‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ‖unitBallCoordinateDerivativeL hcalc s i‖ *
        ‖coefficientMultiplier hcalc (s+1) (F i j)‖ *
          ‖unitBallCoordinateDerivativeL hcalc (s+1) j‖ := by
  exact norm_coefficientDivergenceL_apply_le _ _ _

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contDiffOn_fullCoefficientOperator {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : H → SmoothCoefficientMatrix (s+2)) (q : Set H) (hF : ContDiffOn ℝ n F q) :
    ContDiffOn ℝ n (fun p => fullCoefficientOperatorL hcalc s (F p)) q :=
  (fullCoefficientOperatorL hcalc s).contDiff.comp_contDiffOn hF

def fullCommonSupportWeightedDriftBaseOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (p : R3 × ℝ) : BallSobolev (s+2) →L[ℝ] BallSobolev s :=
  ∑ i : Fin 3, (coefficientMultiplier hcalc s
    (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
      (contDiff_weightedDriftCoordinate w hw b hb i) K hK
      (weightedDriftCoordinate_support w b K hz i) p)).comp
    ((TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s).comp (unitBallCoordinateDerivativeL hcalc (s+1) i))

theorem fullCommonSupportWeightedDriftBaseOperator_comp_subtype
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0) (p : R3 × ℝ) :
    (fullCommonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p := by
  apply ContinuousLinearMap.ext
  intro u
  simp [fullCommonSupportWeightedDriftBaseOperator,commonSupportWeightedDriftBaseOperator,
    strongLowerOrderCoordinateDerivativeL,strongCoordinateDerivativeL]

theorem contDiff_fullCommonSupportWeightedDriftBaseOperator
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0) :
    ContDiff ℝ ∞ (fullCommonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz) := by
  apply ContDiff.sum
  intro i hi
  exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s
    (weightedDriftCoordinate w b i) (contDiff_weightedDriftCoordinate w hw b hb i)
    K hK (weightedDriftCoordinate_support w b K hz i)).clm_comp contDiff_const

def fullCommonSupportStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) : BallSobolev (s+2) →L[ℝ] BallSobolev s :=
  fullCoefficientOperatorL hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hza p) +
    (-L*p.2) • fullCommonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw p

theorem fullCommonSupportStrongDriftFamily_comp_subtype
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) :
    (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p := by
  simp only [fullCommonSupportStrongDriftFamily,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp,fullCoefficientOperatorL_comp_subtype,
    fullCommonSupportWeightedDriftBaseOperator_comp_subtype]
  rfl

theorem contDiff_fullCommonSupportStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0) (L : ℝ) :
    ContDiff ℝ ∞ (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L) := by
  have hA : ContDiff ℝ ∞ (fun p => fullCoefficientOperatorL hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hza p)) := by
    have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc s
        (commonSupportMatrixFamily (s+2) a ha K hK hza p)) := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s+1)
        (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun p z h => by rw [hza p z h]; rfl)
    change ContDiff ℝ ∞ (fun p => coefficientDivergenceL
      (unitBallCoordinateDerivativeL hcalc s) (unitBallCoordinateDerivativeL hcalc (s+1))
      (coefficientMatrixMultiplierL hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hza p)))
    exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
      (unitBallCoordinateDerivativeL hcalc (s+1))).contDiff.comp hm
  exact hA.add ((contDiff_const.mul contDiff_snd).smul
    (contDiff_fullCommonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hzw))

end OAI.AnisotropicCalderon.DirichletFamily
