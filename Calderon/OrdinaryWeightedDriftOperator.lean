import Calderon.WeightedDriftSlice
import Calderon.SupportedDriftInverse
import Calderon.CoordinateFluxEnergy
import Calderon.SupportedDriftConsistency

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

def ordinaryCoefficientOperatorL (hcalc : FixedSobolevCalculus) (s : ℕ) :
    SmoothCoefficientMatrix (s + 2) →L[ℝ]
      BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
    (unitBallCoordinateDerivativeL hcalc (s + 1))).comp
      (coefficientMatrixMultiplierL hcalc s)

def ordinaryPrincipalL (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  ordinaryCoefficientOperatorL hcalc s F

theorem ordinaryPrincipalL_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (E : BallSobolev (s + 2)) :
    ordinaryPrincipalL hcalc s F E = -∑ i : Fin 3, ∑ j : Fin 3,
      unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s + 1) j E)) :=
  coefficientDivergenceL_apply_apply _ _ _ E

theorem ordinaryPrincipalL_restriction (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    (ordinaryPrincipalL hcalc s F).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        strongDirichletOperator hcalc s F := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [ordinaryPrincipalL, ordinaryCoefficientOperatorL,
    strongDirichletOperator, strongCoefficientOperatorL, unitBallDivergenceL,
    coefficientDivergenceL, operatorMatrixEntryL,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.proj_apply]

theorem ordinaryCoefficientFlux_value_ae (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (i j : Fin 3)
    (E : BallSobolev (s + 2)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
        (unitBallCoordinateDerivativeL hcalc (s + 1) j E))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => coefficientValue (s + 2) (F i j) z *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) j :=
  (coefficientMultiplier_value_ae hcalc (s + 1) (F i j)
    (unitBallCoordinateDerivativeL hcalc (s + 1) j E)).trans
      (EventuallyEq.mul (EventuallyEq.refl _ _)
        (unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) j E))

theorem ordinaryPrincipalL_energy (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (E : BallSobolev (s + 2))
    (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) 0 0
        (TauCeti.Wkp.firstOrder (s + 1) E) (v : BallH1) := by
  have hforcing : TauCeti.PDE.dirichletForcing
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (ordinaryPrincipalL hcalc s F E)) v =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ⟪TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
          (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
            (unitBallCoordinateDerivativeL hcalc (s + 1) j E)),
          unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
    rw [TauCeti.PDE.dirichletForcing_apply, ordinaryPrincipalL_apply]
    change ⟪TauCeti.Wkp.valueL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s (-∑ i : Fin 3, ∑ j : Fin 3,
        unitBallCoordinateDerivativeL hcalc s i
          (coefficientMultiplier hcalc (s + 1) (F i j)
            (unitBallCoordinateDerivativeL hcalc (s + 1) j E))),
      TauCeti.W1p.value (v : BallH1)⟫_ℝ = _
    simp only [map_neg, map_sum, inner_neg_left, sum_inner, TauCeti.Wkp.valueL_apply]
    simp_rw [unitBallCoordinateDerivative_inner_integration hcalc s]
    simp only [Finset.sum_neg_distrib, neg_neg]
  exact hforcing.trans (energyFormH1_eq_sum_coordinateFlux_inner
    (coefficientMatrixField (s + 2) F) (TauCeti.Wkp.firstOrder (s + 1) E)
    (v : BallH1)
    (fun i j => TauCeti.Wkp.value (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) (s + 1)
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (unitBallCoordinateDerivativeL hcalc (s + 1) j E)))
    (fun i j => ordinaryCoefficientFlux_value_ae hcalc s F i j E)).symm

def ordinaryLowerOrderCoordinateDerivativeL (hcalc : FixedSobolevCalculus)
    (s : ℕ) (i : Fin 3) : BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) s).comp (unitBallCoordinateDerivativeL hcalc (s + 1) i)

theorem ordinaryLowerOrderCoordinateDerivative_value_ae (hcalc : FixedSobolevCalculus)
    (s : ℕ) (i : Fin 3) (E : BallSobolev (s + 2)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryLowerOrderCoordinateDerivativeL hcalc s i E)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) i := by
  change TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
    (TauCeti.Wkp.lowerOrder s (unitBallCoordinateDerivativeL hcalc (s + 1) i E)) =ᵐ[_] _
  rw [← TauCeti.Wkp.value_succ]
  exact unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) i E

section Family
variable (hcalc : FixedSobolevCalculus) (s : ℕ)
  (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
  (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
  (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
  (K : Set R3) (hK : IsCompact K)
  (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0)
  (L : ℝ)

def ordinaryWeightedDriftBaseL (p : R3 × ℝ) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  ∑ i : Fin 3, (coefficientMultiplier hcalc s
    (commonSupportCoefficientFamily (s + 1) (weightedDriftCoordinate w b i)
      (contDiff_weightedDriftCoordinate w hw b hb i) K hK
      (weightedDriftCoordinate_support w b K hzw i) p)).comp
        (ordinaryLowerOrderCoordinateDerivativeL hcalc s i)

def ordinaryWeightedDriftL (p : R3 × ℝ) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  (-L * p.2) • ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw p

def ordinaryStrongDriftFamily (p : R3 × ℝ) :
    BallSobolev (s + 2) →L[ℝ] BallSobolev s :=
  ordinaryPrincipalL hcalc s (commonSupportMatrixFamily (s + 2) a ha K hK hza p) +
    ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p

theorem ordinaryWeightedDriftL_restriction (p : R3 × ℝ) :
    (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hzw L p := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [ordinaryWeightedDriftL, ordinaryWeightedDriftBaseL,
    commonSupportWeightedDriftOperator, commonSupportWeightedDriftBaseOperator,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply]
  rfl

theorem ordinaryStrongDriftFamily_restriction (p : R3 × ℝ) :
    (ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL =
        commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p := by
  apply ContinuousLinearMap.ext
  intro U
  change ordinaryPrincipalL hcalc s
      (commonSupportMatrixFamily (s + 2) a ha K hK hza p) (U : BallSobolev (s + 2)) +
    ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p (U : BallSobolev (s + 2)) =
      commonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p U
  rw [commonSupportStrongDriftFamily_eq, ContinuousLinearMap.add_apply]
  have hP : ordinaryPrincipalL hcalc s
      (commonSupportMatrixFamily (s + 2) a ha K hK hza p) (U : BallSobolev (s + 2)) =
      strongDirichletOperator hcalc s
        (commonSupportMatrixFamily (s + 2) a ha K hK hza p) U :=
    congrArg (fun T : StrongDirichletSpace s →L[ℝ] BallSobolev s => T U)
      (ordinaryPrincipalL_restriction hcalc s
        (commonSupportMatrixFamily (s + 2) a ha K hK hza p))
  have hD : ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p
      (U : BallSobolev (s + 2)) =
      commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hzw L p U :=
    congrArg (fun T : StrongDirichletSpace s →L[ℝ] BallSobolev s => T U)
      (ordinaryWeightedDriftL_restriction hcalc s w hw b hb K hK hzw L p)
  exact congrArg₂ (fun x y : BallSobolev s => x + y) hP hD

theorem ordinaryWeightedDriftL_value_eq (p : R3 × ℝ) (E : BallSobolev (s + 2)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E) =
        supportedDriftL hcalc 0 (weightedDriftSlice w b L p)
          (contDiff_weightedDriftSlice w hw b hb L p) K hK
          (weightedDriftSlice_support w b L p K hzw)
          (TauCeti.Wkp.firstOrder (s + 1) E) := by
  let T (i : Fin 3) : BallSobolev s := coefficientMultiplier hcalc s
    (commonSupportCoefficientFamily (s + 1) (weightedDriftCoordinate w b i)
      (contDiff_weightedDriftCoordinate w hw b hb i) K hK
      (weightedDriftCoordinate_support w b K hzw i) p)
        (ordinaryLowerOrderCoordinateDerivativeL hcalc s i E)
  have hi (i : Fin 3) : TauCeti.Wkp.value (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s (T i) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => w (p,z) * b (p,z) i *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) i := by
    have hm := coefficientMultiplier_value_ae hcalc s
      (commonSupportCoefficientFamily (s + 1) (weightedDriftCoordinate w b i)
        (contDiff_weightedDriftCoordinate w hw b hb i) K hK
        (weightedDriftCoordinate_support w b K hzw i) p)
      (ordinaryLowerOrderCoordinateDerivativeL hcalc s i E)
    have hd := ordinaryLowerOrderCoordinateDerivative_value_ae hcalc s i E
    apply (hm.trans (EventuallyEq.mul (EventuallyEq.refl _ _) hd)).trans
    apply Eventually.of_forall
    intro z
    exact congrArg (fun c : ℝ => c *
      (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) i)
      (coefficientValue_commonSupportCoefficientFamily (s + 1)
        (weightedDriftCoordinate w b i) (contDiff_weightedDriftCoordinate w hw b hb i)
        K hK (weightedDriftCoordinate_support w b K hzw i) p z)
  have hv : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryWeightedDriftL hcalc s w hw b hb K hK hzw L p E)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => (-L * p.2) * (∑ i : Fin 3, w (p,z) * b (p,z) i *
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder (s + 1) E) z) i) := by
    change (TauCeti.Wkp.valueL s) ((-L * p.2) • (∑ i : Fin 3, T i)) =ᵐ[_] _
    rw [map_smul, map_sum]
    exact (Lp.coeFn_smul _ _).trans
      (((Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ => hi i))).const_smul _)
  apply Lp.ext
  have hr := supportedDriftL_value_ae hcalc 0 (weightedDriftSlice w b L p)
    (contDiff_weightedDriftSlice w hw b hb L p) K hK
    (weightedDriftSlice_support w b L p K hzw) (TauCeti.Wkp.firstOrder (s + 1) E)
  simp only [TauCeti.Wkp.value_zero, TauCeti.Wkp.firstOrder_zero] at hr
  filter_upwards [hv, hr] with z hl hrz
  rw [hl, hrz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [weightedDriftSlice, weightedLinearRadialDrift, PiLp.smul_apply, smul_eq_mul]
  ring

theorem contDiff_ordinaryStrongDriftFamily :
    ContDiff ℝ ∞ (ordinaryStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s + 2) a ha K hK hza p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s + 1)
      (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun p z h => by rw [hza p z h]; rfl)
  have hP : ContDiff ℝ ∞ (fun p => ordinaryPrincipalL hcalc s
      (commonSupportMatrixFamily (s + 2) a ha K hK hza p)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
      (unitBallCoordinateDerivativeL hcalc (s + 1))).contDiff.comp hm
  have hD : ContDiff ℝ ∞ (ordinaryWeightedDriftBaseL hcalc s w hw b hb K hK hzw) := by
    apply ContDiff.sum
    intro i hi
    exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s
      (weightedDriftCoordinate w b i) (contDiff_weightedDriftCoordinate w hw b hb i)
      K hK (weightedDriftCoordinate_support w b K hzw i)).clm_comp contDiff_const
  exact hP.add ((contDiff_const.mul contDiff_snd).smul hD)

end Family
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
