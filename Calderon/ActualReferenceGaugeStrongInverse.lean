import Calderon.ActualReferenceGaugeEnergyGraph
import Calderon.NativeScalarDirichletForcingProduct
import Calderon.NativePrincipalWeakEnergyInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] coefficientMultiplier nativeCoefficientZeroProductL
theorem dirichletForcing_coefficientMultiplier_zeroProduct
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 1) (G : SmoothCoefficientJets 2)
    (hFG : ∀ x ∈ (ballOpens : Set R3), coefficientValue 1 F x = coefficientValue 2 G x)
    (f : BallSobolev 0) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 (coefficientMultiplier hcalc 0 F f)) v =
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 f) (nativeCoefficientZeroProductL hcalc G v) := by
  have hG : TauCeti.W1p.value (nativeCoefficientZeroProductL hcalc G v : BallH1)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => coefficientValue 1 F x * TauCeti.W1p.value (v : BallH1) x := by
    rw [nativeCoefficientZeroProductL_coe]
    filter_upwards [nativeCoefficientH1ProductL_value_ae hcalc G (v : BallH1),
      ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hxball
    rw [hx,hFG x hxball]
  exact dirichletForcing_eq_of_scalar_product_ae
    (TauCeti.Wkp.value 0 f) (TauCeti.Wkp.value 0 (coefficientMultiplier hcalc 0 F f))
    v (nativeCoefficientZeroProductL hcalc G v) (coefficientValue 1 F)
    (coefficientMultiplier_value_ae hcalc 0 F f) hG


private theorem isInvertible_of_apply_eq_comp
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B P : X →L[ℝ] Y) (M : Y →L[ℝ] Y)
    (hM : M.IsInvertible) (hP : P.IsInvertible)
    (h : ∀ u, B u = M (P u)) : B.IsInvertible := by
  have hB : B = M.comp P := ContinuousLinearMap.ext h
  rw [hB]
  exact hM.comp hP

private theorem isInvertible_of_test_precomposition
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B E : V →L[ℝ] StrongDual ℝ V) (T S : V →L[ℝ] V)
    (hST : ∀ v, S (T v) = v) (hTS : ∀ v, T (S v) = v)
    (hE : E.IsInvertible) (h : ∀ u v, B u v = E u (T v)) : B.IsInvertible := by
  have hB : B = ((ContinuousLinearMap.compL ℝ V V ℝ).flip T).comp E := by
    apply ContinuousLinearMap.ext
    intro u
    exact ContinuousLinearMap.ext (h u)
  rw [hB]
  exact (dualPrecomposition_isInvertible_of_inverse T S hST hTS).comp hE

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

attribute [local irreducible] referenceStrongDriftFamily strongDirichletOperator
  referencePhysicalGaugeCoefficientJets referenceGaugeScalarJets coefficientMultiplier
  ordinaryPrincipalL referenceWeakEnergyFamily nativeCoefficientZeroProductL

include hg hData in
set_option diagnostics true in
theorem referenceStrongDriftFamily_zero_apply_eq_gauge_principal
    (hcalc : FixedSobolevCalculus)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (U : StrongDirichletSpace 0) :
    referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r) U =
      coefficientMultiplier hcalc 0
        (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 1 (-L) (q,(y,r)))
        (strongDirichletOperator hcalc 0
          (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) U) := by
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p
  let M := referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 1 (-L) p
  let Q := referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-L) p
  let T := nativeCoefficientZeroProductL hcalc Q
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic
    g L y0 Φ B ε C ρ H a w hData p
  trace "GAUGE-STRONG apply identity entered"
  apply TauCeti.Wkp.ext 0
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  trace "GAUGE-STRONG forcing reduction"
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2)
  have hOld := referenceStrongDriftFamily_energy_of_elliptic
    g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r) lam Lam hUE U v
  trace "GAUGE-STRONG old energy"
  have hWeakOld := referenceWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc p u v
  trace "GAUGE-STRONG weak evaluation"
  have hGauge := referenceWeakEnergyFamily_eq_gauge_principal_test_product
    g hg L y0 Φ B ε C ρ H a w hData hcalc q hq y hy r hr u v
  trace "GAUGE-STRONG gauge graph"
  have hPrincipal := ordinaryPrincipalL_energy hcalc 0 F (U : BallSobolev 2) (T v)
  trace "GAUGE-STRONG principal energy"
  have hRestr : ordinaryPrincipalL hcalc 0 F (U : BallSobolev 2) =
      strongDirichletOperator hcalc 0 F U :=
    congrArg (fun A : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => A U)
      (ordinaryPrincipalL_restriction hcalc 0 F)
  trace "GAUGE-STRONG restriction graph"
  have hRestrForcing := congrArg (fun f : BallSobolev 0 =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 f) (T v)) hRestr
  have hPrincipalRestricted := hRestrForcing.symm.trans hPrincipal
  trace "GAUGE-STRONG forcing restriction projection"
  have hCoeff : coefficientMatrixField 2 F =
      fun z => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z) :=
    coefficientMatrixField_referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 p
  trace "GAUGE-STRONG coefficient graph"
  have hCoeffEnergy := congrArg (fun A : MatrixField =>
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A 0 0 u (T v : BallH1)) hCoeff
  have hPrincipalGauge := hPrincipalRestricted.trans hCoeffEnergy
  trace "GAUGE-STRONG principal gauge energy"
  have hComm := dirichletForcing_coefficientMultiplier_zeroProduct hcalc M Q
    (fun z hz => by
      rw [coefficientValue_referenceGaugeScalarJets_on_unitBall
        g hg L y0 Φ B ε C ρ H a w hData 1 (-L) p z hz,
        coefficientValue_referenceGaugeScalarJets_on_unitBall
          g hg L y0 Φ B ε C ρ H a w hData 2 (-L) p z hz])
    (strongDirichletOperator hcalc 0 F U) v
  trace "GAUGE-STRONG forcing graph"
  exact hOld.trans (hWeakOld.symm.trans (hGauge.trans (hPrincipalGauge.symm.trans hComm.symm)))

include hg hData in
theorem referenceStrongDriftFamily_zero_isInvertible_on_actual_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)).IsInvertible := by
  apply isInvertible_of_apply_eq_comp
    (B := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r))
    (P := strongDirichletOperator hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))))
    (M := coefficientMultiplier hcalc 0
      (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 1 (-L) (q,(y,r))))
    (referenceGaugeScalarMultiplier_isInvertible
      g hg L y0 Φ B ε C ρ H a w hData hcalc 0 (-L) (q,(y,r)))
    (referencePhysicalGaugePrincipal_isInvertible
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 (q,(y,r)))
  intro U
  exact referenceStrongDriftFamily_zero_apply_eq_gauge_principal
    g hg L y0 Φ B ε C ρ H a w hData hcalc q hq y hy r hr U



end OAI.AnisotropicCalderon.ConnectionError
