import Calderon.ActualReferenceGaugeEnergyGraph
import Calderon.NativePrincipalWeakEnergyInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
private theorem topological_test_transfer
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (B E : V →L[ℝ] V →L[ℝ] ℝ) (T S : V →L[ℝ] V)
    (hST : ∀ v, S (T v) = v) (hTS : ∀ v, T (S v) = v)
    (hE : E.IsInvertible) (h : ∀ u v, B u v = E u (T v)) : B.IsInvertible := by
  let D : (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) := T.precomp ℝ
  let Di : (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) := S.precomp ℝ
  have hDi : D.comp Di = ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg ell (hST v)
  have hiD : Di.comp D = ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg ell (hTS v)
  have hD : D.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hDi hiD
  have hB : B = D.comp E := by
    apply ContinuousLinearMap.ext
    intro u
    exact ContinuousLinearMap.ext (h u)
  rw [hB]
  exact hD.comp hE

private theorem nativePrincipalForm_apply_energy
    (A : MatrixField)
    (hc : MemLp (fun z => TauCeti.PDE.energyIntegrand (A z) (0 : R3) (0 : ℝ)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL A 0 0 hc u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A 0 0 (u : BallH1) (v : BallH1) := by
  rw [nativeZeroCoefficientEnergyL_apply,TauCeti.PDE.energyFormH1L0_apply]
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

attribute [local irreducible] referenceWeakDirichletEnergyFamily referenceWeakEnergyFamily
  nativeZeroCoefficientEnergyL nativeCoefficientZeroProductL referenceGaugeScalarJets coefficientMultiplier

include hg hData in
set_option diagnostics true in
theorem referenceWeakDirichletEnergyFamily_isInvertible_on_actual_room
    (hcalc : FixedSobolevCalculus)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r))).IsInvertible := by
  trace "GAUGE-WEAK entered"
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let A : MatrixField := fun z => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H (p,z)
  have hA : Continuous A :=
    ((contDiff_referencePhysicalGaugeCompactPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData).comp
        (contDiff_const.prodMk contDiff_id)).continuous
  trace "GAUGE-WEAK coefficient continuous"
  let hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (A z) (0 : R3) (0 : ℝ)) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_continuousCoefficientEnergyIntegrand A hA
  trace "GAUGE-WEAK principal bounded coefficients"
  let EA := nativeZeroCoefficientEnergyL A 0 0 hcoeff
  trace "GAUGE-WEAK native energy map"
  obtain ⟨lam,Lam,hUEall⟩ :=
    exists_compact_uniformlyElliptic_referencePhysicalGaugeCompactPrincipalCoefficient
      g hg L y0 Φ B ε C ρ H a w hData {p} isCompact_singleton
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam :=
    (hUEall p (mem_singleton p)).mono_set ball_subset_closedBall
  have hEA : EA.IsInvertible :=
    nativeZeroPrincipalCoefficientEnergy_isInvertible A hA lam Lam hUE
  trace "GAUGE-WEAK principal inverse"
  let T := nativeCoefficientZeroProductL hcalc
    (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-L) p)
  let S := nativeCoefficientZeroProductL hcalc
    (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 L p)
  have hST : ∀ v, S (T v) = v := by
    intro v
    exact congrArg (fun A : BallH1Zero →L[ℝ] BallH1Zero => A v)
      (nativeCoefficientZeroProductL_comp_eq_id hcalc _ _
        (referenceGaugeScalarJets_reciprocal g hg L y0 Φ B ε C ρ H a w hData 2 L p))
  have hTSmap : T.comp S = ContinuousLinearMap.id ℝ BallH1Zero := by
    apply nativeCoefficientZeroProductL_comp_eq_id
    intro z hz
    rw [mul_comm]
    exact referenceGaugeScalarJets_reciprocal g hg L y0 Φ B ε C ρ H a w hData 2 L p z hz
  have hTS : ∀ v, T (S v) = v := by
    intro v
    exact congrArg (fun A : BallH1Zero →L[ℝ] BallH1Zero => A v) hTSmap
  have hEval (u v : BallH1Zero) :
      referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v = EA u (T v) := by
    exact (referenceWeakDirichletEnergyFamily_apply_reference
      g L y0 Φ B ε C ρ H a w hData hcalc p u v).trans
      ((referenceWeakEnergyFamily_eq_gauge_principal_test_product
        g hg L y0 Φ B ε C ρ H a w hData hcalc q hq y hy r hr (u : BallH1) v).trans
        ((nativePrincipalForm_apply_energy A hcoeff u (T v)).symm))
  trace "GAUGE-WEAK scalar covariance"
  exact topological_test_transfer
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    EA T S hST hTS hEA hEval



end OAI.AnisotropicCalderon.ConnectionError
