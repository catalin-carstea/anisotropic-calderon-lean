import Calderon.ActualReferenceStrongRoom
import Calderon.SupportedStrongOperatorEnergy

/-! Native supported operator/energy decomposition for actual StrongEnergy2.
Three helper roots including one whole alias were sealed before bodies. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def commonSupportSupportedStrongOperatorL
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a0 : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha0 : ContDiff ℝ ∞ a0)
    (w0 : (R3 × ℝ) × R3 → ℝ) (hw0 : ContDiff ℝ ∞ w0)
    (b0 : (R3 × ℝ) × R3 → R3) (hb0 : ContDiff ℝ ∞ b0)
    (K : Set R3) (hK : IsCompact K)
    (hza0 : ∀ p z, z ∉ K → a0 (p,z) = 0) (hzw0 : ∀ p z, z ∉ K → w0 (p,z) = 0)
    (L0 : ℝ) (p : R3 × ℝ) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  supportedStrongOperatorL hcalc s (commonSupportMatrixFamily (s+2) a0 ha0 K hK hza0 p)
    (weightedDriftSlice w0 b0 L0 p) (contDiff_weightedDriftSlice w0 hw0 b0 hb0 L0 p)
    K hK (weightedDriftSlice_support w0 b0 L0 p K hzw0)

theorem commonSupportSupportedStrongOperatorL_energy_of_elliptic
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a0 : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha0 : ContDiff ℝ ∞ a0)
    (w0 : (R3 × ℝ) × R3 → ℝ) (hw0 : ContDiff ℝ ∞ w0)
    (b0 : (R3 × ℝ) × R3 → R3) (hb0 : ContDiff ℝ ∞ b0)
    (K : Set R3) (hK : IsCompact K)
    (hza0 : ∀ p z, z ∉ K → a0 (p,z) = 0) (hzw0 : ∀ p z, z ∉ K → w0 (p,z) = 0)
    (L0 : ℝ) (p : R3 × ℝ)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a0 (p,z)) lam Lam)
    (U : StrongDirichletSpace s) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (commonSupportSupportedStrongOperatorL hcalc s a0 ha0 w0 hw0 b0 hb0
          K hK hza0 hzw0 L0 p U)) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a0 (p,z)) (weightedDriftSlice w0 b0 L0 p) 0
      (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
        (s+1) (U : BallSobolev (s+2))) (v : BallH1) := by
  let F : SmoothCoefficientMatrix (s+2) := commonSupportMatrixFamily (s+2) a0 ha0 K hK hza0 p
  let beta : R3 → R3 := weightedDriftSlice w0 b0 L0 p
  have hbeta : ContDiff ℝ ∞ beta := contDiff_weightedDriftSlice w0 hw0 b0 hb0 L0 p
  have hz : ∀ z, z ∉ K → beta z = 0 := weightedDriftSlice_support w0 b0 L0 p K hzw0
  have hField : coefficientMatrixField (s+2) F = fun z => a0 (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily (s+2) a0 ha0 K hK hza0 p
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s+2) F) lam Lam := by
    rw [hField]
    exact hUE
  let hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s+2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_coefficientMatrixEnergyIntegrand (s+2) F hUEF
  have hOp : commonSupportSupportedStrongOperatorL hcalc s a0 ha0 w0 hw0 b0 hb0
      K hK hza0 hzw0 L0 p = supportedStrongOperatorL hcalc s F beta hbeta K hK hz := rfl
  have hForcing := congrArg
    (fun T : StrongDirichletSpace s →L[ℝ] BallSobolev s =>
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
          (T U)) v) hOp
  have hNative := supportedStrongOperatorL_energy hcalc s F hcoeff beta hbeta K hK hz U v
  have hProjection := congrArg
    (fun u : BallH1 => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField (s+2) F) beta 0 u (v : BallH1))
    (strongDirichletProjectionL_apply s U)
  have hCoefficient := congrArg
    (fun A : R3 → Matrix (Fin 3) (Fin 3) ℝ => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) A beta 0
      (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
        (s+1) (U : BallSobolev (s+2))) (v : BallH1)) hField
  exact hForcing.trans (hNative.trans (hProjection.trans hCoefficient))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem referenceStrongDriftFamily_eq_supportedOperator
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (p : R3 × ℝ) :
    referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p =
      let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
      commonSupportSupportedStrongOperatorL hcalc s (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hFirst : referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p =
      commonSupportStrongDriftFamily hcalc s
        (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p :=
    congrArg (fun T : R3 × ℝ → StrongDirichletSpace s →L[ℝ] BallSobolev s => T p)
      (referenceStrongDriftFamily_eq_commonSupport g L y0 Φ B ε C ρ H a w hData hcalc s q)
  exact hFirst.trans (commonSupportStrongDriftFamily_eq_supportedStrongOperatorL hcalc s
    (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
