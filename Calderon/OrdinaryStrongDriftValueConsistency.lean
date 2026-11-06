import Calderon.OrdinaryWeightedDriftEnergy
import Calderon.DirichletForcingInjectivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem ordinaryStrongDriftFamily_value_eq_of_firstOrder_eq
    (hcalc : FixedSobolevCalculus)
    (a0 : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha0 : ContDiff ℝ ∞ a0)
    (w0 : (R3 × ℝ) × R3 → ℝ) (hw0 : ContDiff ℝ ∞ w0)
    (b0 : (R3 × ℝ) × R3 → R3) (hb0 : ContDiff ℝ ∞ b0)
    (K : Set R3) (hK : IsCompact K)
    (hza0 : ∀ p z, z ∉ K → a0 (p,z) = 0) (hzw0 : ∀ p z, z ∉ K → w0 (p,z) = 0)
    (L0 : ℝ) (p : R3 × ℝ) (s t : ℕ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a0 (p,z)) lam Lam)
    (E : BallSobolev (s+2)) (F : BallSobolev (t+2))
    (hFirstOrder : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s+1) E =
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (t+1) F) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryStrongDriftFamily hcalc s a0 ha0 w0 hw0 b0 hb0 K hK hza0 hzw0 L0 p E) =
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) t
      (ordinaryStrongDriftFamily hcalc t a0 ha0 w0 hw0 b0 hb0 K hK hza0 hzw0 L0 p F) := by
  let Fs : SmoothCoefficientMatrix (s+2) := commonSupportMatrixFamily (s+2) a0 ha0 K hK hza0 p
  let Ft : SmoothCoefficientMatrix (t+2) := commonSupportMatrixFamily (t+2) a0 ha0 K hK hza0 p
  have hFieldS : coefficientMatrixField (s+2) Fs = fun z => a0 (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily (s+2) a0 ha0 K hK hza0 p
  have hFieldT : coefficientMatrixField (t+2) Ft = fun z => a0 (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily (t+2) a0 ha0 K hK hza0 p
  have hm : AEStronglyMeasurable (fun z => a0 (p,z))
      ((volume : Measure R3).restrict ballOpens) :=
    (ha0.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hcoeff0 := memLp_zeroDriftEnergyIntegrand hUE hm
  have hcoeffS : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField (s+2) Fs z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    rw [hFieldS]
    exact hcoeff0
  have hcoeffT : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField (t+2) Ft z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    rw [hFieldT]
    exact hcoeff0
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hs := ordinaryStrongDriftFamily_energy hcalc s a0 ha0 w0 hw0 b0 hb0
    K hK hza0 hzw0 L0 p hcoeffS E v
  have ht := ordinaryStrongDriftFamily_energy hcalc t a0 ha0 w0 hw0 b0 hb0
    K hK hza0 hzw0 L0 p hcoeffT F v
  rw [hFirstOrder] at hs
  exact hs.trans ht.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
