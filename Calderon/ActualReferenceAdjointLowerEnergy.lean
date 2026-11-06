import Calderon.ActualReferenceAdjointStrongOperator
import Calderon.NativeScalarMassPrincipalRegularity
import Calderon.NativeAdjointEnergyScalarAssembly

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceSupportedDriftZeroL (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    BallH1 →L[ℝ] BallSobolev 0 :=
  supportedDriftL hcalc 0
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p)

lemma referenceSupportedDriftZeroL_value_ae (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) :
    referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) (TauCeti.W1p.gradient u x)) :=
  supportedDriftL_zero_value_ae hcalc
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p) u

lemma referenceSupportedDriftZeroL_neg_value_ae (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) :
    -(referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (-(conformalReferenceWeightedFramedDrift g L Φ H w (p,x))) (TauCeti.W1p.gradient u x)) := by
  let D := referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u
  have hD := referenceSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData hcalc p u
  filter_upwards [Lp.coeFn_neg D,hD] with x hn hd
  have hnEval : (-(D : R3 → ℝ)) x = -(D x) := rfl
  exact hn.trans (hnEval.trans ((congrArg (fun t : ℝ => -t) hd).trans
    (inner_neg_left (conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) (TauCeti.W1p.gradient u x)).symm))

lemma referenceAdjointMass_value_ae (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) :
    nativeCoefficientMassL hcalc (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p) u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (-nativeSupportedDriftDivergence
        (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x) * TauCeti.W1p.value u x) := by
  simpa only [coefficientValue_referenceAdjointMassJetsFamily] using nativeCoefficientMassL_value_ae hcalc
    (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p) u

lemma referencePrincipalEnergyIntegrand_memLp (p : ℝ × (R3 × ℝ)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a (p,x)) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hp := memLp_coefficientMatrixEnergyIntegrand_of_smooth
    (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)
  rw [coefficientMatrixField_referenceJointPrincipalJetsFamily] at hp
  exact hp

lemma referenceOriginalLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) 0 0 u (v : BallH1) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u) v := by
  have hZero : (0 : BallSobolev 0) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
    have hf : (0 : R3 → ℝ) = (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
      funext x
      exact (zero_mul _).symm
    exact hf ▸ Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (referencePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData p) u v
    (referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u) 0
    (referenceSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData hcalc p u) hZero
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v = 0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact eq_add_of_eq_add_add_zero he hz

lemma referenceAdjointLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a (p,x))ᵀ) (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x) u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a (p,x))ᵀ) 0 0 u (v : BallH1) +
      (-TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u) v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (nativeCoefficientMassL hcalc (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p) u) v) := by
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  let D := referenceSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData hcalc p u
  let m := nativeCoefficientMassL hcalc (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p) u
  have hpT := memLp_nativePrincipalTransposeIntegrand (fun x => a (p,x))
    (referencePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData p)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => (a (p,x))ᵀ) (-beta)
    (fun x => -nativeSupportedDriftDivergence beta x) hpT u v (-D) m
    (referenceSupportedDriftZeroL_neg_value_ae g L y0 Φ B ε C ρ H a w hData hcalc p u)
    (referenceAdjointMass_value_ae g L y0 Φ B ε C ρ H a w hData hcalc p u)
  have hn : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (-D) v =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) D v := by
    rw [TauCeti.PDE.dirichletForcing_apply,TauCeti.PDE.dirichletForcing_apply,inner_neg_left]
  exact eq_add_add_of_eq_add_add_of_eq he hn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSupportedDriftZeroL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSupportedDriftZeroL_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSupportedDriftZeroL_neg_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMass_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePrincipalEnergyIntegrand_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOriginalLowerEnergy_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointLowerEnergy_decomposition
