import Calderon.ActualReferenceRotationAdjointStrongOperator
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
variable (iA jA : Fin 3)
include hData

def referenceRotationSupportedDriftZeroL (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (R3 × ℝ))) :
    BallH1 →L[ℝ] BallSobolev 0 :=
  supportedDriftL hcalc 0
    (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).2 t)

lemma referenceRotationSupportedDriftZeroL_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) :
    referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) (TauCeti.W1p.gradient u x)) :=
  supportedDriftL_zero_value_ae hcalc
    (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).2 t) u

lemma referenceRotationSupportedDriftZeroL_neg_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) :
    -(referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (-(coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))) (TauCeti.W1p.gradient u x)) := by
  let D := referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u
  have hD := referenceRotationSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u
  filter_upwards [Lp.coeFn_neg D,hD] with x hn hd
  have hnEval : (-(D : R3 → ℝ)) x = -(D x) := rfl
  exact hn.trans (hnEval.trans ((congrArg (fun t : ℝ => -t) hd).trans
    (inner_neg_left (coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) (TauCeti.W1p.gradient u x)).symm))

lemma referenceRotationAdjointMass_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) :
    nativeCoefficientMassL hcalc (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t) u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (-nativeSupportedDriftDivergence
        (fun y => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x) * TauCeti.W1p.value u x) := by
  simpa only [coefficientValue_referenceRotationAdjointMassJetsFamily] using nativeCoefficientMassL_value_ae hcalc
    (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t) u

lemma referenceRotationPrincipalEnergyIntegrand_memLp (t : ℝ × (ℝ × (R3 × ℝ))) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (coordinateRotationPrincipalFamily iA jA a (t,x)) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hp := memLp_coefficientMatrixEnergyIntegrand_of_smooth
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t)
  rw [coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t] at hp
  exact hp

lemma referenceRotationOriginalLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => coordinateRotationPrincipalFamily iA jA a (t,x)) (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0 u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => coordinateRotationPrincipalFamily iA jA a (t,x)) 0 0 u (v : BallH1) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u) v := by
  have hZero : (0 : BallSobolev 0) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
    have hf : (0 : R3 → ℝ) = (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
      funext x
      exact (zero_mul _).symm
    exact hf ▸ Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => coordinateRotationPrincipalFamily iA jA a (t,x))
    (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0
    (referenceRotationPrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData iA jA t) u v
    (referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u) 0
    (referenceRotationSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u) hZero
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v = 0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact eq_add_of_eq_add_add_zero he hz

lemma referenceRotationAdjointLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily iA jA a (t,x))ᵀ) (fun x => -coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x) u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily iA jA a (t,x))ᵀ) 0 0 u (v : BallH1) +
      (-TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u) v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (nativeCoefficientMassL hcalc (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t) u) v) := by
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  let D := referenceRotationSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u
  let m := nativeCoefficientMassL hcalc (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA t) u
  have hpT := memLp_nativePrincipalTransposeIntegrand (fun x => coordinateRotationPrincipalFamily iA jA a (t,x))
    (referenceRotationPrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData iA jA t)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => (coordinateRotationPrincipalFamily iA jA a (t,x))ᵀ) (-beta)
    (fun x => -nativeSupportedDriftDivergence beta x) hpT u v (-D) m
    (referenceRotationSupportedDriftZeroL_neg_value_ae g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u)
    (referenceRotationAdjointMass_value_ae g L y0 Φ B ε C ρ H a w hData iA jA hcalc t u)
  have hn : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (-D) v =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) D v := by
    rw [TauCeti.PDE.dirichletForcing_apply,TauCeti.PDE.dirichletForcing_apply,inner_neg_left]
  exact eq_add_add_of_eq_add_add_of_eq he hn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSupportedDriftZeroL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSupportedDriftZeroL_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationSupportedDriftZeroL_neg_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMass_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationPrincipalEnergyIntegrand_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOriginalLowerEnergy_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointLowerEnergy_decomposition
