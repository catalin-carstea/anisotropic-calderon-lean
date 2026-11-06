import Calderon.ActualReferenceTwoAngleAdjointStrongOperator
import Calderon.NativeScalarMassPrincipalRegularity
import Calderon.NativeAdjointEnergyScalarAssembly

set_option autoImplicit false
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
variable (iA jA kA lA : Fin 3)
include hData

def referenceTwoAngleSupportedDriftZeroL (hcalc : FixedSobolevCalculus) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallH1 →L[ℝ] BallSobolev 0 :=
  supportedDriftL hcalc 0
    (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 t)

lemma referenceTwoAngleSupportedDriftZeroL_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u : BallH1) :
    referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)) (TauCeti.W1p.gradient u x)) :=
  supportedDriftL_zero_value_ae hcalc
    (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
    (SpatialJetFields.contDiff_spatial_slice _
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).2 t) u

lemma referenceTwoAngleSupportedDriftZeroL_neg_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u : BallH1) :
    -(referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (-(referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))) (TauCeti.W1p.gradient u x)) := by
  let D := referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u
  have hD := referenceTwoAngleSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u
  filter_upwards [Lp.coeFn_neg D,hD] with x hn hd
  have hnEval : (-(D : R3 → ℝ)) x = -(D x) := rfl
  exact hn.trans (hnEval.trans ((congrArg (fun t : ℝ => -t) hd).trans
    (inner_neg_left (referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)) (TauCeti.W1p.gradient u x)).symm))

lemma referenceTwoAngleAdjointMass_value_ae (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u : BallH1) :
    nativeCoefficientMassL hcalc (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t) u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (-nativeSupportedDriftDivergence
        (fun y => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,y)) x) * TauCeti.W1p.value u x) := by
  simpa only [coefficientValue_referenceTwoAngleAdjointMassJetsFamily] using nativeCoefficientMassL_value_ae hcalc
    (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t) u

lemma referenceTwoAnglePrincipalEnergyIntegrand_memLp (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x)) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hp := memLp_coefficientMatrixEnergyIntegrand_of_smooth
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t)
  rw [coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t] at hp
  exact hp

lemma referenceTwoAngleOriginalLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x)) (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)) 0 u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x)) 0 0 u (v : BallH1) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u) v := by
  have hZero : (0 : BallSobolev 0) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
    have hf : (0 : R3 → ℝ) = (fun x => (0 : ℝ)*TauCeti.W1p.value u x) := by
      funext x
      exact (zero_mul _).symm
    exact hf ▸ Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)) 0
    (referenceTwoAnglePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData iA jA kA lA t) u v
    (referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u) 0
    (referenceTwoAngleSupportedDriftZeroL_value_ae g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u) hZero
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v = 0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact eq_add_of_eq_add_add_zero he hz

lemma referenceTwoAngleAdjointLowerEnergy_decomposition (hcalc : FixedSobolevCalculus)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))ᵀ) (fun x => -referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,y)) x) u (v : BallH1) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))ᵀ) 0 0 u (v : BallH1) +
      (-TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u) v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (nativeCoefficientMassL hcalc (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t) u) v) := by
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)
  let D := referenceTwoAngleSupportedDriftZeroL g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u
  let m := nativeCoefficientMassL hcalc (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA t) u
  have hpT := memLp_nativePrincipalTransposeIntegrand (fun x => referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))
    (referenceTwoAnglePrincipalEnergyIntegrand_memLp g L y0 Φ B ε C ρ H a w hData iA jA kA lA t)
  have he := energyFormH1_eq_principal_add_nativeLowerForcing (fun x => (referenceTwoAnglePrincipalFamily a iA jA kA lA (t,x))ᵀ) (-beta)
    (fun x => -nativeSupportedDriftDivergence beta x) hpT u v (-D) m
    (referenceTwoAngleSupportedDriftZeroL_neg_value_ae g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u)
    (referenceTwoAngleAdjointMass_value_ae g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc t u)
  have hn : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (-D) v =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) D v := by
    rw [TauCeti.PDE.dirichletForcing_apply,TauCeti.PDE.dirichletForcing_apply,inner_neg_left]
  exact eq_add_add_of_eq_add_add_of_eq he hn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSupportedDriftZeroL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSupportedDriftZeroL_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSupportedDriftZeroL_neg_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMass_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePrincipalEnergyIntegrand_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOriginalLowerEnergy_decomposition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointLowerEnergy_decomposition
