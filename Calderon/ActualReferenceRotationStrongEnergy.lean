import Calderon.NativeCoefficientStrongDriftEnergy
import Calderon.ActualReferenceRotationHarmonicLiftTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationOrdinaryStrongFamily_energy
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0
        (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t U)) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have h := referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j
  have he := principal_add_fullDriftMultiplierSum_energy hcalc
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)
    (fun l => referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l t)
    (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (h.1.comp (contDiff_const.prodMk contDiff_id))
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (h.2 t)
    (fun l x => coefficientValue_referenceRotationDriftJetsFamily
      g L y0 Φ B ε C ρ H a w hData 1 i j l t x) U v
  rw [coefficientMatrixField_referenceRotationPrincipalJetsFamily] at he
  exact he

lemma referenceRotationHarmonicLiftFamily_weak_energy
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible)
    (E : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      0 (TauCeti.Wkp.firstOrder 1
        (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E)) (v : BallH1) = 0 := by
  have he := referenceRotationOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc i j t
    (referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E) v
  rw [referenceRotationHarmonicLiftFamily_kernel g L y0 Φ B ε C ρ H a w hData hcalc i j t hi E] at he
  simpa only [TauCeti.PDE.dirichletForcing_apply,TauCeti.Wkp.value_zero,inner_zero_left] using he.symm

lemma referenceRotationHarmonicLiftFamily_boundary_difference
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible)
    (E : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1
      (E-referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let c : StrongDirichletSpace 0 :=
    (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).inverse
      (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E)
  have he : referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E =
      E-(c : BallSobolev 2) := by
    change guardedHarmonicLiftFamily _ _ _ t E = _
    rw [guardedHarmonicLiftFamily_eq _ _ _ t hi,harmonicLiftL_apply]
    rfl
  have hm : E-referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t E ∈
      strongDirichletSubmodule 0 := by
    rw [he,sub_sub_cancel]
    exact c.property
  exact (mem_strongDirichletSubmodule 0 _).mp hm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOrdinaryStrongFamily_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_weak_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_boundary_difference
