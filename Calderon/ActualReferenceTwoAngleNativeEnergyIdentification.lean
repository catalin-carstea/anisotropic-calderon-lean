import Calderon.ActualReferenceTwoAngleWeakOperator
import Calderon.NativeCoefficientWeakEnergy

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-native-two-angle-weak-lift-v007.md. SAME native energy and zero space. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

include hData in
lemma referenceTwoAngleNativeEnergy_memLp (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand
      (referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ha : Continuous (fun x : R3 => referenceTwoAnglePrincipalFamily a i j k l (t,x)) :=
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hb : Continuous (fun x : R3 => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) :=
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact memLp_nativeEnergyIntegrand_of_continuous _ _ 0 ha hb continuous_const

lemma referenceTwoAngleWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t =
      nativeCoefficientWeakEnergyL
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
        (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) := by
  have hE := referenceTwoAngleFullWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hN := nativeCoefficientWeakEnergyL_apply
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simpa only [referenceTwoAngleWeakEnergyFamily,ContinuousLinearMap.comp_apply,
    nativeH1ZeroDualRestrictionL_apply] using (hE u (v : BallH1)).trans (hN u v).symm

lemma referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeZeroEnergy
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t =
      nativeZeroCoefficientEnergyL
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
        (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) := by
  have hE := referenceTwoAngleFullWeakEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hN (u v : BallH1Zero) :=
    (nativeZeroCoefficientEnergyL_apply
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) u v).trans
        (TauCeti.PDE.energyFormH1L0_apply
          (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t) u v)
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simpa only [referenceTwoAngleWeakDirichletEnergyFamily,referenceTwoAngleWeakEnergyFamily,
    ContinuousLinearMap.comp_apply,nativeH1ZeroDualRestrictionL_apply,Submodule.subtypeL_apply]
    using (hE (u : BallH1) (v : BallH1)).trans (hN u v).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNativeEnergy_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakEnergyFamily_eq_nativeCoefficientWeakEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakDirichletEnergyFamily_eq_nativeZeroEnergy
