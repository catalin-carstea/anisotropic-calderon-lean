import Calderon.ActualUniformExistingProductLocalJetEstimate
import Calderon.ActualMixedKernelConstruction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

def convexProductPhase (p:R3×R3) (z:R3×R3):ℝ :=
  (‖z.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2+
    ‖z.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2)/2-1

theorem convexProductPhase_contDiff_and_zero (p:R3×R3):
    ContDiff ℝ ∞ (convexProductPhase p) ∧ convexProductPhase p p=0 := by
  constructor
  · have h1:ContDiff ℝ ∞ (fun z:R3×R3 => z.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ)) :=
      (contDiff_fst.sub contDiff_const).add contDiff_const
    have h2:ContDiff ℝ ∞ (fun z:R3×R3 => z.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ)) :=
      (contDiff_snd.sub contDiff_const).add contDiff_const
    exact (((h1.norm_sq (𝕜:=ℝ)).add (h2.norm_sq (𝕜:=ℝ))).div_const 2).sub contDiff_const
  · simp [convexProductPhase]

theorem convexProductPhase_hasFDerivAt (p z:R3×R3):
    HasFDerivAt (convexProductPhase p)
      ((innerSL ℝ (z.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ))).comp (ContinuousLinearMap.fst ℝ R3 R3)+
       (innerSL ℝ (z.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ))).comp (ContinuousLinearMap.snd ℝ R3 R3)) z := by
  have hd1:HasFDerivAt (Prod.fst:R3×R3→R3) (ContinuousLinearMap.fst ℝ R3 R3) z := hasFDerivAt_fst
  have hd2:HasFDerivAt (Prod.snd:R3×R3→R3) (ContinuousLinearMap.snd ℝ R3 R3) z := hasFDerivAt_snd
  have h1 := (hd1.sub_const p.1).add_const (EuclideanSpace.single (0:Fin 3) (1:ℝ))
  have h2 := (hd2.sub_const p.2).add_const (EuclideanSpace.single (0:Fin 3) (1:ℝ))
  have h:=((h1.norm_sq.add h2.norm_sq).const_mul (1/2:ℝ)).sub_const 1
  change HasFDerivAt (fun w:R3×R3 => (1/2:ℝ)*(‖w.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2+
    ‖w.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2)-1) _ z at h
  have heq:convexProductPhase p=(fun w:R3×R3 => (1/2:ℝ)*(‖w.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2+
    ‖w.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ)‖^2)-1) := by funext w;unfold convexProductPhase;ring
  rw [heq]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  simp

theorem convexProductPhase_second_jet (p z:R3×R3):
    ∃ D:R3×R3→L[ℝ] R3×R3→L[ℝ] ℝ,
      HasFDerivAt (fderiv ℝ (convexProductPhase p)) D z ∧
      ∀ W V:R3×R3,D W V=⟪W.1,V.1⟫_ℝ+⟪W.2,V.2⟫_ℝ := by
  have hd1:HasFDerivAt (Prod.fst:R3×R3→R3) (ContinuousLinearMap.fst ℝ R3 R3) z := hasFDerivAt_fst
  have hd2:HasFDerivAt (Prod.snd:R3×R3→R3) (ContinuousLinearMap.snd ℝ R3 R3) z := hasFDerivAt_snd
  have h1 := (hd1.sub_const p.1).add_const (EuclideanSpace.single (0:Fin 3) (1:ℝ))
  have h2 := (hd2.sub_const p.2).add_const (EuclideanSpace.single (0:Fin 3) (1:ℝ))
  have hI1:=((innerSL ℝ : R3→L[ℝ] R3→L[ℝ] ℝ).hasFDerivAt.comp z h1).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.fst ℝ R3 R3) z)
  have hI2:=((innerSL ℝ : R3→L[ℝ] R3→L[ℝ] ℝ).hasFDerivAt.comp z h2).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.snd ℝ R3 R3) z)
  have h:=hI1.add hI2
  have heq:∀ᶠ w in 𝓝 z,fderiv ℝ (convexProductPhase p) w=
      (innerSL ℝ (w.1-p.1+EuclideanSpace.single (0:Fin 3) (1:ℝ))).comp (ContinuousLinearMap.fst ℝ R3 R3)+
      (innerSL ℝ (w.2-p.2+EuclideanSpace.single (0:Fin 3) (1:ℝ))).comp (ContinuousLinearMap.snd ℝ R3 R3) :=
    Filter.Eventually.of_forall fun w => (convexProductPhase_hasFDerivAt p w).fderiv
  refine ⟨_,h.congr_of_eventuallyEq heq,?_⟩
  intro W V
  simp <;> rfl

theorem convexProductPhase_flat_strict (p:R3×R3):
    ProductHessianStrictAt (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ))
      (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) p.1 p.2 (convexProductPhase p) := by
  let e:R3 := EuclideanSpace.single (0:Fin 3) (1:ℝ)
  have he:⟪e,e⟫_ℝ=1 := by simp [e]
  have hgrad:∀ W:R3×R3,fderiv ℝ (convexProductPhase p) p W=⟪e,W.1⟫_ℝ+⟪e,W.2⟫_ℝ := by
    intro W
    rw [(convexProductPhase_hasFDerivAt p p).fderiv]
    simp [e]
  obtain ⟨D,hD,hDe⟩ := convexProductPhase_second_jet p p
  unfold ProductHessianStrictAt
  intro ell ell1 ell2 M1 M2 Gamma1 Gamma2 b1 b2 a1 a2 H
  have hM1:∀ X:R3,M1 X=X := fun X => euclidean_matrixOperator_one X
  have hM2:∀ X:R3,M2 X=X := fun X => euclidean_matrixOperator_one X
  have hG1:∀ X Z:R3,Gamma1 X Z=0 := fun X Z => euclidean_connection_zero _ _ _ _
  have hG2:∀ X Z:R3,Gamma2 X Z=0 := fun X Z => euclidean_connection_zero _ _ _ _
  have hell1:∀ X:R3,ell1 X=⟪e,X⟫_ℝ := by intro X;change fderiv ℝ (convexProductPhase p) p (X,0)=_;rw [hgrad];simp
  have hell2:∀ X:R3,ell2 X=⟪e,X⟫_ℝ := by intro X;change fderiv ℝ (convexProductPhase p) p (0,X)=_;rw [hgrad];simp
  have hb1:b1=e := by
    change matrixOperatorMap ((1:Matrix (Fin 3) (Fin 3) ℝ)⁻¹) (WithLp.toLp 2 (fun i:Fin 3 => ell1 (coordinateVector i)))=e
    rw [(euclidean_metricOperator_one p.1 _).2]
    exact euclidean_coordinate_riesz ell1 e hell1
  have hb2:b2=e := by
    change matrixOperatorMap ((1:Matrix (Fin 3) (Fin 3) ℝ)⁻¹) (WithLp.toLp 2 (fun i:Fin 3 => ell2 (coordinateVector i)))=e
    rw [(euclidean_metricOperator_one p.2 _).2]
    exact euclidean_coordinate_riesz ell2 e hell2
  have ha1:a1=e := by change (⟪M1 b1,b1⟫_ℝ)⁻¹ • b1=e;rw [hM1,hb1,he];simp
  have ha2:a2=e := by change (⟪M2 b2,b2⟫_ℝ)⁻¹ • b2=e;rw [hM2,hb2,he];simp
  have hH:∀ W V:R3×R3,H W V=⟪W.1,V.1⟫_ℝ+⟪W.2,V.2⟫_ℝ := by
    intro W V
    change fderiv ℝ (fderiv ℝ (convexProductPhase p)) p W V-ell (Gamma1 W.1 V.1,Gamma2 W.2 V.2)=_
    rw [hG1,hG2,hD.fderiv,Prod.mk_zero_zero,map_zero,sub_zero,hDe]
  refine ⟨?_,?_,?_⟩
  · intro h0
    have hh:=hell1 e
    rw [h0,ContinuousLinearMap.zero_apply,he] at hh
    norm_num at hh
  · intro h0
    have hh:=hell2 e
    rw [h0,ContinuousLinearMap.zero_apply,he] at hh
    norm_num at hh
  · intro v1 v2 _ _ _ _
    rw [hH,hH,ha1,ha2]
    simp only [Prod.fst,Prod.snd,inner_neg_neg,he]
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    positivity

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
