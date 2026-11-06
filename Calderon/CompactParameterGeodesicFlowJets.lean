import Calderon.CompactParameterGeodesicFlow
import Calderon.NilpotentSecondVariation

/-! UNCOMPILED. Full mathematical expansion precedes this source in EXPANSION.md. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology NNReal
namespace OAI.AnisotropicCalderon.ConnectionError

section ProjectedParameterSlices
variable {P S G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace P] [CompleteSpace S]

theorem fderiv_projected_globalSolution_parameter_slice_apply
    (W : P × S → P × S) {L : ℝ≥0} (hW : LipschitzWith L W)
    (hWs : ContDiff ℝ ∞ W) (R : (P × S) →L[ℝ] G)
    (q : P) (z h : S) (t : ℝ) :
    fderiv ℝ (fun w => R (ODE.globalSolution W hW (q,w) t)) z h =
      R (flowBaseVariation W hW (0,h) ((q,z),t)) := by
  let F : (P × S) × ℝ → P × S := fun p => ODE.globalSolution W hW p.1 p.2
  have hF : ContDiff ℝ ∞ F := contDiff_infty_globalSolution W hW hWs
  have hi : HasFDerivAt (fun w : S => ((q,w),t))
      ((ContinuousLinearMap.inr ℝ P S).prod (0 : S →L[ℝ] ℝ)) z :=
    (hasFDerivAt_prodMk_right q z).prodMk (hasFDerivAt_const t z)
  have hp := R.hasFDerivAt.comp z
    ((hF.differentiable (by simp) ((q,z),t)).hasFDerivAt.comp z hi)
  change HasFDerivAt (fun w => R (ODE.globalSolution W hW (q,w) t)) _ z at hp
  rw [hp.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  rfl

theorem fderiv_fderiv_projected_globalSolution_parameter_slice_apply
    (W : P × S → P × S) {L : ℝ≥0} (hW : LipschitzWith L W)
    (hWs : ContDiff ℝ ∞ W) (R : (P × S) →L[ℝ] G)
    (q : P) (z h k : S) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (fun w => R (ODE.globalSolution W hW (q,w) t))) z k h =
      R (flowSecondBaseVariation W hW (0,h) (0,k) ((q,z),t)) := by
  have hF := contDiff_infty_globalSolution W hW hWs
  have hs : ContDiff ℝ ∞ (fun w : S => R (ODE.globalSolution W hW (q,w) t)) :=
    R.contDiff.comp (hF.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const))
  rw [← fderiv_fderiv_apply_const _ hs z h k]
  have he : (fun w => fderiv ℝ (fun u => R (ODE.globalSolution W hW (q,u) t)) w h) =
      (fun w => R (flowBaseVariation W hW (0,h) ((q,w),t))) := by
    funext w
    exact fderiv_projected_globalSolution_parameter_slice_apply W hW hWs R q w h t
  rw [he]
  let J := flowBaseVariation W hW (0,h)
  have hJ : ContDiff ℝ ∞ J := contDiff_flowBaseVariation W hW hWs (0,h)
  have hi : HasFDerivAt (fun w : S => ((q,w),t))
      ((ContinuousLinearMap.inr ℝ P S).prod (0 : S →L[ℝ] ℝ)) z :=
    (hasFDerivAt_prodMk_right q z).prodMk (hasFDerivAt_const t z)
  have hp := R.hasFDerivAt.comp z
    ((hJ.differentiable (by simp) ((q,z),t)).hasFDerivAt.comp z hi)
  change HasFDerivAt (fun w => R (flowBaseVariation W hW (0,h) ((q,w),t))) _ z at hp
  rw [hp.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  rfl
end ProjectedParameterSlices

section AugmentedSpray
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The complete stationary linearization, including parameter directions. -/
def parameterZeroVelocityLinearization :
    (P × (E × E)) →L[ℝ] P × (E × E) :=
  (0 : (P × (E × E)) →L[ℝ] P).prod
    (((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))).prod
      (0 : (P × (E × E)) →L[ℝ] E))

theorem parameterZeroVelocityLinearization_apply (d : P × (E × E)) :
    parameterZeroVelocityLinearization d = (0,(d.2.2,0)) := rfl

theorem parameterZeroVelocityLinearization_nilpotent (d : P × (E × E)) :
    parameterZeroVelocityLinearization (parameterZeroVelocityLinearization d) = 0 := rfl

def parameterPhasePositionProjection : (P × (E × E)) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))

theorem fderiv_parameterGeodesicPhaseField_apply
    (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (p d : P × (E × E)) :
    fderiv ℝ (parameterGeodesicPhaseField Q M) p d =
      (0,(d.2.2,-(
        fderiv ℝ (fun a : P × (E × E) =>
          parameterCoordinateConnectionField Q M (a.1,a.2.1)) p d p.2.2 p.2.2 +
        parameterCoordinateConnectionField Q M (p.1,p.2.1) d.2.2 p.2.2 +
        parameterCoordinateConnectionField Q M (p.1,p.2.1) p.2.2 d.2.2))) := by
  let Γ : P × (E × E) → E →L[ℝ] E →L[ℝ] E :=
    fun a => parameterCoordinateConnectionField Q M (a.1,a.2.1)
  have hΓs : ContDiff ℝ ∞ Γ :=
    (contDiff_parameterCoordinateConnectionField Q M hQ hM).comp
      (contDiff_fst.prodMk contDiff_snd.fst)
  have hΓ := (hΓs.differentiable (by simp) p).hasFDerivAt
  have hV : HasFDerivAt (fun a : P × (E × E) => a.2.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))) p :=
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))).hasFDerivAt
  have hR := (hΓ.clm_apply hV).clm_apply hV
  have hp := (hasFDerivAt_const (0 : P) p).prodMk (hV.prodMk hR.neg)
  change HasFDerivAt (parameterGeodesicPhaseField Q M) _ p at hp
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.prod_apply,zero_apply,
    neg_apply,add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_snd']
  congr 2
  change -(Γ p p.2.2 d.2.2 + (Γ p d.2.2 p.2.2 +
    fderiv ℝ Γ p d p.2.2 p.2.2)) = _
  dsimp only [Γ]
  abel

theorem fderiv_parameterGeodesicPhaseField_zero_velocity
    (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (q : P) (y : E) :
    fderiv ℝ (parameterGeodesicPhaseField Q M) (q,(y,0)) =
      parameterZeroVelocityLinearization := by
  apply ContinuousLinearMap.ext
  intro d
  rw [fderiv_parameterGeodesicPhaseField_apply Q M hQ hM]
  simp [parameterZeroVelocityLinearization_apply]

theorem fderiv_fderiv_parameterGeodesicPhaseField_zero_velocity
    (Q M : P × E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (q : P) (y : E) (d e : P × (E × E)) :
    fderiv ℝ (fderiv ℝ (parameterGeodesicPhaseField Q M)) (q,(y,0)) e d =
      (0,(0,-(parameterCoordinateConnectionField Q M (q,y) d.2.2 e.2.2 +
        parameterCoordinateConnectionField Q M (q,y) e.2.2 d.2.2))) := by
  let Γ : P × (E × E) → E →L[ℝ] E →L[ℝ] E :=
    fun a => parameterCoordinateConnectionField Q M (a.1,a.2.1)
  let a : P × (E × E) := (q,(y,0))
  have hΓs : ContDiff ℝ ∞ Γ :=
    (contDiff_parameterCoordinateConnectionField Q M hQ hM).comp
      (contDiff_fst.prodMk contDiff_snd.fst)
  have hΓ := (hΓs.differentiable (by simp) a).hasFDerivAt
  have hV : HasFDerivAt (fun z : P × (E × E) => z.2.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))) a :=
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ P (E × E))).hasFDerivAt
  have hDGs : ContDiff ℝ ∞ (fun z : P × (E × E) => fderiv ℝ Γ z d) :=
    (hΓs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hT1 := ((hDGs.differentiable (by simp) a).hasFDerivAt.clm_apply hV).clm_apply hV
  have hT10 : HasFDerivAt
      (fun z : P × (E × E) => fderiv ℝ Γ z d z.2.2 z.2.2)
      (0 : (P × (E × E)) →L[ℝ] E) a := by simpa [a] using hT1
  have hconst : HasFDerivAt (fun _ : P × (E × E) => d.2.2)
      (0 : (P × (E × E)) →L[ℝ] E) a := hasFDerivAt_const _ _
  have hT2 := (hΓ.clm_apply hconst).clm_apply hV
  have hT3 := (hΓ.clm_apply hV).clm_apply hconst
  have hp := (hasFDerivAt_const (0 : P) a).prodMk
    (hconst.prodMk ((hT10.add hT2).add hT3).neg)
  change HasFDerivAt (fun z : P × (E × E) =>
    (0,(d.2.2,-(fderiv ℝ Γ z d z.2.2 z.2.2 +
      Γ z d.2.2 z.2.2 + Γ z z.2.2 d.2.2)))) _ a at hp
  have he : (fun z => fderiv ℝ (parameterGeodesicPhaseField Q M) z d) =
      (fun z : P × (E × E) =>
        (0,(d.2.2,-(fderiv ℝ Γ z d z.2.2 z.2.2 +
          Γ z d.2.2 z.2.2 + Γ z z.2.2 d.2.2)))) := by
    funext z
    exact fderiv_parameterGeodesicPhaseField_apply Q M hQ hM z d
  rw [← fderiv_fderiv_apply_const _
    (contDiff_parameterGeodesicPhaseField Q M hQ hM) a d e,he,hp.fderiv]
  simp [Γ,a]

variable [CompleteSpace P]

theorem hasFDerivAt_parameter_stationary_zeroVelocity_endpoint
    (W : P × (E × E) → P × (E × E)) {L : ℝ≥0}
    (hW : LipschitzWith L W) (hWs : ContDiff ℝ ∞ W) (q : P) (y : E)
    (hz : W (q,(y,0)) = 0)
    (hD : fderiv ℝ W (q,(y,0)) = parameterZeroVelocityLinearization) :
    HasFDerivAt (fun z => (ODE.globalSolution W hW (q,z) 1).2.1)
      (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0) := by
  let R : (P × (E × E)) →L[ℝ] E := parameterPhasePositionProjection
  have hF := contDiff_infty_globalSolution W hW hWs
  have hs : ContDiff ℝ ∞ (fun z : E × E => (ODE.globalSolution W hW (q,z) 1).2.1) :=
    R.contDiff.comp (hF.comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const))
  have hp := (hs.differentiable (by simp) (y,0)).hasFDerivAt
  have heq : fderiv ℝ (fun z => (ODE.globalSolution W hW (q,z) 1).2.1) (y,0) =
      ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro h
    change fderiv ℝ (fun z => R (ODE.globalSolution W hW (q,z) 1)) (y,0) h = h.1 + h.2
    rw [fderiv_projected_globalSolution_parameter_slice_apply W hW hWs R]
    have hn (d : P × (E × E)) :
        fderiv ℝ W (q,(y,0)) (fderiv ℝ W (q,(y,0)) d) = 0 := by
      rw [hD]
      exact parameterZeroVelocityLinearization_nilpotent d
    have hj := globalSolution_baseDerivative_nilpotent W hW hWs (q,(y,0)) hz hn (0,h) 1
    simpa [R,flowBaseVariation,hD,parameterPhasePositionProjection,
      parameterZeroVelocityLinearization_apply] using congrArg R hj
  exact hp.congr_fderiv heq

theorem fderiv_fderiv_parameter_stationary_spray_endpoint
    (W : P × (E × E) → P × (E × E)) {L : ℝ≥0}
    (hW : LipschitzWith L W) (hWs : ContDiff ℝ ∞ W) (q : P) (y : E)
    (hz : W (q,(y,0)) = 0)
    (hD : fderiv ℝ W (q,(y,0)) = parameterZeroVelocityLinearization)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hH : ∀ d e : P × (E × E), fderiv ℝ (fderiv ℝ W) (q,(y,0)) e d =
      (0,(0,-(Γ d.2.2 e.2.2 + Γ e.2.2 d.2.2)))) (h k : E × E) :
    fderiv ℝ (fderiv ℝ (fun z => (ODE.globalSolution W hW (q,z) 1).2.1)) (y,0) k h =
      -(1/2 : ℝ) • (Γ h.2 k.2 + Γ k.2 h.2) := by
  let R : (P × (E × E)) →L[ℝ] E := parameterPhasePositionProjection
  let C : P × (E × E) := (0,(0,-(Γ h.2 k.2 + Γ k.2 h.2)))
  have hn (d : P × (E × E)) :
      fderiv ℝ W (q,(y,0)) (fderiv ℝ W (q,(y,0)) d) = 0 := by
    rw [hD]
    exact parameterZeroVelocityLinearization_nilpotent d
  have hf (t : ℝ) : fderiv ℝ (fderiv ℝ W) (q,(y,0))
      ((0,k) + t • fderiv ℝ W (q,(y,0)) (0,k))
      ((0,h) + t • fderiv ℝ W (q,(y,0)) (0,h)) = C := by
    rw [hH,hD]
    simp [C,parameterZeroVelocityLinearization_apply]
  have hw := globalSolution_secondBaseVariation_nilpotent
    W hW hWs (q,(y,0)) hz hn (0,h) (0,k) C hf 1
  change fderiv ℝ (fderiv ℝ (fun z => R (ODE.globalSolution W hW (q,z) 1))) (y,0) k h = _
  rw [fderiv_fderiv_projected_globalSolution_parameter_slice_apply W hW hWs R]
  simpa [R,C,hD,parameterZeroVelocityLinearization_apply,
    parameterPhasePositionProjection,smul_neg,neg_smul,add_comm] using congrArg R hw
end AugmentedSpray
end OAI.AnisotropicCalderon.ConnectionError
